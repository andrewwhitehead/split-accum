use bls12_381_plus::group::Wnaf;
use bls12_381_plus::{group::Curve, G1Projective, Scalar};

use crate::accum::{
    Accumulator, AccumulatorPrivate, AccumulatorPrivateKey, MembershipWitness, RegistryPublic,
};
use crate::common::{batch_invert, compute_member_value, AccumulatorError, IndexType};
use crate::split_accum::{PartitionSignature, SignedMembershipWitness, SplitRegistryPublic};

impl MembershipWitness {
    /// Begin the update process for a membership witness.
    pub fn begin_update(&self) -> UpdateMembershipWitness {
        UpdateMembershipWitness::new(self, 0)
    }
}

impl SignedMembershipWitness {
    /// Begin the update process for a membership witness.
    pub fn begin_update(&self) -> UpdateMembershipWitness {
        UpdateMembershipWitness::new(&self.membership, self.partition.index)
    }
}

/// A batch removal operation an accumulator.
#[derive(Debug, Clone)]
pub struct BatchRemoval {
    /// The set of terms and encoded member values.
    pub(crate) values: Vec<(G1Projective, IndexType)>,
    /// The partition index of the batch operation.
    pub(crate) partition: IndexType,
}

impl BatchRemoval {
    /// Access the partition index.
    pub fn partition(&self) -> IndexType {
        self.partition
    }

    /// Remove multiple values from an accumulator, producing a batch removal operation.
    pub(crate) fn remove_members(
        accum: &AccumulatorPrivate,
        sk: &AccumulatorPrivateKey,
        members: &[(IndexType, Scalar)],
        partition: IndexType,
    ) -> Result<(BatchRemoval, AccumulatorPrivate), AccumulatorError> {
        let mut denoms = Vec::with_capacity(members.len());
        for (_, member) in members.iter().copied() {
            // each denominator starts as `(a + m_i)`
            denoms.push(sk.member_key + member);
        }
        for idx in 0..denoms.len() {
            for jdx in idx + 1..denoms.len() {
                let term = &members[jdx].1 - &members[idx].1;
                // multiply each index `i` by `(m_j - m_i)`
                denoms[idx] *= term;
                // multiply each index `j` by `(m_i - m_j)`
                denoms[jdx] *= -term;
            }
        }
        // Invert denominators. This should not fail as the secret key is chosen
        // specifically to avoid zero terms.
        assert!(bool::from(batch_invert(&mut denoms)), "Inversion failure");
        // Calculate `g1•v•1/denom` for each member
        let mut wnaf = Wnaf::new();
        let mut wnaf_base = wnaf.base(accum.active.0.into(), denoms.len() + 1);
        let values = members
            .iter()
            .copied()
            .zip(&denoms)
            .map(|((index, _), denom)| (wnaf_base.scalar(denom), index))
            .collect();
        // The new partition state is the previous value times the sum of the denominators
        // which is equal to `v•1/sum_i(a + m_i)`
        let term_mul = denoms.iter().sum::<Scalar>();
        Ok((
            BatchRemoval { values, partition },
            AccumulatorPrivate {
                origin: accum.origin,
                scalar: accum.scalar * term_mul,
                active: Accumulator(wnaf_base.scalar(&term_mul).to_affine()),
            },
        ))
    }
}

/// A wrapper for a membership witness being updated.
pub struct UpdateMembershipWitness {
    witness: G1Projective,
    index: IndexType,
    value: Scalar,
    partition: IndexType,
}

impl UpdateMembershipWitness {
    pub(crate) fn new(membership: &MembershipWitness, partition: IndexType) -> Self {
        Self {
            witness: membership.witness.into(),
            index: membership.index,
            value: compute_member_value(membership.index),
            partition,
        }
    }

    /// Apply a batch removal operation to this membership witness.
    pub fn apply_batch_removal(&mut self, batch: &BatchRemoval) -> Result<(), AccumulatorError> {
        if self.partition != batch.partition {
            Err(AccumulatorError::InvalidPartition)
        } else if batch
            .values
            .iter()
            .copied()
            .any(|(_, member)| member == self.index)
        {
            Err(AccumulatorError::MemberRemoved)
        } else {
            let mut points = Vec::with_capacity(batch.values.len() + 1);
            points.push(self.witness);
            let mut denoms = Vec::with_capacity(batch.values.len() + 1);
            denoms.push(Scalar::ONE);
            for (pt, member) in batch.values.iter().copied() {
                points.push(pt);
                let term = Scalar::from(member) - self.value;
                denoms[0] *= term;
                denoms.push(-term);
            }
            // This inversion should never fail as all the terms are checked to be non-zero
            assert!(bool::from(batch_invert(&mut denoms)), "Inversion error");
            self.witness = G1Projective::sum_of_products(&points, &denoms);
            Ok(())
        }
    }

    /// After applying all updates in an epoch, verify the witness against the current public state.
    pub fn finalize_unsigned(
        self,
        registry: &RegistryPublic,
    ) -> Result<MembershipWitness, AccumulatorError> {
        let witness = MembershipWitness {
            witness: self.witness.to_affine(),
            index: self.index,
        };
        registry.verify_membership_witness(&witness)?;
        Ok(witness)
    }

    /// After applying all updates in an epoch, verify the partition signature and return a signed membership witness.
    pub fn finalize_signed(
        self,
        registry: &SplitRegistryPublic,
        signature: PartitionSignature,
    ) -> Result<SignedMembershipWitness, AccumulatorError> {
        if signature.index != self.partition {
            Err(AccumulatorError::InvalidSignature)
        } else {
            let witness = SignedMembershipWitness {
                membership: MembershipWitness {
                    witness: self.witness.to_affine(),
                    index: self.index,
                },
                partition: signature,
            };
            registry.verify_membership_witness(&witness)?;
            Ok(witness)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::accum::new_registry;
    use crate::split_accum::new_split_registry;

    #[test]
    fn batch_remove() {
        let mut rng = rand::thread_rng();
        let capacity = 16384;
        let epoch0 = 0;
        let (sk, pk) = new_registry(capacity, epoch0, &mut rng);
        let witness1 = sk.create_membership_witness(1).unwrap();
        let witness2 = sk.create_membership_witness(2).unwrap();
        let witness3 = sk.create_membership_witness(3).unwrap();
        pk.verify_membership_witness(&witness1)
            .expect("Error verifying witness");
        pk.verify_membership_witness(&witness2)
            .expect("Error verifying witness");
        pk.verify_membership_witness(&witness3)
            .expect("Error verifying witness");

        // test single removal in batch
        let epoch1 = 1;
        let mut accum1 = sk.clone();
        let update = accum1.remove_members([1]).expect("Error removing members");
        accum1.set_epoch(epoch1);
        // check new accumulator is equal to the membership witness for a single removed value
        assert_eq!(accum1.accum.active.0, witness1.witness);
        // cannot apply batch update for removed member
        assert!(witness1
            .begin_update()
            .apply_batch_removal(&update)
            .is_err());
        // should not be valid against new state
        let pk1 = accum1.to_public();
        assert!(witness1.begin_update().finalize_unsigned(&pk1).is_err());
        // update witness for non-removed member
        let mut upd_witness = witness2.begin_update();
        assert!(upd_witness.apply_batch_removal(&update).is_ok());
        assert!(upd_witness.finalize_unsigned(&pk1).is_ok());

        let mut accum2 = sk.clone();
        // test multi removal
        let update = accum2
            .remove_members([1, 2])
            .expect("Error removing members");
        // cannot apply batch update for removed member
        assert!(witness1
            .begin_update()
            .apply_batch_removal(&update)
            .is_err());
        // should not be valid against new state
        let pk2 = accum2.to_public();
        assert!(witness1.begin_update().finalize_unsigned(&pk2).is_err());
        // update witness for non-removed member
        let mut upd_witness = witness3.begin_update();
        assert!(upd_witness.apply_batch_removal(&update).is_ok());
        assert!(upd_witness.finalize_unsigned(&pk2).is_ok());
    }

    #[test]
    fn batch_remove_split() {
        let mut rng = rand::thread_rng();
        let capacity = 16384;
        let partition_size = 1024;
        let epoch0 = 0;
        let (sk, pk, accums) = new_split_registry(capacity, partition_size, epoch0, &mut rng);
        let mut accum1 = accums[0].clone();
        let witness1 = sk.create_membership_witness(&accum1, 1).unwrap();
        let witness2 = sk.create_membership_witness(&accum1, 2).unwrap();
        let witness3 = sk.create_membership_witness(&accum1, 3).unwrap();
        pk.verify_membership_witness(&witness1)
            .expect("Error verifying witness");
        pk.verify_membership_witness(&witness2)
            .expect("Error verifying witness");
        pk.verify_membership_witness(&witness3)
            .expect("Error verifying witness");

        // test single removal in batch
        let update = sk
            .remove_partition_members(&mut accum1, [1])
            .expect("Error removing members");
        let epoch1 = 1;
        sk.sign_partition(&mut accum1, epoch1);
        // check new accumulator is equal to the membership witness for a single removed value
        assert_eq!(accum1.signature.accum.0, witness1.membership.witness);
        // cannot apply batch update for removed member
        assert!(witness1
            .begin_update()
            .apply_batch_removal(&update)
            .is_err());
        // should not be valid against new signature
        assert!(witness1
            .begin_update()
            .finalize_signed(&pk, accum1.signature().clone())
            .is_err());
        // update witness for non-removed member
        let mut upd_witness = witness2.begin_update();
        assert!(upd_witness.apply_batch_removal(&update).is_ok());
        assert!(upd_witness.finalize_signed(&pk, accum1.signature()).is_ok());

        let mut accum2 = accums[0].clone();
        // test multi removal
        let update = sk
            .remove_partition_members(&mut accum2, [1, 2])
            .expect("Error removing members");
        sk.sign_partition(&mut accum2, epoch1);
        // cannot apply batch update for removed member
        assert!(witness1
            .begin_update()
            .apply_batch_removal(&update)
            .is_err());
        // should not be valid against new signature
        assert!(witness1
            .begin_update()
            .finalize_signed(&pk, accum2.signature().clone())
            .is_err());
        // update witness for non-removed member
        let mut upd_witness = witness3.begin_update();
        assert!(upd_witness.apply_batch_removal(&update).is_ok());
        assert!(upd_witness.finalize_signed(&pk, accum2.signature()).is_ok());
    }
}
