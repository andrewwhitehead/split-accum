use bls12_381_plus::group::Wnaf;
use bls12_381_plus::{group::Curve, G1Affine, G1Projective, Scalar};

use crate::accum::{Accumulator, AccumulatorPrivateKey, MembershipWitness, RegistryPublic};
use crate::common::{batch_invert, compute_member_value, AccumulatorError, IndexType};
use crate::split_accum::{PartitionSignature, SignedMembershipWitness, SplitRegistryPublic};
use crate::EpochType;

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
    pub(crate) values: Vec<(IndexType, G1Affine)>,
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
        accum: &Accumulator,
        sk: &AccumulatorPrivateKey,
        members: &[(IndexType, Scalar)],
        partition: IndexType,
    ) -> Result<(BatchRemoval, Accumulator, Scalar), AccumulatorError> {
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
        let mut wnaf_base = wnaf.base(accum.0.into(), members.len() + 1);
        let mut proj = Vec::with_capacity(members.len() + 1);
        // The new partition state is the previous value times the sum of the denominators
        // which is equal to `v•1/sum_i(a + m_i)`
        let state_mul = denoms.iter().sum::<Scalar>();
        for denom in denoms {
            proj.push(wnaf_base.scalar(&denom));
        }
        proj.push(wnaf_base.scalar(&state_mul));
        let mut aff = vec![G1Affine::identity(); members.len() + 1];
        G1Projective::batch_normalize(&proj, &mut aff);
        let accum = Accumulator(aff.pop().unwrap());
        let values = members
            .iter()
            .copied()
            .zip(aff)
            .map(|((index, _), aff)| (index, aff))
            .collect();
        Ok((BatchRemoval { values, partition }, accum, state_mul))
    }

    pub(crate) fn accumulator(&self) -> Accumulator {
        match self.values.len() {
            0 => Accumulator(G1Affine::identity()), // invalid state
            1 => Accumulator(self.values[0].1),
            _ => Accumulator(
                self.values[1..]
                    .iter()
                    .fold(G1Projective::from(self.values[0].1), |s, p| {
                        s.add_mixed(&p.1)
                    })
                    .to_affine(),
            ),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}

/// A wrapper for a membership witness being updated.
pub struct UpdateMembershipWitness {
    witness: G1Projective,
    index: IndexType,
    value: Scalar,
    epoch: EpochType,
    partition: IndexType,
}

impl UpdateMembershipWitness {
    pub(crate) fn new(membership: &MembershipWitness, partition: IndexType) -> Self {
        Self {
            witness: membership.witness.into(),
            index: membership.index,
            value: compute_member_value(membership.index),
            epoch: membership.epoch,
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
            .any(|(member, _)| member == self.index)
        {
            Err(AccumulatorError::MemberRemoved)
        } else {
            let mut points = Vec::with_capacity(batch.values.len() + 1);
            points.push(self.witness);
            let mut denoms = Vec::with_capacity(batch.values.len() + 1);
            denoms.push(Scalar::ONE);
            for (member, pt) in batch.values.iter().copied() {
                points.push(G1Projective::from(pt));
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

    pub fn start_epoch(&self) -> EpochType {
        self.epoch
    }

    pub fn partition(&self) -> IndexType {
        self.partition
    }

    /// After applying all updates in an epoch, verify the witness against the current public state.
    pub fn finalize_unsigned(
        self,
        registry: &RegistryPublic,
    ) -> Result<MembershipWitness, AccumulatorError> {
        let witness = MembershipWitness {
            witness: self.witness.to_affine(),
            index: self.index,
            epoch: registry.epoch,
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
                    epoch: signature.epoch,
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
        assert_eq!(accum1.accum.0, witness1.witness);
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
        let (mut sk, pk, accums) = new_split_registry(capacity, partition_size, epoch0, &mut rng);
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
        sk.set_epoch(epoch1);
        sk.sign_partition(&mut accum1);
        let pk1 = sk.to_public();
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
            .finalize_signed(&pk1, accum1.signature().clone())
            .is_err());
        // update witness for non-removed member
        let mut upd_witness = witness2.begin_update();
        assert!(upd_witness.apply_batch_removal(&update).is_ok());
        assert!(upd_witness
            .finalize_signed(&pk1, accum1.signature())
            .is_ok());

        let mut accum2 = accums[0].clone();
        // test multi removal
        let update = sk
            .remove_partition_members(&mut accum2, [1, 2])
            .expect("Error removing members");
        sk.sign_partition(&mut accum2);
        // cannot apply batch update for removed member
        assert!(witness1
            .begin_update()
            .apply_batch_removal(&update)
            .is_err());
        // should not be valid against new signature
        assert!(witness1
            .begin_update()
            .finalize_signed(&pk1, accum2.signature().clone())
            .is_err());
        // update witness for non-removed member
        let mut upd_witness = witness3.begin_update();
        assert!(upd_witness.apply_batch_removal(&update).is_ok());
        assert!(upd_witness
            .finalize_signed(&pk1, accum2.signature())
            .is_ok());
    }
}
