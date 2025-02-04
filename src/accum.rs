//! Accumulator implementation

use std::{fmt, vec::Vec};

use bls12_381_plus::{
    elliptic_curve::subtle::Choice,
    ff::Field,
    group::{Curve, Group, Wnaf},
    multi_miller_loop, G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective, Scalar,
};
use rand::RngCore;

/// Possible error cases from split accumulator usage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccumulatorError {
    /// An invalid member value was provided for this context.
    InvalidMember,
    /// An invalid partition value was provided for this context.
    InvalidPartition,
    /// A partition signature failed validation.
    InvalidSignature,
    /// A membership witness failed validation.
    InvalidWitness,
    /// The witness' member has been removed and the witness cannot be updated.
    MemberRemoved,
}

impl fmt::Display for AccumulatorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self, f)
    }
}

/// Define the configuration parameters for the accumulator.
#[derive(Debug)]
pub struct Config {
    /// The size of a each partition.
    pub partition_size: u32,
    /// The total capacity of the accumulator.
    pub capacity: u32,
}

/// Create new public and private keys for an accumulator.
pub fn create_keys(config: &Config, mut rng: impl RngCore) -> (SetupPrivate, SetupPublic) {
    let mk_max = (-Scalar::from(config.capacity + 1)).to_le_bytes();
    let member_key = loop {
        let mk = Scalar::random(&mut rng);
        if mk.to_le_bytes() < mk_max && !mk.is_zero_vartime() {
            break mk;
        }
    };
    let sk = SetupPrivate {
        partition_key: nonzero_scalar(&mut rng),
        member_key,
        sign_key: nonzero_scalar(&mut rng),
        epoch_key: nonzero_scalar(&mut rng),
    };
    let g2 = G2Projective::GENERATOR;
    let pk = SetupPublic {
        member_key: (g2 * sk.member_key).to_affine(),
        sign_key: (g2 * sk.sign_key).to_affine(),
        epoch_key: (g2 * sk.epoch_key).to_affine(),
    };
    (sk, pk)
}

/// Initialize a new split accumulator.
///
/// The initial state is calculated deterministically from the private key.
pub fn initialize(config: &Config, sk: &SetupPrivate) -> Vec<PartitionPrivate> {
    let len = ((config.capacity + config.partition_size - 1) / config.partition_size) as usize;
    let mut ret = Vec::with_capacity(len);
    let mut wnaf = Wnaf::new();
    let mut wnaf_base = wnaf.base(G1Projective::GENERATOR, len);
    let part_mul = Scalar::ONE;
    for idx in 0..len {
        let state = part_mul * sk.partition_key;
        ret.push(PartitionPrivate {
            state,
            commit: wnaf_base.scalar(&state),
            partition: idx as u32,
        });
    }
    ret
}

/// An accumulator private key.
#[derive(Debug, Clone)]
pub struct SetupPrivate {
    partition_key: Scalar,
    member_key: Scalar,
    sign_key: Scalar,
    epoch_key: Scalar,
}

impl SetupPrivate {
    /// Remove multiple values from the partition state, producing a batch removal operation.
    pub fn remove_partition_members(
        &self,
        accum: &PartitionPrivate,
        members: impl IntoIterator<Item = MemberHandle>,
    ) -> Result<(PartitionPrivate, BatchRemoval), AccumulatorError> {
        let members = members.into_iter();
        let mut values = Vec::with_capacity(members.size_hint().0);
        let mut denoms = Vec::with_capacity(values.len());
        for member in members {
            if member.partition != accum.partition {
                return Err(AccumulatorError::InvalidPartition);
            }
            // store generator in values temporarily
            values.push((G1Projective::GENERATOR, member.value));
            // each denominator starts as `(a + m_i)`
            denoms.push(self.member_key + member.value);
        }
        for idx in 0..denoms.len() {
            for jdx in idx + 1..denoms.len() {
                let term = values[jdx].1 - values[idx].1;
                // multiply each index `i` by `(m_j - m_i)`
                denoms[idx] *= term;
                // multiply each index `j` by `(m_i - m_j)`
                denoms[jdx] *= -term;
            }
        }
        // Invert denominators. May fail with negligible probability
        assert!(bool::from(batch_invert(&mut denoms)), "Inversion failure");
        // Calculate `g1•v•1/denom` for each member
        let mut wnaf = Wnaf::new();
        let mut wnaf_base = wnaf.base(G1Projective::GENERATOR, denoms.len() + 1);
        for (value, scalar) in values.iter_mut().zip(&denoms) {
            value.0 = wnaf_base.scalar(&(accum.state * scalar));
        }
        // The new partition state is the previous value times the sum of the denominators
        // which is equal to `v•1/sum_i(a + m_i)`
        let new_state = accum.state * denoms.iter().sum::<Scalar>();
        let accum = PartitionPrivate {
            state: new_state,
            commit: wnaf_base.scalar(&new_state),
            partition: accum.partition,
        };
        let update = BatchRemoval {
            values,
            partition: accum.partition,
        };
        Ok((accum, update))
    }

    /// Sign a partition, producing a signature over the public state for a specific epoch.
    pub fn sign_partition(&self, accum: &PartitionPrivate, epoch: u32) -> SignedPartition {
        let mul = (self.sign_key + self.epoch_key * Scalar::from(epoch) + accum.state)
            .invert()
            .expect("Inversion error");
        let signature = G1Projective::GENERATOR * mul;
        SignedPartition {
            commit: accum.commit,
            g2commit: G2Projective::GENERATOR * accum.state,
            signature,
            partition: accum.partition,
            epoch,
        }
    }

    /// Sign multiple partition states at once.
    ///
    /// This is the equivalent of calling `sk.sign_partition(accum, epoch)` for each
    /// `accum` in `accums` and collecting the results, although more efficient.
    pub fn batch_sign_partitions(
        &self,
        accums: &[PartitionPrivate],
        epoch: u32,
    ) -> Vec<SignedPartition> {
        let mut denoms = Vec::with_capacity(accums.len());
        for acc in accums {
            denoms.push(self.sign_key + self.epoch_key * Scalar::from(epoch) + acc.state);
        }
        // Invert denominators. May fail with negligible probability
        assert!(bool::from(batch_invert(&mut denoms)), "Inversion failure");
        let mut wnaf_g1 = Wnaf::new();
        let mut wnaf_g1base = wnaf_g1.base(G1Projective::GENERATOR, accums.len());
        let mut wnaf_g2 = Wnaf::new();
        let mut wnaf_g2base = wnaf_g2.base(G2Projective::GENERATOR, accums.len());
        accums
            .iter()
            .zip(denoms)
            .map(|(acc, denom)| SignedPartition {
                commit: acc.commit,
                g2commit: wnaf_g2base.scalar(&acc.state),
                signature: wnaf_g1base.scalar(&denom),
                partition: acc.partition,
                epoch,
            })
            .collect()
    }

    /// Create a witness for a member handle against a signed partition state.
    pub fn create_membership_witness(
        &self,
        signature: &SignedPartition,
        member: MemberHandle,
    ) -> Result<MembershipWitness, AccumulatorError> {
        if member.partition != signature.partition {
            return Err(AccumulatorError::InvalidPartition);
        }
        // This inversion is not expected to fail, as no member value should equal `-member_key`
        let mul = (self.member_key + member.value)
            .invert()
            .expect("Inversion failure");
        Ok(MembershipWitness {
            signature: signature.clone(),
            witness: signature.commit * mul,
            value: member.value,
        })
    }
}

/// An accumulator public key.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct SetupPublic {
    /// The public key for verifying member accumulation.
    pub member_key: G2Affine,
    /// The public key for verifying signatures.
    pub sign_key: G2Affine,
    /// The public key for encoding epoch information.
    pub epoch_key: G2Affine,
}

impl SetupPublic {
    /// Privately verify a membership witness against its partition state and signature.
    pub fn verify_membership_witness(
        &self,
        member: &MembershipWitness,
    ) -> Result<(), AccumulatorError> {
        let MembershipWitness {
            signature, witness, ..
        } = member;
        let pairing = multi_miller_loop(&[
            (
                &witness.to_affine(),
                &G2Prepared::from(
                    (self.member_key + G2Projective::GENERATOR * member.value).to_affine(),
                ),
            ),
            (
                &-signature.commit.to_affine(),
                &G2Prepared::from(G2Affine::generator()),
            ),
        ])
        .final_exponentiation()
        .is_identity();
        let check_sig = self._verify_signed_partition(signature);
        if !bool::from(pairing) {
            Err(AccumulatorError::InvalidWitness)
        } else if !bool::from(check_sig) {
            Err(AccumulatorError::InvalidSignature)
        } else {
            Ok(())
        }
    }

    /// Verify a signature over an partition state.
    #[must_use]
    fn _verify_signed_partition(&self, signature: &SignedPartition) -> Choice {
        let sig_check = multi_miller_loop(&[
            (
                &signature.signature.to_affine(),
                &G2Prepared::from(
                    (self.sign_key
                        + self.epoch_key * Scalar::from(signature.epoch)
                        + signature.g2commit)
                        .to_affine(),
                ),
            ),
            (
                &-G1Affine::generator(),
                &G2Prepared::from(G2Affine::generator()),
            ),
        ])
        .final_exponentiation()
        .is_identity();
        let commit_check = multi_miller_loop(&[
            (
                &signature.commit.to_affine(),
                &G2Prepared::from(G2Affine::generator()),
            ),
            (
                &-G1Affine::generator(),
                &G2Prepared::from(signature.g2commit.to_affine()),
            ),
        ])
        .final_exponentiation()
        .is_identity();
        sig_check & commit_check
    }
}

/// An accumulated member value associated with a specific partition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemberHandle {
    /// The encoded member value
    pub value: Scalar,
    /// The partition index
    pub partition: u32,
}

impl MemberHandle {
    /// Calculate the partitioned `MemberHandle` for a global accumulator index.
    pub fn compute_for_index(
        config: &Config,
        index: u32,
    ) -> Result<MemberHandle, AccumulatorError> {
        if index == 0 || index > config.capacity {
            return Err(AccumulatorError::InvalidMember);
        }
        let partition = (index - 1) / config.partition_size;
        Ok(MemberHandle {
            value: Scalar::from(index),
            partition,
        })
    }
}

/// A batch removal operation for a partitioned accumulator.
#[derive(Debug, Clone)]
pub struct BatchRemoval {
    /// The set of terms and encoded member values.
    pub values: Vec<(G1Projective, Scalar)>,
    /// The partition index of the batch operation.
    pub partition: u32,
}

/// The private information for a split accumulator instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartitionPrivate {
    /// The current state of the partition, respective of previous removals.
    pub state: Scalar,
    /// The state of the partition in the G1 subgroup.
    pub commit: G1Projective,
    /// The partition index.
    pub partition: u32,
}

/// A signed accumulator state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedPartition {
    /// The state of the partition in the G1 subgroup.
    pub commit: G1Projective,
    /// The state of the partition in the G2 subgroup.
    pub g2commit: G2Projective,
    /// The signature over the state of the partition and the epoch.
    pub signature: G1Projective,
    /// The partition index.
    pub partition: u32,
    /// The epoch value.
    pub epoch: u32,
}

/// A membership witness against a signed partition state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MembershipWitness {
    /// The signed partition state corresponding to this witness.
    pub signature: SignedPartition,
    /// The value of the witness against the partition state.
    pub witness: G1Projective,
    /// The encoded member value.
    pub value: Scalar,
}

impl MembershipWitness {
    /// Begin the update process for a membership witness.
    pub fn update(&self) -> UpdateMembershipWitness {
        UpdateMembershipWitness {
            inner: self.clone(),
        }
    }
}

/// A wrapper for a membership witness being updated.
pub struct UpdateMembershipWitness {
    inner: MembershipWitness,
}

impl UpdateMembershipWitness {
    /// Apply a batch removal operation to this membership witness.
    pub fn apply_batch_removal(&mut self, batch: &BatchRemoval) -> Result<(), AccumulatorError> {
        let inner = &self.inner;
        if inner.signature.partition != batch.partition
            || batch
                .values
                .iter()
                .any(|(_, member)| member == &inner.value)
        {
            Err(AccumulatorError::MemberRemoved)
        } else {
            let mut points = Vec::with_capacity(batch.values.len() + 1);
            points.push(inner.witness);
            let mut denoms = Vec::with_capacity(batch.values.len() + 1);
            denoms.push(Scalar::ONE);
            for (pt, member) in batch.values.iter() {
                points.push(*pt);
                let term = member - inner.value;
                denoms[0] *= term;
                denoms.push(-term);
            }
            // This inversion should never fail as all the terms are expected to be non-zero
            assert!(bool::from(batch_invert(&mut denoms)), "Inversion error");
            self.inner.witness = G1Projective::sum_of_products(&points, &denoms);
            Ok(())
        }
    }

    /// After applying all updates in an epoch, update the signature for the membership witness.
    pub fn finalize_with_signature(
        self,
        pk: &SetupPublic,
        signature: &SignedPartition,
    ) -> Result<MembershipWitness, AccumulatorError> {
        if signature.partition != self.inner.signature.partition {
            Err(AccumulatorError::InvalidSignature)
        } else {
            let mut inner = self.inner;
            inner.signature = signature.clone();
            pk.verify_membership_witness(&inner)?;
            Ok(inner)
        }
    }
}

fn nonzero_scalar(rng: &mut impl RngCore) -> Scalar {
    loop {
        let val = Scalar::random(&mut *rng);
        if !val.is_zero_vartime() {
            break val;
        }
    }
}

fn batch_invert(values: &mut [Scalar]) -> Choice {
    if values.is_empty() {
        Choice::from(1)
    } else {
        let mut accum = Vec::with_capacity(values.len() - 1);
        let mut carry = values[0];
        for idx in 1..values.len() {
            accum.push(carry);
            carry *= values[idx];
        }
        let invert = carry.invert();
        let ret = invert.is_some();
        carry = invert.unwrap_or(Scalar::ONE);
        for idx in (1..values.len()).rev() {
            let prev = values[idx];
            values[idx] = carry * accum[idx - 1];
            carry *= prev;
        }
        values[0] = carry;
        ret
    }
}

#[cfg(test)]
mod tests {
    use bls12_381_plus::Scalar;

    use super::{batch_invert, create_keys, initialize, nonzero_scalar, Config, MemberHandle};

    #[test]
    fn check_batch_invert() {
        let mut rng = rand::thread_rng();
        let mut buf = [Scalar::ZERO; 10];
        for idx in 0..buf.len() {
            buf[idx] = nonzero_scalar(&mut rng);
        }
        let mut buf_inv = buf;
        assert!(batch_invert(&mut buf_inv).unwrap_u8() == 1);
        for idx in 0..buf.len() {
            assert_eq!(buf[idx].invert().unwrap(), buf_inv[idx]);
        }

        buf[0] = Scalar::ZERO;
        assert!(batch_invert(&mut buf).unwrap_u8() == 0);
    }

    #[test]
    fn batch_remove() {
        let rng = rand::thread_rng();
        let config = Config {
            partition_size: 1024,
            capacity: 16384,
        };
        let (sk, pk) = create_keys(&config, rng);
        let accums = initialize(&config, &sk);
        let epoch0 = 1;
        let accum = accums[0].clone();
        let signed = sk.sign_partition(&accum, epoch0);
        let member1 = MemberHandle::compute_for_index(&config, 1).unwrap();
        let member2 = MemberHandle::compute_for_index(&config, 2).unwrap();
        let member3 = MemberHandle::compute_for_index(&config, 3).unwrap();
        let witness1 = sk.create_membership_witness(&signed, member1).unwrap();
        let witness2 = sk.create_membership_witness(&signed, member2).unwrap();
        let witness3 = sk.create_membership_witness(&signed, member3).unwrap();
        pk.verify_membership_witness(&witness1)
            .expect("Error verifying witness");
        pk.verify_membership_witness(&witness2)
            .expect("Error verifying witness");
        pk.verify_membership_witness(&witness3)
            .expect("Error verifying witness");

        // test single removal in batch
        let (accum2, update) = sk
            .remove_partition_members(&accum, [member1])
            .expect("Error removing members");
        let epoch1 = 1;
        let accum2_sig = sk.sign_partition(&accum2, epoch1);
        // new accumulator is equal to the membership witness for a single removed value
        assert_eq!(accum2_sig.commit, witness1.witness);
        // cannot apply batch update for removed member
        assert!(witness1.update().apply_batch_removal(&update).is_err());
        // should not be valid against new signature
        assert!(witness1
            .update()
            .finalize_with_signature(&pk, &accum2_sig)
            .is_err());
        // update witness for non-removed member
        let mut upd_witness = witness2.update();
        assert!(upd_witness.apply_batch_removal(&update).is_ok());
        assert!(upd_witness
            .finalize_with_signature(&pk, &accum2_sig)
            .is_ok());

        // test multi removal
        let (accum2, update) = sk
            .remove_partition_members(&accum, [member1, member2])
            .expect("Error removing members");
        let accum2_sig = sk.sign_partition(&accum2, epoch1);
        // cannot apply batch update for removed member
        assert!(witness1.update().apply_batch_removal(&update).is_err());
        // should not be valid against new signature
        assert!(witness1
            .update()
            .finalize_with_signature(&pk, &accum2_sig)
            .is_err());
        // update witness for non-removed member
        let mut upd_witness = witness3.update();
        assert!(upd_witness.apply_batch_removal(&update).is_ok());
        assert!(upd_witness
            .finalize_with_signature(&pk, &accum2_sig)
            .is_ok());
    }

    #[test]
    fn check_signed_state() {
        let rng = rand::thread_rng();
        let config = Config {
            partition_size: 10,
            capacity: 100,
        };
        let (sk, pk) = create_keys(&config, rng);
        let accums = initialize(&config, &sk);
        let epoch0 = 0;
        let accum1 = accums[0].clone();
        let accum2 = accums[1].clone();

        // generate signature for a single accumulator
        let signed = sk.sign_partition(&accum1, epoch0);
        assert!(bool::from(pk._verify_signed_partition(&signed)));

        // check batch signature for single accumulator
        let batch_signed = sk.batch_sign_partitions(&[accum1.clone()], epoch0);
        assert!(batch_signed.len() == 1);
        assert!(bool::from(pk._verify_signed_partition(&batch_signed[0])));

        // check batch signature for two accumulators
        let batch_signed = sk.batch_sign_partitions(&[accum1.clone(), accum2.clone()], epoch0);
        assert!(batch_signed.len() == 2);
        assert!(bool::from(pk._verify_signed_partition(&batch_signed[0])));
        assert!(bool::from(pk._verify_signed_partition(&batch_signed[1])));
    }
}
