//! Accumulator implementation

use rand::RngCore;
use std::{fmt, vec::Vec};

use bls12_381_plus::{
    elliptic_curve::subtle::Choice,
    ff::Field,
    group::{Curve, Group},
    multi_miller_loop, G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective, Scalar,
};

/// Define the configuration parameters for the accumulator.
#[derive(Debug)]
pub struct Config {
    /// The size of a each partition.
    pub partition_size: u32,
    /// The total capacity of the accumulator.
    pub capacity: u32,
}

/// Possible error cases from split accumulator usage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccumulatorError {
    /// An invalid member value was provided for this context.
    InvalidMember,
    /// An invalid partition value was provided for this context.
    InvalidPartition,
    /// A membership proof failed validation.
    InvalidProof,
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
    pub(crate) fn _verify_signed_partition(&self, signature: &SignedPartition) -> Choice {
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

    /// Add the public key to a Fiat-Shamir transcript.
    pub fn add_challenge_input(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.member_key.to_compressed());
        out.extend_from_slice(&self.sign_key.to_compressed());
        out.extend_from_slice(&self.epoch_key.to_compressed());
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
    /// Access a `MemberHandle` for this membership witness.
    pub fn member_handle(&self) -> MemberHandle {
        MemberHandle {
            value: self.value,
            partition: self.signature.partition,
        }
    }

    /// Begin the update process for a membership witness.
    pub fn begin_update(&self) -> UpdateMembershipWitness {
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

pub(crate) fn nonzero_scalar(rng: &mut impl RngCore) -> Scalar {
    loop {
        let val = Scalar::random(&mut *rng);
        if !val.is_zero_vartime() {
            break val;
        }
    }
}

pub(crate) fn batch_invert(values: &mut [Scalar]) -> Choice {
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

    use super::{batch_invert, nonzero_scalar};

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
}
