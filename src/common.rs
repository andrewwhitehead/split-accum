//! Accumulator implementation

use rand::RngCore;
use std::{fmt, vec::Vec};

use bls12_381_plus::{
    elliptic_curve::{hash2curve::ExpandMsgXmd, subtle::Choice},
    ff::Field,
    Scalar,
};
use sha2::Sha256;

/// The type of epoch identifiers.
pub type EpochType = u32;
/// The type of member and partition indexes.
pub type IndexType = u32;

/// Compute an encoded member value from an index.
/// The caller must ensure that the index is non-zero and
/// appropriate for the current partition or registry.
pub fn compute_member_value(index: IndexType) -> Scalar {
    debug_assert!(index != 0, "Member index must not be zero");
    Scalar::from(index)
}

/// Possible error cases from split accumulator usage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccumulatorError {
    /// There is a mismatch between the witness epoch and the current epoch.
    EpochMismatch,
    /// A validation error occurred in parsing the witness update log.
    InvalidLog,
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
    /// Wrap IO errors from log operations.
    Io(std::io::ErrorKind),
}

impl fmt::Display for AccumulatorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self, f)
    }
}

impl core::error::Error for AccumulatorError {}

impl From<std::io::Error> for AccumulatorError {
    fn from(value: std::io::Error) -> Self {
        AccumulatorError::Io(value.kind())
    }
}

#[derive(Debug, Clone)]
pub struct ZKScalar {
    pub secret: Scalar,
    pub blind: Scalar,
}

impl ZKScalar {
    pub fn hidden(secret: Scalar, rng: &mut impl RngCore) -> Self {
        Self {
            secret,
            blind: nonzero_scalar(rng),
        }
    }

    pub fn random(rng: &mut impl RngCore) -> Self {
        Self {
            secret: nonzero_scalar(rng),
            blind: nonzero_scalar(rng),
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

pub(crate) fn hash_to_scalar(input: &[u8], dst: &[u8]) -> Scalar {
    Scalar::hash::<ExpandMsgXmd<Sha256>>(&input, dst)
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
