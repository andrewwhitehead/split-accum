//! Operations for creating and managing bilinear accumulators.

use bls12_381_plus::{
    elliptic_curve::subtle::Choice,
    ff::Field,
    group::{Curve, Group},
    multi_miller_loop, G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective, Scalar,
};
use rand::RngCore;

use crate::common::{compute_member_value, AccumulatorError, IndexType};
use crate::{batch_update::BatchRemoval, EpochType};

pub mod proof;

/// Create new public and private keys for an accumulator.
pub fn new_registry(
    capacity: IndexType,
    epoch: EpochType,
    rng: &mut impl RngCore,
) -> (RegistryPrivate, RegistryPublic) {
    let sk = RegistryPrivate::new(capacity, epoch, rng);
    let pk = sk.to_public();
    (sk, pk)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// An accumulator value against which witnesses may be issued.
pub struct Accumulator(pub G1Affine);

/// An accumulator private key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AccumulatorPrivateKey {
    pub member_key: Scalar,
    pub public: AccumulatorPublicKey,
}

impl AccumulatorPrivateKey {
    pub fn new(capacity: IndexType, rng: &mut impl RngCore) -> Self {
        let mk_max = (-Scalar::from(capacity + 1)).to_le_bytes();
        let member_key = loop {
            let mk = Scalar::random(&mut *rng);
            if mk.to_le_bytes() < mk_max && !mk.is_zero_vartime() {
                break mk;
            }
        };
        AccumulatorPrivateKey {
            member_key,
            public: AccumulatorPublicKey {
                member_key: (G2Affine::generator() * member_key).to_affine(),
            },
        }
    }

    #[inline]
    pub fn create_membership_witness(
        &self,
        accum: &Accumulator,
        index: IndexType,
        epoch: EpochType,
    ) -> MembershipWitness {
        let value = compute_member_value(index);
        // This inversion is not expected to fail, as no member value should equal `-member_key`
        let mul = (self.member_key + value)
            .invert()
            .expect("Inversion failure");
        MembershipWitness {
            witness: (accum.0 * mul).to_affine(),
            index,
            epoch,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// The public key associated with an accumulator.
pub struct AccumulatorPublicKey {
    /// The public key for verifying member accumulation.
    pub(crate) member_key: G2Affine,
}

impl AccumulatorPublicKey {
    /// Privately verify a membership witness against its accumulator state.
    pub fn verify_accumulator_witness(
        &self,
        accum: &Accumulator,
        membership: &MembershipWitness,
    ) -> Choice {
        let MembershipWitness { index, witness, .. } = membership;
        let value = compute_member_value(*index);
        multi_miller_loop(&[
            (
                &witness,
                &G2Prepared::from((self.member_key + G2Projective::GENERATOR * value).to_affine()),
            ),
            (&-accum.0, &G2Prepared::from(G2Affine::generator())),
        ])
        .final_exponentiation()
        .is_identity()
    }
}

/// An accumulator private key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AccumulatorPrivate {
    pub origin: Accumulator,
    pub scalar: Scalar,
    pub active: Accumulator,
}

impl AccumulatorPrivate {
    pub fn new(rng: &mut impl RngCore) -> Self {
        let origin = Accumulator(G1Projective::random(rng).to_affine());
        Self {
            origin,
            scalar: Scalar::ONE,
            active: origin,
        }
    }
}

/// A membership witness against a public accumulator state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MembershipWitness {
    /// The value of the witness against the accumulator state.
    pub(crate) witness: G1Affine,
    /// The unencoded member index.
    pub(crate) index: IndexType,
    /// The epoch of the witness.
    pub(crate) epoch: EpochType,
}

/// An accumulator private key.
#[derive(Debug, Clone)]
pub struct RegistryPrivate {
    pub(crate) capacity: IndexType,
    pub(crate) accum_key: AccumulatorPrivateKey,
    pub(crate) accum: AccumulatorPrivate,
    pub(crate) epoch: EpochType,
}

impl RegistryPrivate {
    /// Create a new registry.
    pub fn new(capacity: IndexType, epoch: EpochType, rng: &mut impl RngCore) -> Self {
        let accum_key = AccumulatorPrivateKey::new(capacity, rng);
        RegistryPrivate {
            capacity,
            accum_key,
            accum: AccumulatorPrivate::new(rng),
            epoch,
        }
    }

    /// Create a witness for a member handle against a signed partition state.
    pub fn create_membership_witness(
        &self,
        index: IndexType,
    ) -> Result<MembershipWitness, AccumulatorError> {
        if index > self.capacity {
            Err(AccumulatorError::InvalidMember)
        } else {
            Ok(self
                .accum_key
                .create_membership_witness(&self.accum.active, index, self.epoch))
        }
    }

    /// Remove multiple values from the partition state, producing a batch removal operation.
    pub fn remove_members(
        &mut self,
        indices: impl IntoIterator<Item = IndexType>,
    ) -> Result<BatchRemoval, AccumulatorError> {
        let members = indices
            .into_iter()
            .map(|index| {
                if index == 0 || index > self.capacity {
                    Err(AccumulatorError::InvalidMember)
                } else {
                    Ok((index, compute_member_value(index)))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let (update, new_accum) =
            BatchRemoval::remove_members(&self.accum, &self.accum_key, &members, 0)?;
        self.accum = new_accum;
        Ok(update)
    }

    /// Access the registry capacity.
    pub fn capacity(&self) -> IndexType {
        self.capacity
    }

    /// Access the current epoch.
    pub fn epoch(&self) -> EpochType {
        self.epoch
    }

    /// Update the current epoch.
    pub fn set_epoch(&mut self, epoch: EpochType) {
        self.epoch = epoch;
    }

    /// Get the current public registry state.
    pub fn to_public(&self) -> RegistryPublic {
        RegistryPublic {
            accum_key: self.accum_key.public.clone(),
            accum: self.accum.active,
            epoch: self.epoch,
        }
    }
}

/// An accumulator private key.
#[derive(Debug, Clone)]
pub struct RegistryPublic {
    /// The public key for checking accumulated member values.
    pub accum_key: AccumulatorPublicKey,
    /// The current state of the accumulator.
    pub accum: Accumulator,
    /// The current epoch.
    pub epoch: EpochType,
}

impl RegistryPublic {
    /// Privately verify a membership witness against its accumulator state.
    pub fn verify_membership_witness(
        &self,
        witness: &MembershipWitness,
    ) -> Result<(), AccumulatorError> {
        if witness.epoch != self.epoch {
            return Err(AccumulatorError::EpochMismatch);
        }
        if bool::from(
            self.accum_key
                .verify_accumulator_witness(&self.accum, &witness),
        ) {
            Ok(())
        } else {
            Err(AccumulatorError::InvalidWitness)
        }
    }

    /// Add the public key to a Fiat-Shamir transcript.
    pub fn add_challenge_input(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.accum_key.member_key.to_compressed());
        out.extend_from_slice(&self.accum.0.to_compressed());
        out.extend_from_slice(&self.epoch.to_le_bytes());
    }
}
