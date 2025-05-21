//! Operations for creating and managing split bilinear accumulators.

use bls12_381_plus::{
    elliptic_curve::subtle::Choice,
    group::{Curve, Group, Wnaf},
    multi_miller_loop, G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective, Scalar,
};
use rand::RngCore;

use crate::batch_update::BatchRemoval;
use crate::{
    accum::{Accumulator, AccumulatorPublicKey},
    common::hash_to_scalar,
};
use crate::{
    accum::{AccumulatorPrivateKey, MembershipWitness},
    common::{
        batch_invert, compute_member_value, nonzero_scalar, AccumulatorError, EpochType, IndexType,
    },
};

pub mod proof;
pub mod update_log;

/// Create new public and private keys for an accumulator.
pub fn new_split_registry(
    capacity: IndexType,
    partition_size: IndexType,
    epoch: EpochType,
    rng: &mut impl RngCore,
) -> (
    SplitRegistryPrivate,
    SplitRegistryPublic,
    Vec<PartitionPrivate>,
) {
    let sk = SplitRegistryPrivate::new(capacity, partition_size, epoch, rng);
    let pk = sk.to_public();
    let partitions = sk.init_partitions();
    (sk, pk, partitions)
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct PartitioningPrivateKey {
    /// The base point for accumulator states and witnesses.
    base_point: G1Affine,
    /// The private key for generating initial partition states.
    init_key: Scalar,
    /// The private key for encoding epoch information.
    epoch_key: Scalar,
    /// The private key for signing partitions.
    signing_key: Scalar,
    /// The public key.
    public: PartitioningPublicKey,
}

impl PartitioningPrivateKey {
    pub fn new(rng: &mut impl RngCore) -> Self {
        let base_point = G1Projective::random(&mut *rng).to_affine();
        let init_key = nonzero_scalar(rng);
        let signing_key = nonzero_scalar(rng);
        let epoch_key = nonzero_scalar(rng);
        let p2 = G2Affine::generator();
        PartitioningPrivateKey {
            base_point,
            init_key,
            epoch_key,
            signing_key,
            public: PartitioningPublicKey {
                base_point: base_point,
                epoch_key: (p2 * epoch_key).to_affine(),
                signing_key: (p2 * signing_key).to_affine(),
            },
        }
    }
}

/// A public key for verifying signed accumulator partitions.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct PartitioningPublicKey {
    /// The base point for accumulator states and witnesses.
    pub base_point: G1Affine,
    /// The public key for encoding epoch information.
    pub epoch_key: G2Affine,
    /// The public key for verifying signatures.
    pub signing_key: G2Affine,
}

impl PartitioningPublicKey {
    /// Fetch the signing key for a specific epoch.
    pub fn epoch_signing_key(&self, epoch: EpochType) -> G2Projective {
        self.signing_key + self.epoch_key * Scalar::from(epoch)
    }

    /// Verify a signature over an partition state.
    #[must_use]
    pub(crate) fn verify_partition_signature(&self, signature: &PartitionSignature) -> Choice {
        // Combining these pairings using an additional deterministic factor (r),
        // deterministically chosen.
        // e(S, G2x + G2y•epoch + U) =? e(G1, G2)
        // e(V, G2) =? e(G1, U)
        // => e(S, G2x + G2y•epoch + U)•e(G1•r, U) =? e(G1 + V•r, G2)
        let mut enc = Vec::with_capacity(48 + 48 + 96);
        enc.extend_from_slice(&signature.accum.0.to_compressed());
        enc.extend_from_slice(&signature.g2accum.to_compressed());
        enc.extend_from_slice(&signature.signature.to_compressed());
        let r = hash_to_scalar(&enc, b"pairing factor");

        multi_miller_loop(&[
            (
                &signature.signature,
                &G2Prepared::from(
                    (self.signing_key
                        + self.epoch_key * Scalar::from(signature.epoch)
                        + signature.g2accum)
                        .to_affine(),
                ),
            ),
            (
                &(self.base_point * r).to_affine(),
                &G2Prepared::from(signature.g2accum),
            ),
            (
                &-(G1Affine::generator() + signature.accum.0 * r).to_affine(),
                &G2Prepared::from(G2Affine::generator()),
            ),
        ])
        .final_exponentiation()
        .is_identity()
    }
}

/// A signature for a split accumulator state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartitionSignature {
    /// The state of the partition in the G1 subgroup.
    pub accum: Accumulator,
    /// The state of the partition in the G2 subgroup.
    pub g2accum: G2Affine,
    /// The signature over the state of the partition and the epoch.
    pub signature: G1Affine,
    /// The partition index.
    pub index: IndexType,
    /// The epoch value.
    pub epoch: EpochType,
}

/// The private information for a split accumulator instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartitionPrivate {
    /// The current state of the partition as a scalar, relative to the base point.
    pub(crate) state: Scalar,
    /// The current state of the partition as an accumulator.
    pub(crate) accum: Accumulator,
    /// The partition index.
    pub(crate) index: IndexType,
    /// The latest partition signature, against which witnesses are created.
    pub(crate) signature: PartitionSignature,
}

impl PartitionPrivate {
    /// Access the partition index.
    pub fn index(&self) -> IndexType {
        self.index
    }

    /// Access the partition signature.
    pub fn signature(&self) -> PartitionSignature {
        self.signature.clone()
    }
}

/// A membership witness against a signed accumulator state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedMembershipWitness {
    /// The witness against the accumulator state.
    pub membership: MembershipWitness,
    /// The signed partition information.
    pub partition: PartitionSignature,
}

/// The private part of a split accumulator registry.
#[derive(Debug, Clone)]
pub struct SplitRegistryPrivate {
    /// The total capacity of the registry.
    capacity: IndexType,
    /// The size of each partition.
    partition_size: IndexType,
    /// The private key for accumulating member values.
    accum_key: AccumulatorPrivateKey,
    /// The private key for signing partition states.
    partition_key: PartitioningPrivateKey,
    /// A randomized generator used in proofs.
    h: G1Affine,
    /// The current epoch of the registry.
    epoch: EpochType,
}

impl SplitRegistryPrivate {
    /// Create a new split accumulator registry instance.
    pub fn new(
        capacity: IndexType,
        partition_size: IndexType,
        epoch: EpochType,
        rng: &mut impl RngCore,
    ) -> Self {
        let accum_key = AccumulatorPrivateKey::new(capacity, rng);
        let partition_key = PartitioningPrivateKey::new(rng);
        Self {
            capacity,
            partition_size,
            accum_key,
            partition_key,
            h: G1Projective::random(rng).to_affine(),
            epoch,
        }
    }

    /// Initialize the partitions associated with a split registry.
    pub fn init_partitions(&self) -> Vec<PartitionPrivate> {
        let len = ((self.capacity + self.partition_size - 1) / self.partition_size) as usize;
        let mut ret = Vec::with_capacity(len);
        let mut wnaf = Wnaf::new();
        let mut wnaf_base = wnaf.base(G1Projective::from(self.partition_key.base_point), len);
        let mut part_mul = Scalar::ONE;
        for idx in 0..len {
            part_mul *= self.partition_key.init_key;
            let accum = Accumulator(wnaf_base.scalar(&part_mul).to_affine());
            ret.push(PartitionPrivate {
                // temporary signature, replaced later
                signature: PartitionSignature {
                    accum: Accumulator(G1Affine::generator()),
                    g2accum: G2Affine::generator(),
                    signature: G1Affine::generator(),
                    index: idx as IndexType,
                    epoch: self.epoch,
                },
                state: part_mul,
                accum,
                index: idx as IndexType,
            });
        }
        self.batch_sign_partitions(&mut ret);
        ret
    }

    /// Remove multiple values from the partition state, producing a batch removal operation.
    pub fn remove_partition_members(
        &self,
        partition: &mut PartitionPrivate,
        indices: impl IntoIterator<Item = IndexType>,
    ) -> Result<BatchRemoval, AccumulatorError> {
        let members = indices
            .into_iter()
            .map(|index| {
                if index == 0
                    || index > self.capacity
                    || (index - 1) / self.partition_size != partition.index
                {
                    Err(AccumulatorError::InvalidMember)
                } else {
                    Ok((index, compute_member_value(index)))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let (update, new_accum, state_mul) = BatchRemoval::remove_members(
            &partition.accum,
            &self.accum_key,
            &members,
            partition.index,
        )?;
        partition.accum = new_accum;
        partition.state *= state_mul;
        Ok(update)
    }

    /// Sign a partition, producing a signature over the public state for a specific epoch.
    pub fn sign_partition(&self, partition: &mut PartitionPrivate) {
        let sig_mul = (self.partition_key.signing_key
            + self.partition_key.epoch_key * Scalar::from(self.epoch)
            + partition.state)
            .invert()
            .expect("Inversion error");
        let signature = (G1Affine::generator() * sig_mul).to_affine();
        partition.signature = PartitionSignature {
            accum: partition.accum,
            g2accum: (G2Affine::generator() * partition.state).to_affine(),
            signature,
            index: partition.index,
            epoch: self.epoch,
        }
    }

    /// Sign multiple partition states at once.
    ///
    /// This is the equivalent of calling `sk.sign_partition(p, epoch)` for each
    /// `p` in `partitions` and collecting the results, although more efficient.
    pub fn batch_sign_partitions(&self, partitions: &mut [PartitionPrivate]) {
        let pcount = partitions.len();
        let mut denoms = Vec::with_capacity(pcount);
        let mut g2proj = Vec::with_capacity(pcount);
        let mut sigsproj = Vec::with_capacity(pcount);
        let mut g2commits = vec![G2Affine::generator(); pcount];
        let mut sigs = vec![G1Affine::generator(); pcount];

        for partition in &*partitions {
            denoms.push(
                self.partition_key.signing_key
                    + self.partition_key.epoch_key * Scalar::from(self.epoch)
                    + partition.state,
            );
        }
        // Invert denominators. May fail with negligible probability
        assert!(bool::from(batch_invert(&mut denoms)), "Inversion failure");
        let mut wnaf_g1 = Wnaf::new();
        let mut wnaf_g1base = wnaf_g1.base(G1Projective::GENERATOR, pcount);
        let mut wnaf_g2 = Wnaf::new();
        let mut wnaf_g2base = wnaf_g2.base(G2Projective::GENERATOR, pcount);
        partitions
            .iter()
            .zip(denoms)
            .for_each(|(partition, denom)| {
                g2proj.push(wnaf_g2base.scalar(&partition.state));
                sigsproj.push(wnaf_g1base.scalar(&denom));
            });
        G2Projective::batch_normalize(&g2proj, &mut g2commits);
        G1Projective::batch_normalize(&sigsproj, &mut sigs);

        partitions
            .iter_mut()
            .zip(g2commits.into_iter().zip(sigs))
            .for_each(|(partition, (g2commit, signature))| {
                partition.signature = PartitionSignature {
                    accum: partition.accum,
                    g2accum: g2commit,
                    signature,
                    index: partition.index,
                    epoch: self.epoch,
                }
            });
    }

    /// Create a witness for a member handle against a signed partition state.
    pub fn create_membership_witness(
        &self,
        partition: &PartitionPrivate,
        index: IndexType,
    ) -> Result<SignedMembershipWitness, AccumulatorError> {
        if index == 0 || (index - 1) / self.partition_size != partition.index {
            Err(AccumulatorError::InvalidMember)
        } else {
            let membership = self.accum_key.create_membership_witness(
                &partition.signature.accum,
                index,
                partition.signature.epoch,
            );
            Ok(SignedMembershipWitness {
                membership,
                partition: partition.signature.clone(),
            })
        }
    }

    /// Access the current epoch.
    pub fn epoch(&self) -> EpochType {
        self.epoch
    }

    /// Update the current epoch.
    pub fn set_epoch(&mut self, epoch: EpochType) {
        self.epoch = epoch;
    }

    /// Get the public registry definition.
    pub fn to_public(&self) -> SplitRegistryPublic {
        SplitRegistryPublic {
            accum_key: self.accum_key.public.clone(),
            partition_key: self.partition_key.public.clone(),
            h: self.h,
            epoch: self.epoch,
        }
    }
}

/// The public state of a split registry.
#[derive(Debug, Clone)]
pub struct SplitRegistryPublic {
    /// The public key for verifying membership witnesses.
    pub accum_key: AccumulatorPublicKey,
    /// The public key for verifying signed partition states.
    pub partition_key: PartitioningPublicKey,
    /// A randomized generator used in proving.
    pub h: G1Affine,
    /// The current epoch.
    pub epoch: EpochType,
}

impl SplitRegistryPublic {
    /// Privately verify a signed membership witness.
    pub fn verify_membership_witness(
        &self,
        witness: &SignedMembershipWitness,
    ) -> Result<(), AccumulatorError> {
        if witness.membership.epoch != self.epoch
            || witness.membership.epoch != witness.partition.epoch
        {
            return Err(AccumulatorError::EpochMismatch);
        }
        let chk_wit = self
            .accum_key
            .verify_accumulator_witness(&witness.partition.accum, &witness.membership);
        let chk_sig = self
            .partition_key
            .verify_partition_signature(&witness.partition);
        if bool::from(chk_wit & chk_sig) {
            Ok(())
        } else {
            Err(AccumulatorError::InvalidWitness)
        }
    }

    /// Add the public key to a Fiat-Shamir transcript.
    pub fn add_challenge_input(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.accum_key.member_key.to_compressed());
        out.extend_from_slice(&self.partition_key.base_point.to_compressed());
        out.extend_from_slice(&self.partition_key.signing_key.to_compressed());
        out.extend_from_slice(&self.partition_key.epoch_key.to_compressed());
    }
}

#[cfg(test)]
mod tests {
    use super::new_split_registry;

    #[test]
    fn check_signed_state() {
        let mut rng = rand::thread_rng();
        let capacity = 100;
        let partition_size = 10;
        let epoch0 = 0;
        let (mut sk, pk, mut accums) =
            new_split_registry(capacity, partition_size, epoch0, &mut rng);
        let mut accum1 = accums[0].clone();

        // generate signature for a single accumulator
        sk.sign_partition(&mut accum1);
        assert_eq!(accum1.signature.epoch, epoch0);
        assert!(bool::from(
            pk.partition_key
                .verify_partition_signature(&accum1.signature)
        ));

        // check batch signature for single accumulator
        let epoch1 = 1;
        sk.set_epoch(epoch1);
        sk.batch_sign_partitions(&mut accums[..1]);
        assert_eq!(accums[0].signature.epoch, epoch1);
        assert!(bool::from(
            pk.partition_key
                .verify_partition_signature(&accums[0].signature)
        ));

        // check batch signature for multiple accumulators
        let epoch2 = 2;
        sk.set_epoch(epoch2);
        sk.batch_sign_partitions(&mut accums);
        for accum in &accums {
            assert_eq!(accum.signature.epoch, epoch2);
            assert!(bool::from(
                pk.partition_key
                    .verify_partition_signature(&accum.signature)
            ));
        }
    }
}
