//! Fast, scalable bilinear accumulators and split accumulators.

#![warn(missing_docs)]

mod accum;
mod batch_update;
mod common;
mod split_accum;

pub use self::{
    accum::{
        new_registry,
        proof::{MembershipProof, PrepareMembershipProof},
        update_log::RegistryUpdateLog,
        AccumulatorPublicKey, RegistryPrivate, RegistryPublic,
    },
    batch_update::BatchRemoval,
    common::{AccumulatorError, EpochType, IndexType},
    split_accum::{
        new_split_registry,
        proof::{PrepareSignedMembershipProof, SignedMembershipProof},
        update_log::SplitRegistryUpdateLog,
        PartitionPrivate, PartitionSignature, PartitioningPublicKey, SplitRegistryPrivate,
        SplitRegistryPublic,
    },
};
