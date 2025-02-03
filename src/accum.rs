//! Accumulator implementation

use std::vec::Vec;

use bls12_381_plus::{
    elliptic_curve::subtle::{Choice, ConstantTimeEq},
    ff::Field,
    group::{Curve, Group, Wnaf},
    multi_miller_loop, G1Projective, G2Affine, G2Prepared, G2Projective, Scalar,
};
use rand::RngCore;

/// Define the configuration parameters for the accumulator.
#[derive(Debug)]
pub struct Config {
    /// The size of a each partition.
    pub partition_size: u32,
    /// The total capacity of the accumulator.
    pub capacity: u32,
}

/// An accumulator private key.
#[derive(Debug, Clone)]
pub struct SetupPrivate {
    partition_key: Scalar,
    member_key: Scalar,
    sign_key: Scalar,
    epoch_key: Scalar,
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

/// Create new public and private keys for an accumulator.
pub fn create_key(config: &Config, mut rng: impl RngCore) -> (SetupPrivate, SetupPublic) {
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
pub fn initialize(config: &Config, sk: &SetupPrivate) -> Vec<AccumulatorPrivate> {
    let len = ((config.capacity + config.partition_size - 1) / config.partition_size) as usize;
    let mut ret = Vec::with_capacity(len);
    let mut part_mul = Scalar::ONE;
    for idx in 0..len {
        part_mul *= sk.partition_key;
        ret.push(AccumulatorPrivate {
            value: part_mul,
            partition: idx as u32,
        });
    }
    ret
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
    pub fn compute_for_index(config: &Config, index: u32) -> MemberHandle {
        if index > config.capacity {
            panic!("Exceeded accumulator capacity");
        }
        let partition = index / config.partition_size;
        MemberHandle {
            value: Scalar::from(index),
            partition,
        }
    }
}

/// A batch removal operation for a partitioned accumulator.
#[derive(Debug, Clone)]
pub struct BatchRemoval {
    /// The set of terms and encoded member values.
    pub values: Vec<(G1Projective, Scalar)>,
    /// The partition index of the batch operation.
    pub partition: u32,
    /// The value of the new accumulator epoch.
    pub epoch: u32,
}

impl BatchRemoval {
    /// Calculate the final accumulator state from a batch removal operation.
    pub fn accumulator(&self) -> AccumulatorPublic {
        let value = self.values.iter().map(|(pt, _)| pt).sum();
        AccumulatorPublic {
            value,
            partition: self.partition,
            epoch: self.epoch,
        }
    }
}

/// The private information for a split accumulator instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccumulatorPrivate {
    /// The current state of the accumulator.
    pub value: Scalar,
    /// The partition index.
    pub partition: u32,
}

impl AccumulatorPrivate {
    /// Create a public accumulator value from this instance.
    pub fn to_public(&self, epoch: u32) -> AccumulatorPublic {
        AccumulatorPublic {
            value: G1Projective::GENERATOR * self.value,
            partition: self.partition,
            epoch,
        }
    }

    /// Convert multiple private accumulator values to public values.
    pub fn batch_to_public(accums: &[Self], epoch: u32) -> Vec<AccumulatorPublic> {
        let mut wnaf = Wnaf::new();
        let mut wnaf_base = wnaf.base(G1Projective::GENERATOR, accums.len());
        accums
            .iter()
            .map(|acc| AccumulatorPublic {
                value: wnaf_base.scalar(&acc.value),
                partition: acc.partition,
                epoch,
            })
            .collect()
    }

    /// Create a witness for an encoded member handle and a specific epoch value.
    pub fn create_witness(
        &self,
        sk: &SetupPrivate,
        member: MemberHandle,
        epoch: u32,
    ) -> MembershipWitness {
        assert_eq!(
            member.partition, self.partition,
            "Invalid partition for member value"
        );
        let mul = (sk.member_key + member.value)
            .invert()
            .expect("Inversion failure");
        MembershipWitness {
            value: G1Projective::GENERATOR * (self.value * mul),
            member,
            epoch,
        }
    }

    /// Remove multiple values from the accumulator state, producing a batch removal operation.
    pub fn batch_remove(
        &self,
        sk: &SetupPrivate,
        members: impl IntoIterator<Item = MemberHandle>,
        epoch: u32,
    ) -> (Self, BatchRemoval) {
        let members = members.into_iter();
        let mut values = Vec::with_capacity(members.size_hint().0);
        let mut denoms = Vec::with_capacity(values.len());
        for member in members {
            assert_eq!(
                member.partition, self.partition,
                "Invalid partition for member value"
            );
            // store generator in values temporarily
            values.push((G1Projective::GENERATOR, member.value));
            // each denominator starts as `(a + m_i)`
            denoms.push(sk.member_key + member.value);
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
        // invert denominators
        assert!(bool::from(batch_invert(&mut denoms)), "Inversion failure");
        // calculate `v•denom` for each member
        let mut wnaf = Wnaf::new();
        let mut wnaf_base = wnaf.base(G1Projective::GENERATOR * self.value, denoms.len());
        for (value, scalar) in values.iter_mut().zip(&denoms) {
            value.0 = wnaf_base.scalar(scalar);
        }
        // the new accumulator state is the previous value times the sum of the denominators
        let value = self.value * denoms.iter().sum::<Scalar>();
        let accum = Self {
            value,
            partition: self.partition,
        };
        let update = BatchRemoval {
            values,
            partition: self.partition,
            epoch,
        };
        (accum, update)
    }
}

/// A public split accumulator value.
#[derive(Debug, Clone, Copy)]
pub struct AccumulatorPublic {
    /// The accumulator point.
    pub value: G1Projective,
    /// The partition index.
    pub partition: u32,
    /// The epoch value.
    pub epoch: u32,
}

/// A membership witness against a split accumulator instance.
#[derive(Debug)]
pub struct MembershipWitness {
    /// The value of the witness against the accumulator.
    pub value: G1Projective,
    /// The encoded member handle.
    pub member: MemberHandle,
    /// The epoch index of the witness.
    pub epoch: u32,
}

impl MembershipWitness {
    /// Apply a batch removal operation to this membership witness.
    ///
    /// If the operation cannot be applied (possibly because the operation removes this
    /// member) then the result will be `None`.
    pub fn apply_batch_removal(&self, batch: &BatchRemoval) -> Option<MembershipWitness> {
        if self.member.partition != batch.partition
            || batch
                .values
                .iter()
                .any(|(_, member)| member == &self.member.value)
        {
            None
        } else {
            let mut points = Vec::with_capacity(batch.values.len() + 1);
            points.push(self.value);
            let mut denoms = Vec::with_capacity(batch.values.len() + 1);
            denoms.push(Scalar::ONE);
            for (pt, member) in batch.values.iter() {
                points.push(*pt);
                let term = member - self.member.value;
                denoms[0] *= term;
                denoms.push(-term);
            }
            assert!(bool::from(batch_invert(&mut denoms)));
            let value = G1Projective::sum_of_products(&points, &denoms);
            Some(MembershipWitness {
                value,
                member: self.member,
                epoch: batch.epoch,
            })
        }
    }

    /// Privately verify a membership witness against a public accumulator state.
    pub fn verify(&self, pk: &SetupPublic, accum: &AccumulatorPublic) -> Choice {
        let sanity = accum.partition.ct_eq(&self.member.partition) & accum.epoch.ct_eq(&self.epoch);
        let pairing = multi_miller_loop(&[
            (
                &self.value.to_affine(),
                &G2Prepared::from(
                    (pk.member_key + G2Projective::GENERATOR * self.member.value).to_affine(),
                ),
            ),
            (
                &-accum.value.to_affine(),
                &G2Prepared::from(G2Affine::generator()),
            ),
        ])
        .final_exponentiation()
        .is_identity();
        sanity & pairing
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

    use super::{batch_invert, create_key, initialize, nonzero_scalar, Config, MemberHandle};

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
        let (sk, pk) = create_key(&config, rng);
        let accums = initialize(&config, &sk);
        let epoch0 = 1;
        let accum = accums[0].clone();
        let accum_public = accum.to_public(epoch0);
        let member1 = MemberHandle::compute_for_index(&config, 1);
        let member2 = MemberHandle::compute_for_index(&config, 2);
        let member3 = MemberHandle::compute_for_index(&config, 3);
        let witness1 = accum.create_witness(&sk, member1, epoch0);
        let witness2 = accum.create_witness(&sk, member2, epoch0);
        let witness3 = accum.create_witness(&sk, member3, epoch0);
        assert!(
            bool::from(witness1.verify(&pk, &accum_public)),
            "Error verifying witness"
        );
        assert!(
            bool::from(witness2.verify(&pk, &accum_public)),
            "Error verifying witness"
        );
        assert!(
            bool::from(witness3.verify(&pk, &accum_public)),
            "Error verifying witness"
        );

        // test single removal in batch
        let epoch1 = 1;
        let (accum2, update) = accum.batch_remove(&sk, [member1], epoch1);
        // new accumulator is equal to the membership witness for a single removed value
        let accum_check_public = accum2.to_public(epoch1);
        assert_eq!(accum_check_public.value, witness1.value);
        let upd_witness = witness1.apply_batch_removal(&update);
        assert!(upd_witness.is_none());
        let upd_witness = witness2.apply_batch_removal(&update);
        let witness = upd_witness.expect("Expected updated witness");
        assert!(bool::from(witness.verify(&pk, &accum_check_public)));

        // test multi removal
        let (accum2, update) = accum.batch_remove(&sk, [member1, member2], epoch1);
        let accum2_public = accum2.to_public(epoch1);
        assert!(!bool::from(witness1.verify(&pk, &accum2_public)));
        assert!(!bool::from(witness2.verify(&pk, &accum2_public)));
        assert!(!bool::from(witness3.verify(&pk, &accum2_public)));
        let upd_witness = witness1.apply_batch_removal(&update);
        assert!(upd_witness.is_none());
        let upd_witness = witness2.apply_batch_removal(&update);
        assert!(upd_witness.is_none());
        let upd_witness = witness3.apply_batch_removal(&update);
        let witness = upd_witness.expect("Expected updated witness");
        assert!(bool::from(witness.verify(&pk, &accum2_public)));
        assert_eq!(witness.member, member3);
    }
}
