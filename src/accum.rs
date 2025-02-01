use std::vec::Vec;

use bls12_381_plus::{
    elliptic_curve::subtle::Choice,
    ff::Field,
    group::{Curve, Group, Wnaf},
    multi_miller_loop, G1Projective, G2Affine, G2Prepared, G2Projective, Scalar,
};
use rand::RngCore;

#[derive(Debug)]
pub struct Config {
    pub partition_size: u32,
    pub capacity: u32,
}

#[derive(Debug, Clone)]
pub struct SetupPrivate {
    partition_key: Scalar,
    member_key: Scalar,
    sign_key: Scalar,
    epoch_key: Scalar,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct SetupPublic {
    pub member_key: G2Affine,
    pub sign_key: G2Affine,
    pub epoch_key: G2Affine,
}

pub fn setup(config: &Config, mut rng: impl RngCore) -> (SetupPrivate, SetupPublic) {
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

pub fn init(config: &Config, sk: &SetupPrivate) -> Vec<AccumulatorPrivate> {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemberHandle {
    pub value: Scalar,
    pub partition: u32,
}

impl MemberHandle {
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

#[derive(Debug, Clone)]
pub struct BatchRemoval {
    pub values: Vec<(G1Projective, Scalar)>,
    pub partition: u32,
}

impl BatchRemoval {
    pub fn accumulator(&self) -> AccumulatorPublic {
        let value = self.values.iter().map(|(pt, _)| pt).sum();
        AccumulatorPublic {
            value,
            partition: self.partition,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccumulatorPrivate {
    pub value: Scalar,
    pub partition: u32,
}

impl AccumulatorPrivate {
    pub fn to_public(&self) -> AccumulatorPublic {
        AccumulatorPublic {
            value: G1Projective::GENERATOR * self.value,
            partition: self.partition,
        }
    }

    pub fn batch_to_public(accums: &[Self]) -> Vec<AccumulatorPublic> {
        let mut wnaf = Wnaf::new();
        let mut wnaf_base = wnaf.base(G1Projective::GENERATOR, accums.len());
        accums
            .iter()
            .map(|acc| AccumulatorPublic {
                value: wnaf_base.scalar(&acc.value),
                partition: acc.partition,
            })
            .collect()
    }

    pub fn create_witness(&self, sk: &SetupPrivate, member: MemberHandle) -> Witness {
        assert_eq!(
            member.partition, self.partition,
            "Invalid partition for member value"
        );
        let mul = (sk.member_key + member.value)
            .invert()
            .expect("Inversion failure");
        Witness {
            value: G1Projective::GENERATOR * (self.value * mul),
            member,
        }
    }

    pub fn remove(&self, sk: &SetupPrivate, member: &MemberHandle) -> Self {
        // track state?
        assert_eq!(
            member.partition, self.partition,
            "Invalid partition for member value"
        );
        let mul = (sk.member_key + member.value)
            .invert()
            .expect("Invert error");
        Self {
            value: self.value * mul,
            partition: self.partition,
        }
    }

    pub fn batch_remove(
        &self,
        sk: &SetupPrivate,
        members: impl IntoIterator<Item = MemberHandle>,
    ) -> (Self, BatchRemoval) {
        let members = members.into_iter();
        let mut values = Vec::with_capacity(members.size_hint().0);
        let mut inv_mul = Vec::with_capacity(values.len());
        for member in members {
            assert_eq!(
                member.partition, self.partition,
                "Invalid partition for member value"
            );
            values.push((G1Projective::GENERATOR, member.value));
            inv_mul.push(sk.member_key + member.value);
        }
        for idx in 0..inv_mul.len() {
            for jdx in idx + 1..inv_mul.len() {
                let term = values[jdx].1 - values[idx].1;
                inv_mul[idx] *= term;
                inv_mul[jdx] *= -term;
            }
        }
        assert!(bool::from(batch_invert(&mut inv_mul)), "Inversion failure");
        // if values.len() > 2 {
        let mut wnaf = Wnaf::new();
        let mut wnaf_base = wnaf.base(G1Projective::GENERATOR * self.value, inv_mul.len());
        for (value, scalar) in values.iter_mut().zip(&inv_mul) {
            value.0 = wnaf_base.scalar(scalar);
        }
        // } else {
        //     ...
        // }
        let accum = Self {
            value: self.value * inv_mul.iter().sum::<Scalar>(),
            partition: self.partition,
        };
        let update = BatchRemoval {
            values,
            partition: self.partition,
        };
        (accum, update)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AccumulatorPublic {
    pub value: G1Projective,
    pub partition: u32,
}

#[derive(Debug)]
pub struct Witness {
    pub value: G1Projective,
    pub member: MemberHandle,
}

impl Witness {
    pub fn update_removal(
        &self,
        accum: &AccumulatorPublic,
        member: &MemberHandle,
    ) -> Option<Witness> {
        if accum.partition != member.partition
            || accum.partition != self.member.partition
            || member == &self.member
        {
            None
        } else {
            Some(Witness {
                value: (self.value - accum.value)
                    * (member.value - self.member.value)
                        .invert()
                        .expect("Inversion failure"),
                member: self.member,
            })
        }
    }

    pub fn update_batch_removal(&self, batch: &BatchRemoval) -> Option<Witness> {
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
            let mut inv_mul = Vec::with_capacity(batch.values.len() + 1);
            inv_mul.push(Scalar::ONE);
            for (pt, member) in batch.values.iter() {
                points.push(*pt);
                let term = member - self.member.value;
                inv_mul[0] *= term;
                inv_mul.push(-term);
            }
            assert!(bool::from(batch_invert(&mut inv_mul)));
            Some(Witness {
                value: G1Projective::sum_of_products(&points, &inv_mul),
                member: self.member,
            })
        }
    }

    pub fn verify(&self, pk: &SetupPublic, accum: &AccumulatorPublic) -> Choice {
        // FIXME - return false
        assert_eq!(
            self.member.partition, accum.partition,
            "Partition mismatch for witness"
        );
        multi_miller_loop(&[
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
        .is_identity()
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
        let mut accum = Vec::with_capacity(values.len());
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

    use crate::accum::{init, setup, Config};

    use super::{batch_invert, nonzero_scalar, MemberHandle};

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
    fn single_update() {
        let rng = rand::thread_rng();
        let config = Config {
            partition_size: 1024,
            capacity: 16384,
        };
        let (sk, pk) = setup(&config, rng);
        let accums = init(&config, &sk);
        let accum = accums[0].clone();
        let accum_public = accum.to_public();
        let member1 = MemberHandle::compute_for_index(&config, 1);
        let member2 = MemberHandle::compute_for_index(&config, 2);
        let witness1 = accum.create_witness(&sk, member1);
        let witness2 = accum.create_witness(&sk, member2);
        assert!(
            bool::from(witness1.verify(&pk, &accum_public)),
            "Error verifying witness"
        );
        assert!(
            bool::from(witness2.verify(&pk, &accum_public)),
            "Error verifying witness"
        );

        let accum2 = accum.remove(&sk, &member1);
        let accum2_public = accum2.to_public();
        assert!(!bool::from(witness1.verify(&pk, &accum2_public)));
        assert!(!bool::from(witness2.verify(&pk, &accum2_public)));
        let upd_witness = witness1.update_removal(&accum2_public, &member1);
        assert!(upd_witness.is_none());
        let upd_witness = witness2.update_removal(&accum2_public, &member1);
        let witness = upd_witness.expect("Expected updated witness");
        assert!(bool::from(witness.verify(&pk, &accum2_public)));
        assert_eq!(witness.member, member2);
    }

    #[test]
    fn batch_update() {
        let rng = rand::thread_rng();
        let config = Config {
            partition_size: 1024,
            capacity: 16384,
        };
        let (sk, pk) = setup(&config, rng);
        let accums = init(&config, &sk);
        let accum = accums[0].clone();
        let accum_public = accum.to_public();
        let member1 = MemberHandle::compute_for_index(&config, 1);
        let member2 = MemberHandle::compute_for_index(&config, 2);
        let member3 = MemberHandle::compute_for_index(&config, 3);
        let witness1 = accum.create_witness(&sk, member1);
        let witness2 = accum.create_witness(&sk, member2);
        let witness3 = accum.create_witness(&sk, member3);
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
        let accum_check1 = accum.remove(&sk, &member1);
        let (accum_check2, update) = accum.batch_remove(&sk, [member1]);
        assert_eq!(accum_check1, accum_check2);
        // new accumulator is equal to witness for removed value
        let accum_check_public = accum_check1.to_public();
        assert_eq!(accum_check_public.value, witness1.value);
        let upd_witness = witness1.update_batch_removal(&update);
        assert!(upd_witness.is_none());
        let upd_witness = witness2.update_batch_removal(&update);
        let witness = upd_witness.expect("Expected updated witness");
        assert!(bool::from(witness.verify(&pk, &accum_check_public)));

        // test multi removal
        let (accum2, update) = accum.batch_remove(&sk, [member1, member2]);
        let accum2_public = accum2.to_public();
        assert!(!bool::from(witness1.verify(&pk, &accum2_public)));
        assert!(!bool::from(witness2.verify(&pk, &accum2_public)));
        assert!(!bool::from(witness3.verify(&pk, &accum2_public)));
        let upd_witness = witness1.update_batch_removal(&update);
        assert!(upd_witness.is_none());
        let upd_witness = witness2.update_batch_removal(&update);
        assert!(upd_witness.is_none());
        let upd_witness = witness3.update_batch_removal(&update);
        let witness = upd_witness.expect("Expected updated witness");
        assert!(bool::from(witness.verify(&pk, &accum2_public)));
        assert_eq!(witness.member, member3);
    }

    // #[test]
    // fn end_to_end() {
    //     let mut rng = rand::thread_rng();
    //     let config = Config {
    //         partition_size: 1024,
    //         capacity: 16384,
    //     };
    //     let (sk, pk) = setup(&config, rng);
    //     let accums = init(&config, &sk);
    //     let (new_accum, update) = accums[0].batch_remove(
    //         &sk,
    //         (0..100).map(|i| MemberHandle::compute_for_index(&config, i)),
    //     );

    // }
}
