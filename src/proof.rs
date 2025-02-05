use bls12_381_plus::{
    elliptic_curve::{
        group::{Curve, Group},
        hash2curve::ExpandMsgXmd,
        subtle::ConstantTimeEq,
    },
    multi_miller_loop, G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective, Scalar,
};
use rand::RngCore;
use sha2::Sha256;

use crate::common::{
    nonzero_scalar, AccumulatorError, MembershipWitness, SetupPublic, SignedPartition,
};

#[derive(Debug, Clone)]
struct ZKScalar {
    secret: Scalar,
    blind: Scalar,
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

impl MembershipWitness {
    /// Begin preparing a membership proof.
    pub fn prepare_proof(
        &self,
        pk: &SetupPublic,
        mut rng: impl RngCore,
    ) -> Result<PrepareMembershipProof, AccumulatorError> {
        // Unrevealed blinding scalars
        let r1 = ZKScalar::random(&mut rng);
        let r2 = ZKScalar::random(&mut rng);
        let r3 = ZKScalar::random(&mut rng);
        // The hidden member handle value
        let m = ZKScalar::hidden(self.value, &mut rng);
        // The witness value
        let w = self.witness;

        let SignedPartition {
            // The partitioned accumulator value
            commit: v,
            // The accumulator value in the G2 subgroup
            g2commit: u,
            // The signature over the accumulator value and epoch
            signature: s,
            // The epoch of the signature
            epoch,
            ..
        } = &self.signature;

        // The signature public key for the epoch
        let epoch_sign = pk.sign_key + pk.epoch_key * Scalar::from(*epoch);

        let ri = (r1.secret * r3.secret).invert().unwrap();
        // 1/r1
        let r1i = ri * r3.secret;
        // 1/r3
        let r3i = ri * r1.secret;

        // The blinded witness value W'
        let w_p = w * (r1.secret * r2.secret);
        // The blinded accumulator value V'
        let v_p = v * r1.secret;
        // The blinded accumulator value in the G2 subgroup
        let u_p = u * r1.secret;
        // \bar{W} <- V'r2 - W'm = W'a
        let w_b = v_p * r2.secret - w_p * m.secret;
        // Prove the calculation of \bar{W}
        let t1 = v_p * r2.blind + w_p * m.blind;
        // The blinded signature value, S' = Sr3/r1
        let s_p = s * (r3.secret * r1i);
        // The blinded value K' = (G2x + G2y•epoch + U)r1/r3,
        // calculated such that e(S', K') = e(G1, G2)
        let k_p = (epoch_sign + u) * (r1.secret * r3i);
        // Prove the calculation of K'
        let t2 = k_p * r3.blind + epoch_sign * r1.blind;

        Ok(PrepareMembershipProof {
            pk: pk.clone(),
            epoch: self.signature.epoch,
            w_p,
            w_b,
            v_p,
            u_p,
            s_p,
            k_p,
            t1,
            t2,
            r1,
            r2,
            r3,
            m,
        })
    }
}

#[derive(Debug, Clone)]
pub struct PrepareMembershipProof {
    pk: SetupPublic,
    epoch: u32,
    w_p: G1Projective,
    w_b: G1Projective,
    v_p: G1Projective,
    u_p: G2Projective,
    s_p: G1Projective,
    k_p: G2Projective,
    t1: G1Projective,
    t2: G2Projective,
    r1: ZKScalar,
    r2: ZKScalar,
    r3: ZKScalar,
    m: ZKScalar,
}

impl PrepareMembershipProof {
    pub fn finalize(&self, challenge: &Scalar) -> MembershipProof {
        MembershipProof {
            epoch: self.epoch,
            w_p: self.w_p,
            w_b: self.w_b,
            v_p: self.v_p,
            u_p: self.u_p,
            s_p: self.s_p,
            k_p: self.k_p,
            r1_c: self.r1.blind + self.r1.secret * challenge,
            r2_c: self.r2.blind - self.r2.secret * challenge,
            r3_c: self.r3.blind - self.r3.secret * challenge,
            m_c: self.m.blind + self.m.secret * challenge,
        }
    }

    /// Add the challenge input to a shared transcript.
    // FIXME: would be better to use a standard trait here
    pub fn add_challenge_input(&self, out: &mut Vec<u8>) {
        // println!(
        //     "t1: {:?}, t2: {:?}",
        //     self.t1.to_affine(),
        //     self.t2.to_affine()
        // );
        self.pk.add_challenge_input(out);
        out.extend_from_slice(&self.epoch.to_le_bytes());
        out.extend_from_slice(&self.w_p.to_compressed());
        out.extend_from_slice(&self.w_b.to_compressed());
        out.extend_from_slice(&self.v_p.to_compressed());
        out.extend_from_slice(&self.u_p.to_compressed());
        out.extend_from_slice(&self.s_p.to_compressed());
        out.extend_from_slice(&self.k_p.to_compressed());
        out.extend_from_slice(&self.t1.to_compressed());
        out.extend_from_slice(&self.t2.to_compressed());
    }

    /// Compute the challenge value in isolation.
    pub fn compute_challenge(&self) -> Scalar {
        let mut ch_data = Vec::new();
        self.add_challenge_input(&mut ch_data);
        Scalar::hash::<ExpandMsgXmd<Sha256>>(&ch_data, b"split-accum-member")
    }
}

#[derive(Debug, Clone)]
pub struct MembershipProof {
    epoch: u32,
    w_p: G1Projective,
    w_b: G1Projective,
    v_p: G1Projective,
    u_p: G2Projective,
    s_p: G1Projective,
    k_p: G2Projective,
    r1_c: Scalar,
    r2_c: Scalar,
    r3_c: Scalar,
    m_c: Scalar,
}

impl MembershipProof {
    pub fn verify(&self, pk: &SetupPublic, challenge: &Scalar) -> Result<(), AccumulatorError> {
        // FIXME shared challenge would be checked outside of this scope.
        // may need a structure which associates a received MembershipProof with a public key and challenge.
        let ch = self.compute_challenge(pk, *challenge);
        let check_challenge = ch.ct_eq(&challenge);

        // Combining the pairings using the challenge as randomness
        // (may want to require another RNG instance here):
        // e(S', K') =? e(G1, G2)
        // e(W', G2a) =? e(Wb, G2)
        // e(G1, U') =? e(V', G2)
        // => e(S', K')•e(W'c, G2a)•e(G1c^2, U') =? e(G1 + Wbc + V'c^2, G2)

        let neg_g2p = G2Prepared::from(-G2Affine::generator());
        let pair = multi_miller_loop(&[
            (
                &self.s_p.to_affine(),
                &G2Prepared::from(self.k_p.to_affine()),
            ),
            (
                &(self.w_p * challenge).to_affine(),
                &G2Prepared::from(pk.member_key),
            ),
            (
                &(G1Affine::generator() * challenge.square()).to_affine(),
                &G2Prepared::from(self.u_p.to_affine()),
            ),
            (
                &(G1Affine::generator() + self.w_b * challenge + self.v_p * challenge.square())
                    .to_affine(),
                &neg_g2p,
            ),
        ])
        .final_exponentiation()
        .is_identity();

        if bool::from(pair & check_challenge) {
            Ok(())
        } else {
            Err(AccumulatorError::InvalidProof)
        }
    }

    /// Add the challenge input to a shared transcript.
    // FIXME: would be better to use a standard trait here
    pub fn add_challenge_input(&self, pk: &SetupPublic, challenge: Scalar, out: &mut Vec<u8>) {
        let epoch_sign = pk.sign_key + pk.epoch_key * Scalar::from(self.epoch);
        let t1 = self.w_b * challenge + self.v_p * self.r2_c + self.w_p * self.m_c;
        let t2 = self.u_p * challenge + self.k_p * self.r3_c + epoch_sign * self.r1_c;
        // println!("t1v: {:?}, t2v: {:?}", t1.to_affine(), t2.to_affine());

        pk.add_challenge_input(out);
        out.extend_from_slice(&self.epoch.to_le_bytes());
        out.extend_from_slice(&self.w_p.to_compressed());
        out.extend_from_slice(&self.w_b.to_compressed());
        out.extend_from_slice(&self.v_p.to_compressed());
        out.extend_from_slice(&self.u_p.to_compressed());
        out.extend_from_slice(&self.s_p.to_compressed());
        out.extend_from_slice(&self.k_p.to_compressed());
        out.extend_from_slice(&t1.to_compressed());
        out.extend_from_slice(&t2.to_compressed());
    }

    /// Compute the challenge value in isolation.
    pub fn compute_challenge(&self, pk: &SetupPublic, challenge: Scalar) -> Scalar {
        let mut ch_data = Vec::new();
        self.add_challenge_input(pk, challenge, &mut ch_data);
        Scalar::hash::<ExpandMsgXmd<Sha256>>(&ch_data, b"split-accum-member")
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn check_member_proof() {
        use crate::common::MemberHandle;
        use crate::manager::*;

        let mut rng = rand::thread_rng();
        let config = Config {
            partition_size: 10,
            capacity: 100,
        };
        let (sk, pk) = create_keys(&config, &mut rng);
        let accums = initialize(&config, &sk);
        let epoch0 = 0;
        let accum1 = accums[0].clone();
        let member = MemberHandle::compute_for_index(&config, 1).unwrap();

        // generate signature for a single accumulator
        let signed = sk.sign_partition(&accum1, epoch0);
        let witness = sk
            .create_membership_witness(&signed, member)
            .expect("Error creating witness");
        let prepared = witness
            .prepare_proof(&pk, &mut rng)
            .expect("Error preparing membership proof");
        let challenge = prepared.compute_challenge();
        let proof = prepared.finalize(&challenge);
        proof
            .verify(&pk, &challenge)
            .expect("Error verifying proof");
    }
}
