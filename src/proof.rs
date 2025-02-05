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

impl MembershipWitness {
    /// Begin preparing a membership proof.
    pub fn prepare_proof(
        &self,
        pk: &SetupPublic,
        mut rng: impl RngCore,
    ) -> Result<PrepareMembershipProof, AccumulatorError> {
        let r1 = nonzero_scalar(&mut rng);
        let r1_b = nonzero_scalar(&mut rng);
        let r2 = nonzero_scalar(&mut rng);
        let r2_b = nonzero_scalar(&mut rng);
        let r3 = nonzero_scalar(&mut rng);
        let r3_b = nonzero_scalar(&mut rng);
        let m = self.value;
        let m_b = nonzero_scalar(&mut rng);
        let w = self.witness;
        let SignedPartition {
            commit: v,
            g2commit: u,
            signature: s,
            epoch,
            ..
        } = &self.signature;
        let ri = (r1 * r3).invert().unwrap();
        let r1i = ri * r3;
        let r3i = ri * r1;

        let w_t = w * (r1 * r2);
        let v_t = v * r1;
        let u_t = u * r1;
        let w_b = v_t * r2 - w_t * m;
        let t1 = v_t * r2_b + w_t * m_b;
        let s_t = s * (r3 * r1i);
        let r_key = pk.sign_key + pk.epoch_key * Scalar::from(*epoch);
        let r = (r_key + u) * (r1 * r3i);
        let t2 = r * r3_b + r_key * r1_b;
        // u'c + r(r3^) + r_key(r1^)
        // ur1 + (r_key + u) * (r1 * r3i) + r_key(r1^)

        Ok(PrepareMembershipProof {
            pk: pk.clone(),
            epoch: self.signature.epoch,
            w_t,
            w_b,
            v_t,
            u_t,
            s_t,
            r,
            t1,
            t2,
            r1,
            r1_b,
            r2,
            r2_b,
            r3,
            r3_b,
            m,
            m_b,
        })
    }
}

#[derive(Debug, Clone)]
pub struct PrepareMembershipProof {
    pk: SetupPublic,
    epoch: u32,
    w_t: G1Projective,
    w_b: G1Projective,
    v_t: G1Projective,
    u_t: G2Projective,
    s_t: G1Projective,
    r: G2Projective,
    t1: G1Projective,
    t2: G2Projective,
    r1: Scalar,
    r1_b: Scalar,
    r2: Scalar,
    r2_b: Scalar,
    r3: Scalar,
    r3_b: Scalar,
    m: Scalar,
    m_b: Scalar,
}

impl PrepareMembershipProof {
    pub fn finalize(&self, challenge: &Scalar) -> MembershipProof {
        MembershipProof {
            epoch: self.epoch,
            w_t: self.w_t,
            w_b: self.w_b,
            v_t: self.v_t,
            u_t: self.u_t,
            s_t: self.s_t,
            r: self.r,
            r1_c: self.r1_b + self.r1 * challenge,
            r2_c: self.r2_b - self.r2 * challenge,
            r3_c: self.r3_b - self.r3 * challenge,
            m_c: self.m_b + self.m * challenge,
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
        out.extend_from_slice(&self.w_t.to_compressed());
        out.extend_from_slice(&self.w_b.to_compressed());
        out.extend_from_slice(&self.v_t.to_compressed());
        out.extend_from_slice(&self.u_t.to_compressed());
        out.extend_from_slice(&self.s_t.to_compressed());
        out.extend_from_slice(&self.r.to_compressed());
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
    w_t: G1Projective,
    w_b: G1Projective,
    v_t: G1Projective,
    u_t: G2Projective,
    s_t: G1Projective,
    r: G2Projective,
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

        // Combining the pairings using randomness
        // e(S', R) =? e(G1, G2)
        // e(W', G2a) =? e(Wb, G2)
        // e(G1, U') =? e(V', G2)
        // => e(S', R)•e(W'c, G2a)•e(G1c^2, U') =? e(G1 + Wbc + V'c^2, G2)

        let neg_g2p = G2Prepared::from(-G2Affine::generator());
        let pair = multi_miller_loop(&[
            (&self.s_t.to_affine(), &G2Prepared::from(self.r.to_affine())),
            (
                &(self.w_t * challenge).to_affine(),
                &G2Prepared::from(pk.member_key),
            ),
            (
                &(G1Affine::generator() * challenge.square()).to_affine(),
                &G2Prepared::from(self.u_t.to_affine()),
            ),
            (
                &(G1Affine::generator() + self.w_b * challenge + self.v_t * challenge.square())
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
        let r_key = pk.sign_key + pk.epoch_key * Scalar::from(self.epoch);
        let t1 = self.w_b * challenge + self.v_t * self.r2_c + self.w_t * self.m_c;
        let t2 = self.u_t * challenge + self.r * self.r3_c + r_key * self.r1_c;
        // println!("t1v: {:?}, t2v: {:?}", t1.to_affine(), t2.to_affine());

        pk.add_challenge_input(out);
        out.extend_from_slice(&self.epoch.to_le_bytes());
        out.extend_from_slice(&self.w_t.to_compressed());
        out.extend_from_slice(&self.w_b.to_compressed());
        out.extend_from_slice(&self.v_t.to_compressed());
        out.extend_from_slice(&self.u_t.to_compressed());
        out.extend_from_slice(&self.s_t.to_compressed());
        out.extend_from_slice(&self.r.to_compressed());
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
