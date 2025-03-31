use bls12_381_plus::{
    elliptic_curve::{group::Group, subtle::ConstantTimeEq},
    multi_miller_loop, G1Affine, G1Projective, G2Affine, G2Prepared, Scalar,
};
use rand::RngCore;

use crate::{
    accum::{MembershipWitness, RegistryPublic},
    common::{compute_member_value, hash_to_scalar, AccumulatorError, ZKScalar},
};

impl MembershipWitness {
    /// Begin preparing a membership proof.
    pub fn prepare_proof(
        &self,
        registry: &RegistryPublic,
        mut rng: impl RngCore,
    ) -> Result<PrepareMembershipProof, AccumulatorError> {
        debug_assert!(registry.verify_membership_witness(&self).is_ok());

        // The accumulator value
        let v = registry.accum.0;
        // The witness value
        let w = self.witness;
        // The hidden member handle value
        let m = ZKScalar::hidden(compute_member_value(self.index), &mut rng);
        // Unrevealed blinding scalar
        let r = ZKScalar::random(&mut rng);

        // The blinded witness value W'
        let w_p = w * r.secret;
        // \bar{W} <- Cr1r2 - W'm = W'x
        let w_b = v * r.secret - w_p * m.secret;
        // T <- Vr~ - W'm~
        let t = v * r.blind - w_p * m.blind;

        let mut aff = [G1Affine::generator(); 3];
        G1Projective::batch_normalize(&[w_p, w_b, t], &mut aff);

        Ok(PrepareMembershipProof {
            pk: registry.clone(),
            w_p: aff[0],
            w_b: aff[1],
            t: aff[2],
            r,
            m,
        })
    }
}

/// A membership proof in process.
#[derive(Debug, Clone)]
pub struct PrepareMembershipProof {
    pk: RegistryPublic,
    w_p: G1Affine,
    w_b: G1Affine,
    t: G1Affine,
    r: ZKScalar,
    m: ZKScalar,
}

impl PrepareMembershipProof {
    /// Finalize the proof given a challenge value.
    pub fn finalize(&self, challenge: &Scalar) -> MembershipProof {
        MembershipProof {
            w_p: self.w_p,
            w_b: self.w_b,
            r: self.r.blind + self.r.secret * challenge,
            m: self.m.blind + self.m.secret * challenge,
        }
    }

    /// Add the challenge input to a shared transcript.
    // FIXME: would be better to use a standard trait here
    pub fn add_challenge_input(&self, out: &mut Vec<u8>) {
        self.pk.add_challenge_input(out);
        out.extend_from_slice(&self.w_p.to_compressed());
        out.extend_from_slice(&self.w_b.to_compressed());
        out.extend_from_slice(&self.t.to_compressed());
    }

    /// Compute the challenge value in isolation.
    pub fn compute_challenge(&self) -> Scalar {
        let mut ch_data = Vec::new();
        self.add_challenge_input(&mut ch_data);
        hash_to_scalar(&ch_data, b"accum-member")
    }
}

/// A proof of knowledge of a membership witness against a public
/// accumulator registry state.
#[derive(Debug, Clone)]
pub struct MembershipProof {
    w_p: G1Affine,
    w_b: G1Affine,
    r: Scalar,
    m: Scalar,
}

impl MembershipProof {
    /// Verify the membership proof against a public registry state.
    pub fn verify(&self, pk: &RegistryPublic, challenge: &Scalar) -> Result<(), AccumulatorError> {
        // FIXME shared challenge would be checked outside of this scope.
        // may need a structure which associates a received MembershipProof with a public key and challenge.
        let ch = self.compute_challenge(pk, *challenge);
        let check_challenge = ch.ct_eq(&challenge);

        let pair = multi_miller_loop(&[
            (&self.w_p, &G2Prepared::from(pk.accum_key.member_key)),
            (&self.w_b, &G2Prepared::from(-G2Affine::generator())),
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
    pub fn add_challenge_input(&self, pk: &RegistryPublic, challenge: Scalar, out: &mut Vec<u8>) {
        let t1 = pk.accum.0 * self.r - self.w_p * self.m - self.w_b * challenge;

        pk.add_challenge_input(out);
        out.extend_from_slice(&self.w_p.to_compressed());
        out.extend_from_slice(&self.w_b.to_compressed());
        out.extend_from_slice(&t1.to_compressed());
    }

    /// Compute the challenge value in isolation.
    pub fn compute_challenge(&self, pk: &RegistryPublic, challenge: Scalar) -> Scalar {
        let mut ch_data = Vec::new();
        self.add_challenge_input(pk, challenge, &mut ch_data);
        hash_to_scalar(&ch_data, b"accum-member")
    }
}

#[cfg(test)]
mod tests {
    use crate::accum::new_registry;

    #[test]
    fn check_member_proof() {
        let mut rng = rand::thread_rng();
        let capacity = 100;
        let epoch0 = 0;
        let (sk, pk) = new_registry(capacity, epoch0, &mut rng);

        // create a witness
        let witness = sk
            .create_membership_witness(1)
            .expect("Error creating witness");
        // prepare proof for witness
        let prepared = witness
            .prepare_proof(&pk, &mut rng)
            .expect("Error preparing membership proof");
        let challenge = prepared.compute_challenge();
        let proof = prepared.finalize(&challenge);
        // verify proof
        proof
            .verify(&pk, &challenge)
            .expect("Error verifying proof");
    }
}
