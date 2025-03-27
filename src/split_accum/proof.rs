use bls12_381_plus::{
    elliptic_curve::{group::Curve, subtle::ConstantTimeEq},
    multi_miller_loop, G1Affine, G1Projective, G2Affine, G2Prepared, Gt, Scalar,
};
use rand::RngCore;

use crate::{
    common::{compute_member_value, hash_to_scalar, AccumulatorError, ZKScalar},
    split_accum::{Accumulator, PartitionSignature, SignedMembershipWitness, SplitRegistryPublic},
};

impl SignedMembershipWitness {
    /// Begin preparing a membership proof.
    pub fn prepare_proof(
        &self,
        registry: &SplitRegistryPublic,
        mut rng: impl RngCore,
    ) -> Result<PrepareSignedMembershipProof, AccumulatorError> {
        debug_assert!(registry.verify_membership_witness(&self).is_ok());

        // The hidden member handle value
        let m = ZKScalar::hidden(compute_member_value(self.membership.index), &mut rng);
        // The witness value
        let w = self.membership.witness;
        let PartitionSignature {
            // The signature over the accumulator value and epoch
            signature: a,
            // The accumulator value in the G2 subgroup
            g2accum: b,
            // The split accumulator value
            accum: Accumulator(c),
            // The epoch of the signature
            epoch,
            ..
        } = &self.partition;

        // The signature public key for the epoch
        let k = registry.partition_key.epoch_signing_key(*epoch);
        // Random generator used for proving
        let h = registry.h;

        // Unrevealed blinding scalars
        let r1 = ZKScalar::random(&mut rng);
        let r2 = ZKScalar::random(&mut rng);
        let r3 = ZKScalar::hidden(r1.secret * r2.secret, &mut rng);
        let r4 = ZKScalar::random(&mut rng);
        let r5 = ZKScalar::hidden(r4.secret * r2.secret, &mut rng);

        // The blinded signature A'
        let a_p = a * r1.secret;
        // The blinded accumulator value B'
        let b_p = b * r2.secret;
        // The blinded witness value W'
        let w_p = w * r3.secret;
        // \bar{W} <- Cr1r2 - W'm = W'x
        let w_b = c * r3.secret - w_p * m.secret;
        // R = Gr1 + Hr4
        let r = G1Affine::generator() * r1.secret + h * r4.secret;
        // T1 <- Cr1r2~ - W'm~
        let t1 = c * (r2.secret * r1.blind) - w_p * m.blind;
        // T2 <- e(A'r2~, K) - e(Gr3~, G)
        let t2 = multi_miller_loop(&[
            (
                &(a_p * r2.blind).to_affine(),
                &G2Prepared::from(k.to_affine()),
            ),
            (
                &(G1Affine::generator() * (-r3.blind)).to_affine(),
                &G2Prepared::from(G2Affine::generator()),
            ),
        ])
        .final_exponentiation();
        let t3 = G1Affine::generator() * r1.blind + h * r4.blind;
        let t4 = G1Affine::generator() * r3.blind + h * r5.blind - r * r2.blind;

        let mut aff = [G1Affine::generator(); 7];
        G1Projective::batch_normalize(&[a_p, r, t1, t3, t4, w_p, w_b], &mut aff);

        Ok(PrepareSignedMembershipProof {
            pk: registry.clone(),
            epoch: self.partition.epoch,
            a_p: aff[0],
            b_p: b_p.to_affine(),
            r: aff[1],
            t1: aff[2],
            t2,
            t3: aff[3],
            t4: aff[4],
            w_p: aff[5],
            w_b: aff[6],
            r1,
            r2,
            r3,
            r4,
            r5,
            m,
        })
    }
}

/// A proof of knowledge of a signed membership proof in process.
#[derive(Debug, Clone)]
pub struct PrepareSignedMembershipProof {
    pk: SplitRegistryPublic,
    epoch: u32,
    a_p: G1Affine,
    b_p: G2Affine,
    w_p: G1Affine,
    w_b: G1Affine,
    r: G1Affine,
    t1: G1Affine,
    t2: Gt,
    t3: G1Affine,
    t4: G1Affine,
    r1: ZKScalar,
    r2: ZKScalar,
    r3: ZKScalar,
    r4: ZKScalar,
    r5: ZKScalar,
    m: ZKScalar,
}

impl PrepareSignedMembershipProof {
    /// Finalize the proof given a challenge value.
    pub fn finalize(&self, challenge: &Scalar) -> SignedMembershipProof {
        SignedMembershipProof {
            epoch: self.epoch,
            a_p: self.a_p,
            b_p: self.b_p,
            w_p: self.w_p,
            w_b: self.w_b,
            r: self.r,
            t1: self.t1,
            r1: self.r1.blind + self.r1.secret * challenge,
            r2: self.r2.blind + self.r2.secret * challenge,
            r3: self.r3.blind + self.r3.secret * challenge,
            r4: self.r4.blind + self.r4.secret * challenge,
            r5: self.r5.blind + self.r5.secret * challenge,
            m: self.m.blind + self.m.secret * challenge,
        }
    }

    /// Add the challenge input to a shared transcript.
    // FIXME: would be better to use a standard trait here
    pub fn add_challenge_input(&self, out: &mut Vec<u8>) {
        self.pk.add_challenge_input(out);
        out.extend_from_slice(&self.epoch.to_le_bytes());
        out.extend_from_slice(&self.a_p.to_compressed());
        out.extend_from_slice(&self.b_p.to_compressed());
        out.extend_from_slice(&self.t1.to_compressed());
        out.extend_from_slice(&self.t2.to_bytes());
        out.extend_from_slice(&self.t3.to_compressed());
        out.extend_from_slice(&self.t4.to_compressed());
        out.extend_from_slice(&self.w_p.to_compressed());
        out.extend_from_slice(&self.w_b.to_compressed());
    }

    /// Compute the challenge value in isolation.
    pub fn compute_challenge(&self) -> Scalar {
        let mut ch_data = Vec::new();
        self.add_challenge_input(&mut ch_data);
        hash_to_scalar(&ch_data, b"split-accum-member")
    }
}

/// A proof of knowledge of a signed membership witness against a
/// split accumulator registry.
#[derive(Debug, Clone)]
pub struct SignedMembershipProof {
    epoch: u32,
    a_p: G1Affine,
    b_p: G2Affine,
    w_p: G1Affine,
    w_b: G1Affine,
    r: G1Affine,
    t1: G1Affine,
    r1: Scalar,
    r2: Scalar,
    r3: Scalar,
    r4: Scalar,
    r5: Scalar,
    m: Scalar,
}

impl SignedMembershipProof {
    /// Verify the proof of knowledge against a split accumulator registry.
    pub fn verify(
        &self,
        pk: &SplitRegistryPublic,
        challenge: &Scalar,
    ) -> Result<(), AccumulatorError> {
        // FIXME shared challenge would be checked outside of this scope.
        // may need a structure which associates a received SignedMembershipProof with a public key and challenge.
        let ch = self.compute_challenge(pk, *challenge);
        let check_challenge = ch.ct_eq(&challenge);

        if bool::from(check_challenge) {
            Ok(())
        } else {
            Err(AccumulatorError::InvalidProof)
        }
    }

    /// Add the challenge input to a shared transcript.
    // FIXME: would be better to use a standard trait here
    pub fn add_challenge_input(
        &self,
        registry: &SplitRegistryPublic,
        challenge: Scalar,
        out: &mut Vec<u8>,
    ) {
        let k = registry.partition_key.epoch_signing_key(self.epoch);
        let h = registry.h;

        // Combining the pairings using the challenge as randomness
        // (may want to require another RNG instance or compute a hash here):
        let r = challenge;

        let t2 = multi_miller_loop(&[
            (
                &self.a_p,
                &G2Prepared::from((self.b_p * challenge + k * self.r2).to_affine()),
            ),
            (
                &(self.w_p * r).to_affine(),
                &G2Prepared::from(registry.accum_key.member_key),
            ),
            (
                &registry.partition_key.base_point,
                &G2Prepared::from((self.b_p * (self.r1 * r.square())).to_affine()),
            ),
            (
                &(G1Affine::generator() * self.r3
                    + self.w_b * r
                    + (self.w_p * self.m + self.w_b * challenge + self.t1) * r.square())
                .to_affine(),
                &G2Prepared::from(-G2Affine::generator()),
            ),
        ])
        .final_exponentiation();

        let t3 = G1Affine::generator() * self.r1 + h * self.r4 - self.r * challenge;
        let t4 = G1Affine::generator() * self.r3 + h * self.r5 - self.r * self.r2;

        registry.add_challenge_input(out);
        out.extend_from_slice(&self.epoch.to_le_bytes());
        out.extend_from_slice(&self.a_p.to_compressed());
        out.extend_from_slice(&self.b_p.to_compressed());
        out.extend_from_slice(&self.t1.to_compressed());
        out.extend_from_slice(&t2.to_bytes());
        out.extend_from_slice(&t3.to_compressed());
        out.extend_from_slice(&t4.to_compressed());
        out.extend_from_slice(&self.w_p.to_compressed());
        out.extend_from_slice(&self.w_b.to_compressed());
    }

    /// Compute the challenge value in isolation.
    pub fn compute_challenge(&self, pk: &SplitRegistryPublic, challenge: Scalar) -> Scalar {
        let mut ch_data = Vec::new();
        self.add_challenge_input(pk, challenge, &mut ch_data);
        hash_to_scalar(&ch_data, b"split-accum-member")
    }
}

#[cfg(test)]
mod tests {
    use crate::split_accum::new_split_registry;

    #[test]
    fn check_signed_member_proof() {
        let mut rng = rand::thread_rng();
        let capacity = 100;
        let partition_size = 10;
        let epoch0 = 0;
        let (sk, pk, accums) = new_split_registry(capacity, partition_size, epoch0, &mut rng);
        let accum1 = accums[0].clone();

        // create witness against first partition
        let witness = sk
            .create_membership_witness(&accum1, 1)
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
