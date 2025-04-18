#![allow(clippy::too_many_arguments)]
use super::commitments::{Commitments, MultiCommitGens};
use super::errors::ProofVerifyError;
use super::group::{CompressedGroup, CompressedGroupExt};
use super::math::Math;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use merlin::Transcript;
use serde::{Deserialize, Serialize};

mod bullet;
use bullet::BulletReductionProof;

#[derive(Serialize, Deserialize, Debug)]
pub struct KnowledgeProof {
  alpha: CompressedGroup,
  z1: Scalar,
  z2: Scalar,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct EqualityProof {
  alpha: CompressedGroup,
  z: Scalar,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct ProductProof {
  alpha: CompressedGroup,
  beta: CompressedGroup,
  delta: CompressedGroup,
  z: [Scalar; 5],
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DotProductProof {
  delta: CompressedGroup,
  beta: CompressedGroup,
  z: Vec<Scalar>,
  z_delta: Scalar,
  z_beta: Scalar,
}

#[derive(Clone, Serialize)]
pub struct DotProductProofGens {
  n: usize,
  pub gens_n: MultiCommitGens,
  pub gens_1: MultiCommitGens,
}

impl DotProductProofGens {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let (gens_n, gens_1) = MultiCommitGens::new(n + 1, label).split_at(n);
    DotProductProofGens { n, gens_n, gens_1 }
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DotProductProofLog {
  bullet_reduction_proof: BulletReductionProof,
  delta: CompressedGroup,
  beta: CompressedGroup,
  z1: Scalar,
  z2: Scalar,
}

impl DotProductProofLog {
  fn protocol_name() -> &'static [u8] {
    b"dot product proof (log)"
  }

  pub fn compute_dotproduct(a: &[Scalar], b: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| a[i] * b[i]).sum()
  }

  pub fn prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    blind_x: &Scalar,
    a_vec: &[Scalar],
    y: &Scalar,
    blind_y: &Scalar,
  ) -> (DotProductProofLog, CompressedGroup, CompressedGroup) {
    transcript.append_protocol_name(DotProductProofLog::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert!(gens.n >= n);

    // produce randomness for generating a proof
    let d = random_tape.random_scalar(b"d");
    let r_delta = random_tape.random_scalar(b"r_delta");
    let r_beta = random_tape.random_scalar(b"r_delta");
    let blinds_vec = {
      let v1 = random_tape.random_vector(b"blinds_vec_1", 2 * n.log_2());
      let v2 = random_tape.random_vector(b"blinds_vec_2", 2 * n.log_2());
      (0..v1.len())
        .map(|i| (v1[i], v2[i]))
        .collect::<Vec<(Scalar, Scalar)>>()
    };

    let Cx = x_vec.commit(blind_x, &gens.gens_n).compress();
    Cx.append_to_transcript(b"Cx", transcript);
    let Cy = y.commit(blind_y, &gens.gens_1).compress();
    Cy.append_to_transcript(b"Cy", transcript);
    a_vec.append_to_transcript(b"a", transcript);

    // sample a random base and scale the generator used for
    // the output of the inner product
    let r = transcript.challenge_scalar(b"r");
    let gens_1_scaled = gens.gens_1.scale(&r);

    let blind_Gamma = blind_x + r * blind_y;
    let (bullet_reduction_proof, _Gamma_hat, x_hat, a_hat, g_hat, rhat_Gamma) =
      BulletReductionProof::prove(
        transcript,
        &gens_1_scaled.G[0],
        &gens.gens_n.G[..n],
        &gens.gens_n.h,
        x_vec,
        a_vec,
        &blind_Gamma,
        &blinds_vec,
      );

    let y_hat = x_hat * a_hat;

    let delta = {
      let gens_hat = MultiCommitGens {
        n: 1,
        G: vec![g_hat],
        h: gens.gens_1.h,
      };
      d.commit(&r_delta, &gens_hat).compress()
    };
    delta.append_to_transcript(b"delta", transcript);

    let beta = d.commit(&r_beta, &gens_1_scaled).compress();
    beta.append_to_transcript(b"beta", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z1 = d + c * y_hat;
    let z2 = a_hat * (c * rhat_Gamma + r_beta) + r_delta;

    (
      DotProductProofLog {
        bullet_reduction_proof,
        delta,
        beta,
        z1,
        z2,
      },
      Cx,
      Cy,
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    a: &[Scalar],
    Cx: &CompressedGroup,
    Cy: &CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.n >= n);
    assert_eq!(a.len(), n);

    transcript.append_protocol_name(DotProductProofLog::protocol_name());
    Cx.append_to_transcript(b"Cx", transcript);
    Cy.append_to_transcript(b"Cy", transcript);
    a.append_to_transcript(b"a", transcript);

    // sample a random base and scale the generator used for
    // the output of the inner product
    let r = transcript.challenge_scalar(b"r");
    let gens_1_scaled = gens.gens_1.scale(&r);

    let Gamma = Cx.unpack()? + r * Cy.unpack()?;

    let (g_hat, Gamma_hat, a_hat) =
      self
        .bullet_reduction_proof
        .verify(n, a, transcript, &Gamma, &gens.gens_n.G[..n])?;

    self.delta.append_to_transcript(b"delta", transcript);
    self.beta.append_to_transcript(b"beta", transcript);

    let c = transcript.challenge_scalar(b"c");

    let c_s = &c;
    let beta_s = self.beta.unpack()?;
    let a_hat_s = &a_hat;
    let delta_s = self.delta.unpack()?;
    let z1_s = &self.z1;
    let z2_s = &self.z2;

    let lhs = ((Gamma_hat * c_s + beta_s) * a_hat_s + delta_s).compress();
    let rhs = ((g_hat + gens_1_scaled.G[0] * a_hat_s) * z1_s + gens_1_scaled.h * z2_s).compress();

    assert_eq!(lhs, rhs);

    if lhs == rhs {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  #[test]
  fn check_knowledgeproof() {
    let mut csprng: OsRng = OsRng;

    let gens_1 = MultiCommitGens::new(1, b"test-knowledgeproof");

    let x = Scalar::random(&mut csprng);
    let r = Scalar::random(&mut csprng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, committed_value) =
      KnowledgeProof::prove(&gens_1, &mut prover_transcript, &mut random_tape, &x, &r);

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &committed_value)
      .is_ok());
  }

  #[test]
  fn check_equalityproof() {
    let mut csprng: OsRng = OsRng;

    let gens_1 = MultiCommitGens::new(1, b"test-equalityproof");
    let v1 = Scalar::random(&mut csprng);
    let v2 = v1;
    let s1 = Scalar::random(&mut csprng);
    let s2 = Scalar::random(&mut csprng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, C1, C2) = EqualityProof::prove(
      &gens_1,
      &mut prover_transcript,
      &mut random_tape,
      &v1,
      &s1,
      &v2,
      &s2,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &C1, &C2)
      .is_ok());
  }

  #[test]
  fn check_productproof() {
    let mut csprng: OsRng = OsRng;

    let gens_1 = MultiCommitGens::new(1, b"test-productproof");
    let x = Scalar::random(&mut csprng);
    let rX = Scalar::random(&mut csprng);
    let y = Scalar::random(&mut csprng);
    let rY = Scalar::random(&mut csprng);
    let z = x * y;
    let rZ = Scalar::random(&mut csprng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, X, Y, Z) = ProductProof::prove(
      &gens_1,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &rX,
      &y,
      &rY,
      &z,
      &rZ,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &X, &Y, &Z)
      .is_ok());
  }

  #[test]
  fn check_dotproductproof() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens_1 = MultiCommitGens::new(1, b"test-two");
    let gens_1024 = MultiCommitGens::new(n, b"test-1024");

    let mut x: Vec<Scalar> = Vec::new();
    let mut a: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      x.push(Scalar::random(&mut csprng));
      a.push(Scalar::random(&mut csprng));
    }
    let y = DotProductProofLog::compute_dotproduct(&x, &a);
    let r_x = Scalar::random(&mut csprng);
    let r_y = Scalar::random(&mut csprng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Cx, Cy) = DotProductProof::prove(
      &gens_1,
      &gens_1024,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &a,
      &y,
      &r_y,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &gens_1024, &mut verifier_transcript, &a, &Cx, &Cy)
      .is_ok());
  }

  #[test]
  fn check_dotproductproof_log() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens = DotProductProofGens::new(n, b"test-1024");

    let x: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let a: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let y = DotProductProof::compute_dotproduct(&x, &a);

    let r_x = Scalar::random(&mut csprng);
    let r_y = Scalar::random(&mut csprng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Cx, Cy) = DotProductProofLog::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &a,
      &y,
      &r_y,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &a, &Cx, &Cy)
      .is_ok());
  }
}
