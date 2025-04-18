#![allow(clippy::too_many_arguments)]
use crate::{ProverWitnessSecInfo, VerifierWitnessSecInfo};

use super::commitments::MultiCommitGens;
use super::dense_mlpoly::{
  DensePolynomial, EqPolynomial, PolyCommitmentGens, PolyEvalProof,
};
use super::custom_dense_mlpoly::DensePolynomialPqx;
use super::errors::ProofVerifyError;
use super::math::Math;
use super::r1csinstance::R1CSInstance;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::sumcheck::SumcheckInstanceProof;
use super::timer::Timer;
use super::transcript::{AppendToTranscript, ProofTranscript};
use std::cmp::min;
use std::iter::zip;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

const ZERO: Scalar = Scalar::zero();
const ONE: Scalar = Scalar::one();

#[derive(Serialize, Deserialize, Debug)]
pub struct R1CSProof {
  sc_proof_phase1: SumcheckInstanceProof,
  sc_proof_phase2: SumcheckInstanceProof,
  claims_phase2: (Scalar, Scalar, Scalar),
  // Need to commit vars for short and long witnesses separately
  // The long version must exist, the short version might not
  eval_vars_at_ry_list: Vec<Vec<Scalar>>,
  eval_vars_at_ry: Scalar,
  proof_eval_vars_at_ry_list: Vec<PolyEvalProof>,
}

#[derive(Clone, Serialize)]
pub struct R1CSSumcheckGens {
  gens_1: MultiCommitGens,
  gens_3: MultiCommitGens,
  gens_4: MultiCommitGens,
}

// TODO: fix passing gens_1_ref
impl R1CSSumcheckGens {
  pub fn new(label: &'static [u8], gens_1_ref: &MultiCommitGens) -> Self {
    let gens_1 = gens_1_ref.clone();
    let gens_3 = MultiCommitGens::new(3, label);
    let gens_4 = MultiCommitGens::new(4, label);

    R1CSSumcheckGens {
      gens_1,
      gens_3,
      gens_4,
    }
  }
}

#[derive(Clone, Serialize)]
pub struct R1CSGens {
  pub gens_sc: R1CSSumcheckGens,
  pub gens_pc: PolyCommitmentGens,
}

impl R1CSGens {
  pub fn new(label: &'static [u8], _num_cons: usize, num_vars: usize) -> Self {
    let num_poly_vars = num_vars.log_2();
    let gens_pc = PolyCommitmentGens::new(num_poly_vars, label);
    let gens_sc = R1CSSumcheckGens::new(label, &gens_pc.gens.gens_1);
    R1CSGens { gens_sc, gens_pc }
  }
}

impl R1CSProof {
  fn prove_phase_one(
    num_rounds: usize,
    num_rounds_x_max: usize,
    num_rounds_q_max: usize,
    num_rounds_p: usize,
    num_proofs: &Vec<usize>,
    num_cons: &Vec<usize>,
    evals_tau_p: &mut DensePolynomial,
    evals_tau_q: &mut DensePolynomial,
    evals_tau_x: &mut DensePolynomial,
    evals_Az: &mut DensePolynomialPqx,
    evals_Bz: &mut DensePolynomialPqx,
    evals_Cz: &mut DensePolynomialPqx,
    transcript: &mut Transcript,
  ) -> (SumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>) {
    let comb_func = |poly_A_comp: &Scalar,
                     poly_B_comp: &Scalar,
                     poly_C_comp: &Scalar,
                     poly_D_comp: &Scalar|
     -> Scalar { poly_A_comp * (poly_B_comp * poly_C_comp - poly_D_comp) };

    let (sc_proof_phase_one, r, claims) =
      SumcheckInstanceProof::prove_cubic_with_additive_term_disjoint_rounds(
        &ZERO, // claim is zero
        num_rounds,
        num_rounds_x_max,
        num_rounds_q_max,
        num_rounds_p,
        num_proofs.clone(),
        num_cons.clone(),
        evals_tau_p,
        evals_tau_q,
        evals_tau_x,
        evals_Az,
        evals_Bz,
        evals_Cz,
        comb_func,
        transcript,
      );

    (sc_proof_phase_one, r, claims)
  }

  fn prove_phase_two(
    num_rounds: usize,
    num_rounds_y_max: usize,
    num_rounds_w: usize,
    num_rounds_p: usize,
    single_inst: bool,
    num_witness_secs: usize,
    num_inputs: Vec<Vec<usize>>,
    claim: &Scalar,
    evals_eq: &mut DensePolynomial,
    evals_ABC: &mut DensePolynomialPqx,
    evals_z: &mut DensePolynomialPqx,
    transcript: &mut Transcript,
  ) -> (SumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>, Vec<Vec<Scalar>>) {
    let comb_func =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar, poly_C_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp * poly_C_comp };
    let (sc_proof_phase_two, r, claims, claimed_vars_at_ry) = SumcheckInstanceProof::prove_cubic_disjoint_rounds(
      claim,
      num_rounds,
      num_rounds_y_max,
      num_rounds_w,
      num_rounds_p,
      single_inst,
      num_witness_secs,
      num_inputs,
      evals_eq,
      evals_ABC,
      evals_z,
      comb_func,
      transcript,
    );

    (sc_proof_phase_two, r, claims, claimed_vars_at_ry)
  }

  fn protocol_name() -> &'static [u8] {
    b"R1CS proof"
  }

  // A generic R1CS prover that enables data-parallelism on instances
  pub fn prove(
    num_circuits: usize,
    max_num_proofs: usize,
    num_proofs: &Vec<usize>,
    // Number of inputs of the combined Z matrix
    max_num_inputs: usize,
    // WITNESS_SECS
    // How many sections does each Z vector have?
    // num_witness_secs can be between 1 - 8
    // if num_witness_secs is not a power of 2, the remaining secs are simply 0's
    // For each witness sec, record the following:
    // IS_SINGLE: does it have just one copy across all blocks?
    // IS_SHORT: does it have only one copy per block? A single witness sect must also be short
    // NUM_INPUTS: number of inputs per block
    // W_MAT: num_circuits x num_proofs x num_inputs hypermatrix for all values
    // POLY_W: one dense polynomial per circuit
    witness_secs: Vec<&ProverWitnessSecInfo>,
    // INSTANCES
    inst: &R1CSInstance,
    gens: &R1CSGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (R1CSProof, [Vec<Scalar>; 4]) {
    let timer_prove = Timer::new("R1CSProof::prove");
    transcript.append_protocol_name(R1CSProof::protocol_name());

    let num_witness_secs = witness_secs.len();

    // Assert everything is a power of 2, except num_circuits
    assert_eq!(max_num_proofs, max_num_proofs.next_power_of_two());
    for p in num_proofs {
      assert_eq!(*p, p.next_power_of_two());
      assert!(*p <= max_num_proofs);
    }
    // Construct num_inputs as P x W
    // Note: w.num_inputs[p_w] might exceed max_num_inputs, but only the first max_num_inputs entries are used
    let num_inputs: Vec<Vec<usize>> = (0..num_circuits).map(|p| witness_secs.iter().map(|w| {
      let p_w = if w.num_inputs.len() == 1 { 0 } else { p };
      min(w.num_inputs[p_w], max_num_inputs)
    }
    ).collect()).collect();
    // Number of circuits is either one or matches num_circuits
    assert!(inst.get_num_circuits() == 1 || inst.get_num_circuits() == num_circuits);
    // Assert num_witness_secs is valid
    assert!(num_witness_secs >= 1 && num_witness_secs <= 16);
    for w in &witness_secs {
      // assert size of w_mat
      assert!(w.w_mat.len() == 1 || w.w_mat.len() == num_circuits);
      for p in 0..w.w_mat.len() {
        assert!(w.w_mat[p].len() == 1 || w.w_mat[p].len() == num_proofs[p]);
        for q in 0..w.w_mat[p].len() {
          assert_eq!(w.w_mat[p][q].len(), w.num_inputs[p]);
        }
      }
    }

    // --
    // PHASE 1
    // --
    let num_cons = inst.get_num_cons();
    let block_num_cons = if inst.get_num_circuits() == 1 { vec![inst.get_inst_num_cons()[0]; num_circuits] } else { inst.get_inst_num_cons().clone() };
    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // append input to variables to create a single vector z
    let timer_tmp = Timer::new("prove_z_gen");
    let mut z_mat: Vec<Vec<Vec<Vec<Scalar>>>> = Vec::new();
    for p in 0..num_circuits {
      z_mat.push(vec![vec![Vec::new(); witness_secs.len()]; num_proofs[p]]);
      for w in 0..witness_secs.len() {
        let ws = witness_secs[w];
        let p_w = if ws.w_mat.len() == 1 { 0 } else { p };
        let num_proofs_w = if ws.is_single() { 1 } else { num_proofs[p] };
        for q in 0..num_proofs_w {
          z_mat[p][q][w] = vec![ZERO; num_inputs[p][w]];
          let q_w = if ws.w_mat[p_w].len() == 1 { 0 } else { q };
          // Only append the first num_inputs_entries of w_mat[p][q]
          for i in 0..min(ws.num_inputs[p_w], max_num_inputs) {
            z_mat[p][q][w][i] = ws.w_mat[p_w][q_w][i];
          }
        }
      }
    }
    // Construct a p * q * len(z) matrix Z and bound it to r_q
    let mut Z_poly = DensePolynomialPqx::new(
      z_mat, 
      witness_secs.iter().map(|w| w.is_single()).collect()
    );
    timer_tmp.stop();

    // derive the verifier's challenge \tau
    let timer_tmp = Timer::new("prove_vec_mult");
    let (num_rounds_p, num_rounds_q, num_rounds_x, num_rounds_w, num_rounds_y) = 
      (num_circuits.next_power_of_two().log_2(), max_num_proofs.log_2(), num_cons.log_2(), num_witness_secs.log_2(), max_num_inputs.log_2());
    let tau_p = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_x = transcript.challenge_vector(b"challenge_tau_x", num_rounds_x);

    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau_p = DensePolynomial::new(EqPolynomial::new(tau_p).evals());
    let mut poly_tau_q = DensePolynomial::new(EqPolynomial::new(tau_q).evals());
    let mut poly_tau_x = DensePolynomial::new(EqPolynomial::new(tau_x).evals());
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec_block(
        num_circuits, 
        num_proofs.clone(), 
        max_num_proofs, 
        max_num_inputs, 
        num_cons, 
        block_num_cons.clone(), 
        &Z_poly,
      );
    timer_tmp.stop();

    // Sumcheck 1: (Az * Bz - Cz) * eq(x, q, p) = 0
    let timer_tmp = Timer::new("prove_sum_check");
    let (sc_proof_phase1, rx_rev, _claims_phase1) = R1CSProof::prove_phase_one(
      num_rounds_x + num_rounds_q + num_rounds_p,
      num_rounds_x,
      num_rounds_q,
      num_rounds_p,
      &num_proofs,
      &block_num_cons,
      &mut poly_tau_p,
      &mut poly_tau_q,
      &mut poly_tau_x,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      transcript,
    );
    assert_eq!(poly_tau_p.len(), 1);
    assert_eq!(poly_tau_q.len(), 1);
    assert_eq!(poly_tau_x.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_tmp.stop();
    timer_sc_proof_phase1.stop();

    let (_tau_claim, Az_claim, Bz_claim, Cz_claim) =
      (&(poly_tau_p[0] * poly_tau_q[0] * poly_tau_x[0]), &poly_Az.index(0, 0, 0, 0), &poly_Bz.index(0, 0, 0, 0), &poly_Cz.index(0, 0, 0, 0));

    Az_claim.append_to_transcript(b"Az_claim", transcript);
    Bz_claim.append_to_transcript(b"Bz_claim", transcript);
    Cz_claim.append_to_transcript(b"Cz_claim", transcript);

    // prove the final step of sum-check #1
    // Deferred to the verifier

    // Separate the result rx into rp, rq, and rx
    let (rx_rev, rq_rev) = rx_rev.split_at(num_rounds_x);
    let (rq_rev, rp_rev) = rq_rev.split_at(num_rounds_q);
    let rx: Vec<Scalar> = rx_rev.iter().copied().rev().collect();
    let rq: Vec<Scalar> = rq_rev.iter().copied().rev().collect();
    let rp = rp_rev.iter().copied().rev().collect();

    // --
    // PHASE 2
    // --
    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A = transcript.challenge_scalar(b"challenge_Az");
    let r_B = transcript.challenge_scalar(b"challenge_Bz");
    let r_C = transcript.challenge_scalar(b"challenge_Cz");

    let claim_phase2 = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;

    let timer_tmp = Timer::new("prove_abc_gen");
    let evals_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(rx.clone()).evals();
      let (evals_A, evals_B, evals_C) =
      inst.compute_eval_table_sparse_disjoint_rounds(
        num_circuits, 
        inst.get_inst_num_cons(), 
        num_witness_secs, 
        max_num_inputs, 
        &num_inputs, 
        &evals_rx
      );

      let mut evals_ABC = Vec::new();
      for p in 0..inst.get_num_circuits() {
        evals_ABC.push(vec![Vec::new()]);
        for w in 0..num_witness_secs {
          evals_ABC[p][0].push(Vec::new());
          // If single circuit, need to find the maximum num_inputs
          let num_inputs = if inst.get_num_circuits() == 1 { 
            num_inputs.iter().map(|n| n[w]).max().unwrap()
          } else { num_inputs[p][w] };
          for i in 0..num_inputs {
            evals_ABC[p][0][w].push(r_A * evals_A[p][0][w][i] + r_B * evals_B[p][0][w][i] + r_C * evals_C[p][0][w][i]);
          }
        }
      }
      evals_ABC
    };
    let mut ABC_poly = DensePolynomialPqx::new(evals_ABC, vec![false; num_witness_secs]);
    timer_tmp.stop();

    // Bound Z_poly to r_q
    let timer_tmp = Timer::new("prove_z_bind");
    Z_poly.bound_poly_vars_rq(rq_rev);
    timer_tmp.stop();

    // An Eq function to match p with rp
    let mut eq_p_rp_poly = DensePolynomial::new(EqPolynomial::new(rp).evals());
    // Sumcheck 2: (rA + rB + rC) * Z * eq(p) = e
    let (sc_proof_phase2, ry_rev, _claims_phase2, claimed_vars_at_ry) = R1CSProof::prove_phase_two(
      num_rounds_y + num_rounds_w + num_rounds_p,
      num_rounds_y,
      num_rounds_w,
      num_rounds_p,
      inst.get_num_circuits() == 1,
      num_witness_secs,
      num_inputs.clone(),
      &claim_phase2,
      &mut eq_p_rp_poly,
      &mut ABC_poly,
      &mut Z_poly,
      transcript,
    );
    timer_sc_proof_phase2.stop();

    // Separate ry into rp, rw, and ry
    let (ry_rev, rw_rev) = ry_rev.split_at(num_rounds_y);
    let (rw_rev, rp_rev) = rw_rev.split_at(num_rounds_w);
    let rp: Vec<Scalar> = rp_rev.iter().copied().rev().collect();
    let rw: Vec<Scalar> = rw_rev.iter().copied().rev().collect();
    let ry: Vec<Scalar> = ry_rev.iter().copied().rev().collect();

    assert_eq!(Z_poly.len(), 1);
    assert_eq!(ABC_poly.len(), 1);

    // --
    // POLY COMMIT
    // --
    // Commit each witness by circuit
    let timer_polyeval = Timer::new("polyeval");

    // For every possible wit_sec.num_inputs, compute ry_factor = prodX(1 - ryX)...
    let mut rq_factors = vec![ONE; num_rounds_q + 1];
    for i in 0..num_rounds_q {
      rq_factors[i + 1] = rq_factors[i] * (ONE - rq[i]);
    }
    let mut ry_factors = vec![ONE; num_rounds_y + 1];
    for i in 0..num_rounds_y {
      ry_factors[i + 1] = ry_factors[i] * (ONE - ry[i]);
    }

    let mut poly_list = Vec::new();
    let mut num_proofs_list = Vec::new();
    let mut num_inputs_list = Vec::new();
    // List of all evaluations
    let mut Zr_list = Vec::new();
    // Obtain list of evaluations separated by witness_secs
    // Note: eval_vars_at_ry_list and raw_eval_vars_at_ry_list are W * P but claimed_vars_at_ry_list is P * W, and
    // raw_eval_vars_at_ry_list does not multiply rq_factor and ry_factor
    let mut eval_vars_at_ry_list = vec![Vec::new(); num_witness_secs];
    let mut raw_eval_vars_at_ry_list = vec![Vec::new(); num_witness_secs];
    for i in 0..num_witness_secs {
      let w = witness_secs[i];
      let wit_sec_num_circuits = w.w_mat.len();
      for p in 0..wit_sec_num_circuits {
        if w.num_inputs[p] > 1 {
          poly_list.push(&w.poly_w[p]);
          num_proofs_list.push(w.w_mat[p].len());
          num_inputs_list.push(w.num_inputs[p]);
          // Find out the extra q and y padding to remove in raw_eval_vars_at_ry_list
          let rq_pad_inv = rq_factors[num_rounds_q - num_proofs[p].log_2()].invert().unwrap();
          let ry_pad_inv = if w.num_inputs[p] >= max_num_inputs { ONE } else { ry_factors[num_rounds_y - w.num_inputs[p].log_2()].invert().unwrap() };
          eval_vars_at_ry_list[i].push(claimed_vars_at_ry[p][i] * rq_pad_inv); // I don't know why need to divide by rq and later multiply it back, but it doesn't work without this
          let claimed_vars_at_ry_no_pad = claimed_vars_at_ry[p][i] * rq_pad_inv * ry_pad_inv;
          Zr_list.push(claimed_vars_at_ry_no_pad);
          raw_eval_vars_at_ry_list[i].push(claimed_vars_at_ry_no_pad);
        } else {
          eval_vars_at_ry_list[i].push(ZERO);
          raw_eval_vars_at_ry_list[i].push(ZERO);
        }
      }
    }

    let proof_eval_vars_at_ry_list = PolyEvalProof::prove_batched_polys_disjoint_rounds(
      &poly_list,
      &num_proofs_list,
      &num_inputs_list,
      None,
      &rq,
      &ry,
      &Zr_list,
      None,
      &gens.gens_pc,
      transcript,
      random_tape,
    );

    // Bind the resulting witness list to rp
    // poly_vars stores the result of each witness matrix bounded to (rq_short ++ ry)
    // but we want to bound them to (rq ++ ry)
    // So we need to multiply each entry by (1 - rq0)(1 - rq1)
    let mut eval_vars_comb_list = Vec::new();
    for p in 0..num_circuits {
      let wit_sec_p = |i: usize| if witness_secs[i].w_mat.len() == 1 { 0 } else { p };
      let e = |i: usize| eval_vars_at_ry_list[i][wit_sec_p(i)];
      let prefix_list = match num_witness_secs.next_power_of_two() {
        1 => { vec![ONE] }
        2 => { vec![(ONE - rw[0]), rw[0]] }
        4 => { vec![(ONE - rw[0]) * (ONE - rw[1]), (ONE - rw[0]) * rw[1], rw[0] * (ONE - rw[1]), rw[0] * rw[1]] }
        8 => { vec![
          (ONE - rw[0]) * (ONE - rw[1]) * (ONE - rw[2]),
          (ONE - rw[0]) * (ONE - rw[1]) * rw[2],
          (ONE - rw[0]) * rw[1] * (ONE - rw[2]),
          (ONE - rw[0]) * rw[1] * rw[2],
          rw[0] * (ONE - rw[1]) * (ONE - rw[2]),
          rw[0] * (ONE - rw[1]) * rw[2],
          rw[0] * rw[1] * (ONE - rw[2]),
          rw[0] * rw[1] * rw[2],
        ] }
        _ => { panic!("Unsupported num_witness_secs: {}", num_witness_secs); }
      };
      let mut eval_vars_comb = (0..num_witness_secs).fold(ZERO, |s, i| s + prefix_list[i] * e(i));
      eval_vars_comb *= rq_factors[num_rounds_q - num_proofs[p].log_2()];
      eval_vars_comb_list.push(eval_vars_comb);
    }
    timer_polyeval.stop();

    let poly_vars = DensePolynomial::new(eval_vars_comb_list);
    let eval_vars_at_ry = poly_vars.evaluate(&rp);
    assert_eq!(Z_poly.index(0, 0, 0, 0), eval_vars_at_ry);
    // prove the final step of sum-check #2
    // Deferred to verifier
    timer_prove.stop();

    (
      R1CSProof {
        sc_proof_phase1,
        claims_phase2: (*Az_claim, *Bz_claim, *Cz_claim),
        sc_proof_phase2,
        eval_vars_at_ry_list: raw_eval_vars_at_ry_list, // Note: NOT eval_vars_at_ry_list!
        eval_vars_at_ry,
        proof_eval_vars_at_ry_list,
      },
      [rp, rq, rx, [rw, ry].concat()]
    )
  }

  pub fn verify(
    &self,
    num_circuits: usize,
    max_num_proofs: usize,
    num_proofs: &Vec<usize>,
    max_num_inputs: usize,

    // NUM_WITNESS_SECS
    // How many sections does each Z vector have?
    // num_witness_secs can be between 1 - 8
    // if num_witness_secs is not a power of 2, the remaining secs are simply 0's
    // For each witness sec, record the following:
    // IS_SINGLE: does it have just one copy across all blocks?
    // IS_SHORT: does it have only one copy per block? A single witness sect must also be short
    // NUM_INPUTS: number of inputs per block
    // W_MAT: num_circuits x num_proofs x num_inputs hypermatrix for all values
    // COMM_W: one commitment per circuit
    witness_secs: Vec<&VerifierWitnessSecInfo>,

    num_cons: usize,
    gens: &R1CSGens,
    evals: &[Scalar; 3],
    transcript: &mut Transcript,
  ) -> Result<[Vec<Scalar>; 4], ProofVerifyError> {
    transcript.append_protocol_name(R1CSProof::protocol_name());

    let num_witness_secs = witness_secs.len();

    // Assert num_witness_secs is valid
    assert!(num_witness_secs >= 1 && num_witness_secs <= 16);

    let (num_rounds_p, num_rounds_q, num_rounds_x, num_rounds_w, num_rounds_y) = 
      (num_circuits.next_power_of_two().log_2(), max_num_proofs.log_2(), num_cons.log_2(), num_witness_secs.log_2(), max_num_inputs.log_2());

    // derive the verifier's challenge tau
    let tau_p = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_x = transcript.challenge_vector(b"challenge_tau_x", num_rounds_x);

    // verify the first sum-check instance
    let (claim_post_phase_1, rx_rev) =
      self
        .sc_proof_phase1
        .verify(ZERO, num_rounds_x + num_rounds_q + num_rounds_p, 3, transcript)?;

    // Separate the result rx into rp_round1, rq, and rx
    let (rx_rev, rq_rev) = rx_rev.split_at(num_rounds_x);
    let (rq_rev, rp_rev) = rq_rev.split_at(num_rounds_q);
    let rx: Vec<Scalar> = rx_rev.iter().copied().rev().collect();
    let rq: Vec<Scalar> = rq_rev.iter().copied().rev().collect();
    let rp_round1: Vec<Scalar> = rp_rev.iter().copied().rev().collect();

    // taus_bound_rx is really taus_bound_rx_rq_rp
    let taus_bound_rp: Scalar = (0..rp_round1.len())
      .map(|i| rp_round1[i] * tau_p[i] + (ONE - rp_round1[i]) * (ONE - tau_p[i]))
      .product();
    let taus_bound_rq: Scalar = (0..rq.len())
      .map(|i| rq[i] * tau_q[i] + (ONE - rq[i]) * (ONE - tau_q[i]))
      .product();
    let taus_bound_rx: Scalar = (0..rx.len())
      .map(|i| rx[i] * tau_x[i] + (ONE - rx[i]) * (ONE - tau_x[i]))
      .product();
    let taus_bound_rx = taus_bound_rp * taus_bound_rq * taus_bound_rx;

    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (Az_claim, Bz_claim, Cz_claim) = self.claims_phase2;
    Az_claim.append_to_transcript(b"Az_claim", transcript);
    Bz_claim.append_to_transcript(b"Bz_claim", transcript);
    Cz_claim.append_to_transcript(b"Cz_claim", transcript);

    assert_eq!(taus_bound_rx * (Az_claim * Bz_claim - Cz_claim), claim_post_phase_1);

    // derive three public challenges and then derive a joint claim
    let r_A = transcript.challenge_scalar(b"challenge_Az");
    let r_B = transcript.challenge_scalar(b"challenge_Bz");
    let r_C = transcript.challenge_scalar(b"challenge_Cz");

    // r_A * comm_Az_claim + r_B * comm_Bz_claim + r_C * comm_Cz_claim;
    let claim_phase2 = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;

    // verify the joint claim with a sum-check protocol
    let (claim_post_phase_2, ry_rev) =
      self
        .sc_proof_phase2
        .verify(claim_phase2, num_rounds_y + num_rounds_w + num_rounds_p, 3, transcript)?;

    // Separate ry into rp, rw, and ry
    let (ry_rev, rw_rev) = ry_rev.split_at(num_rounds_y);
    let (rw_rev, rp_rev) = rw_rev.split_at(num_rounds_w);
    let rp: Vec<Scalar> = rp_rev.iter().copied().rev().collect();
    let rw: Vec<Scalar> = rw_rev.iter().copied().rev().collect();
    let ry: Vec<Scalar> = ry_rev.iter().copied().rev().collect();

    // An Eq function to match p with rp
    let p_rp_poly_bound_ry: Scalar = (0..rp.len())
      .map(|i| rp[i] * rp_round1[i] + (ONE - rp[i]) * (ONE - rp_round1[i]))
      .product();

    // verify Z(rp, rq, ry) proof against the initial commitment
    // First by witness & by circuit on ry
    // For every possible wit_sec.num_inputs, compute ry_factor = prodX(1 - ryX)...
    // If there are 2 witness secs, then ry_factors[0] = 1, ry_factors[1] = 1, ry_factors[2] = 1 - ry1, ry_factors[3] = (1 - ry1)(1 - ry2), etc.
    let mut ry_factors = vec![ONE; num_rounds_y + 1];
    for i in 0..num_rounds_y {
      ry_factors[i + 1] = (ry_factors[i]) * (ONE - ry[i]);
    }

    // POLY COMMIT
    let timer_commit_opening = Timer::new("verify_sc_commitment_opening");
    let mut comm_list = Vec::new();
    let mut num_proofs_list = Vec::new();
    let mut num_inputs_list = Vec::new();
    let mut eval_Zr_list = Vec::new();
    for i in 0..num_witness_secs {
      let w = witness_secs[i];
      let wit_sec_num_circuits = w.num_proofs.len();
      for p in 0..wit_sec_num_circuits {
        if w.num_inputs[p] > 1 {
          comm_list.push(&w.comm_w[p]);
          num_proofs_list.push(w.num_proofs[p]);
          num_inputs_list.push(w.num_inputs[p]);
          eval_Zr_list.push(self.eval_vars_at_ry_list[i][p]);
        } else {
          assert_eq!(self.eval_vars_at_ry_list[i][p], ZERO);
        }
      }
    }
    PolyEvalProof::verify_plain_batched_polys_disjoint_rounds(
      &self.proof_eval_vars_at_ry_list,
      &num_proofs_list,
      &num_inputs_list,
      &gens.gens_pc,
      transcript,
      &rq,
      &ry,
      &eval_Zr_list,
      &comm_list,
    )?;

    // Then on rp
    let mut expected_eval_vars_list = Vec::new();
    for p in 0..num_circuits {
      let wit_sec_p = |i: usize| if witness_secs[i].num_proofs.len() == 1 { 0 } else { p };
      let c = |i: usize| 
        if witness_secs[i].num_inputs[wit_sec_p(i)] >= max_num_inputs {
          self.eval_vars_at_ry_list[i][wit_sec_p(i)]
        } else {
          self.eval_vars_at_ry_list[i][wit_sec_p(i)] * ry_factors[num_rounds_y - witness_secs[i].num_inputs[wit_sec_p(i)].log_2()]
        };
      let prefix_list = match num_witness_secs.next_power_of_two() {
        1 => { vec![ONE] }
        2 => { vec![(ONE - rw[0]), rw[0]] }
        4 => { vec![(ONE - rw[0]) * (ONE - rw[1]), (ONE - rw[0]) * rw[1], rw[0] * (ONE - rw[1]), rw[0] * rw[1]] }
        8 => { vec![
          (ONE - rw[0]) * (ONE - rw[1]) * (ONE - rw[2]),
          (ONE - rw[0]) * (ONE - rw[1]) * rw[2],
          (ONE - rw[0]) * rw[1] * (ONE - rw[2]),
          (ONE - rw[0]) * rw[1] * rw[2],
          rw[0] * (ONE - rw[1]) * (ONE - rw[2]),
          rw[0] * (ONE - rw[1]) * rw[2],
          rw[0] * rw[1] * (ONE - rw[2]),
          rw[0] * rw[1] * rw[2],
        ] }
        _ => { panic!("Unsupported num_witness_secs: {}", num_witness_secs); }
      };
      let mut eval_vars_comb = (1..num_witness_secs).fold(prefix_list[0] * c(0), |s, i| s + prefix_list[i] * c(i));
      for q in 0..(num_rounds_q - num_proofs[p].log_2()) {
        eval_vars_comb *= ONE - rq[q];
      }
      expected_eval_vars_list.push(eval_vars_comb);
    }

    let EQ_p = &EqPolynomial::new(rp.clone()).evals()[..num_circuits];
    let expected_eval_vars_at_ry = zip(EQ_p, expected_eval_vars_list).fold(ZERO, |s, (a, b)| s + a * b);
  
    assert_eq!(expected_eval_vars_at_ry, self.eval_vars_at_ry);
    timer_commit_opening.stop();

    // compute commitment to eval_Z_at_ry = (ONE - ry[0]) * self.eval_vars_at_ry + ry[0] * poly_input_eval
    let eval_Z_at_ry = &self.eval_vars_at_ry;

    // perform the final check in the second sum-check protocol
    let [eval_A_r, eval_B_r, eval_C_r] = evals;
    let expected_claim_post_phase2 =
      (r_A * eval_A_r + r_B * eval_B_r + r_C * eval_C_r) * eval_Z_at_ry * p_rp_poly_bound_ry;

    // verify proof that expected_claim_post_phase2 == claim_post_phase2
    assert_eq!(claim_post_phase_2, expected_claim_post_phase2);

    Ok([rp, rq, rx, [rw, ry].concat()])
  }

}