#![allow(non_snake_case)]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(clippy::assertions_on_result_states)]

// TODO: Can we allow split in R1CSGens?
// TODO: Can we parallelize the proofs?
// TODO: Problem when there is only one block & one execution

extern crate byteorder;
extern crate core;
extern crate curve25519_dalek;
extern crate digest;
extern crate merlin;
extern crate rand;
extern crate sha3;

#[cfg(feature = "multicore")]
extern crate rayon;

mod commitments;
mod dense_mlpoly;
mod custom_dense_mlpoly;
mod errors;
mod group;
/// R1CS instance used by libspartan
pub mod instance;
mod math;
mod nizk;
mod product_tree;
mod r1csinstance;
mod r1csproof;
mod random;
/// Field type used by libspartan
pub mod scalar;
mod sparse_mlpoly;
mod sumcheck;
mod timer;
mod transcript;
mod unipoly;

use std::{cmp::max, fs::File, io::Write};

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use instance::Instance;
use dense_mlpoly::{DensePolynomial, PolyCommitment, PolyEvalProof};
use errors::{ProofVerifyError, R1CSError};
use itertools::Itertools;
use math::Math;
use merlin::Transcript;
use r1csinstance::{
  R1CSCommitment, R1CSCommitmentGens, R1CSDecommitment, R1CSEvalProof, R1CSInstance,
};
use r1csproof::{R1CSGens, R1CSProof};
use random::RandomTape;
use scalar::Scalar;
use serde::{Deserialize, Serialize};
use timer::Timer;
use transcript::{AppendToTranscript, ProofTranscript};

use crate::commitments::Commitments;

const ZERO: Scalar = Scalar::zero();
const ONE: Scalar = Scalar::one();

const INIT_PHY_MEM_WIDTH: usize = 8;
const INIT_VIR_MEM_WIDTH: usize = 8;
const PHY_MEM_WIDTH: usize = 8;
const VIR_MEM_WIDTH: usize = 8;
const W3_WIDTH: usize = 8;

/// `ComputationCommitment` holds a public preprocessed NP statement (e.g., R1CS)
#[derive(Clone, Serialize)]
pub struct ComputationCommitment {
  comm: R1CSCommitment,
}

/// `ComputationDecommitment` holds information to decommit `ComputationCommitment`
pub struct ComputationDecommitment {
  decomm: R1CSDecommitment,
}

/// `Assignment` holds an assignment of values to either the inputs or variables in an `Instance`
#[derive(Clone, Serialize, Deserialize)]
pub struct Assignment {
  /// Entries of an assignment
  pub assignment: Vec<Scalar>,
}

impl Assignment {
  /// Constructs a new `Assignment` from a vector
  pub fn new(assignment: &[[u8; 32]]) -> Result<Assignment, R1CSError> {
    let bytes_to_scalar = |vec: &[[u8; 32]]| -> Result<Vec<Scalar>, R1CSError> {
      let mut vec_scalar: Vec<Scalar> = Vec::new();
      for v in vec {
        let val = Scalar::from_bytes(v);
        if val.is_some().unwrap_u8() == 1 {
          vec_scalar.push(val.unwrap());
        } else {
          return Err(R1CSError::InvalidScalar);
        }
      }
      Ok(vec_scalar)
    };
    let assignment_scalar = bytes_to_scalar(assignment);

    // check for any parsing errors
    if assignment_scalar.is_err() {
      return Err(R1CSError::InvalidScalar);
    }

    Ok(Assignment {
      assignment: assignment_scalar.unwrap(),
    })
  }

  /// Write the assignment into a file
  pub fn write(&self, mut f: &File) -> std::io::Result<()> {
    for assg in &self.assignment {
        write_bytes(&mut f, &assg.to_bytes())?;
    }
    Ok(())
  }
}

fn write_bytes(mut f: &File, bytes: &[u8; 32]) -> std::io::Result<()> {
  // Disregard the trailing zeros
  let mut size = 32;
  while size > 0 && bytes[size - 1] == 0 {
      size -= 1;
  }
  for i in 0..size {
      write!(&mut f, "{} ", bytes[i])?;
  }
  writeln!(&mut f, "")?;
  Ok(())
}


/// `VarsAssignment` holds an assignment of values to variables in an `Instance`
pub type VarsAssignment = Assignment;

/// `InputsAssignment` holds an assignment of values to inputs in an `Instance`
pub type InputsAssignment = Assignment;

/// `MemsAssignment` holds an assignment of values to (addr, val) pairs in an `Instance`
pub type MemsAssignment = Assignment;

/// `SNARKGens` holds public parameters for producing and verifying proofs with the Spartan SNARK
#[derive(Serialize)]
pub struct SNARKGens {
  /// Generator for witness commitment
  pub gens_r1cs_sat: R1CSGens,
  gens_r1cs_eval: R1CSCommitmentGens,
}

impl SNARKGens {
  /// Constructs a new `SNARKGens` given the size of the R1CS statement
  /// `num_nz_entries` specifies the maximum number of non-zero entries in any of the three R1CS matrices
  pub fn new(num_cons: usize, num_vars: usize, num_circuits: usize, num_nz_entries: usize) -> Self {
    let num_vars_padded = num_vars.next_power_of_two();

    let num_circuits_padded: usize = num_circuits.next_power_of_two();
    let gens_r1cs_sat = R1CSGens::new(b"gens_r1cs_sat", num_cons, num_vars_padded);
    let gens_r1cs_eval = R1CSCommitmentGens::new(
      b"gens_r1cs_eval",
      num_circuits_padded,
      num_cons,
      num_vars_padded,
      num_nz_entries,
    );
    SNARKGens {
      gens_r1cs_sat,
      gens_r1cs_eval,
    }
  }
}

// IOProofs contains a series of proofs that the committed values match the input and output of the program
#[derive(Serialize, Deserialize, Debug)]
struct IOProofs {
  // The prover needs to prove:
  // 1. Input and output block are both valid
  // 2. Block number of the input and output block are correct
  // 3. Input and outputs are correct
  // 4. The constant value of the input is 1
  proofs: Vec<PolyEvalProof>,
}

impl IOProofs {
  // Given the polynomial in execution order, generate all proofs
  fn prove(
    exec_poly_inputs: &DensePolynomial,
    
    num_ios: usize,
    num_inputs_unpadded: usize,
    num_proofs: usize,
    input_block_num: Scalar,
    output_block_num: Scalar,
    
    input_liveness: &Vec<bool>,
    input_offset: usize,
    output_offset: usize,
    input: Vec<Scalar>,
    output: Scalar,
    output_exec_num: usize,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape
  ) -> IOProofs {
    let r_len = (num_proofs * num_ios).log_2();
    let to_bin_array = |x: usize| (0..r_len).rev().map(|n| (x >> n) & 1).map(|i| Scalar::from(i as u64)).collect::<Vec::<Scalar>>();

    // input indices are 6(%SP) ++ 5(%AS) ++ [2 + input_offset..](others)
    // Filter out all dead inputs
    let mut input_indices: Vec<usize> = (0..input_liveness.len() - 2).map(|i| 2 + input_offset + i).collect();
    if input_liveness[1] {
      // %AS is alive, add entry 5
      input_indices.insert(0, 5);
    }
    if input_liveness[0] {
      // %SP is alive, add entry 6
      input_indices.insert(0, 6);
    }
    assert_eq!(input_liveness.len(), input.len());
    let mut live_input = Vec::new();
    for i in 0..input_liveness.len() {
      if input_liveness[i] {
        live_input.push(input[i].clone());
      }
    }
    input_indices = input_indices[..live_input.len()].to_vec();

    // batch prove all proofs
    let proofs = PolyEvalProof::prove_batched_points(
      exec_poly_inputs,
      None,
      [
        vec![
          0, // input valid
          output_exec_num * num_ios, // output valid
          2, // input block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1), // output block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1) + output_offset - 1, // output correctness
        ], 
        input_indices // input correctness
      ].concat().iter().map(|i| to_bin_array(*i)).collect(), 
      vec![
        vec![ONE, ONE, input_block_num, output_block_num, output],
        live_input
      ].concat(),
      None,
      &vars_gens.gens_pc,
      transcript,
      random_tape,
    );
    IOProofs {
      proofs,
    }
  }

  fn verify(
    &self,
    comm_poly_inputs: &PolyCommitment,
    num_ios: usize,
    num_inputs_unpadded: usize,
    num_proofs: usize,
    input_block_num: Scalar,
    output_block_num: Scalar,

    input_liveness: &Vec<bool>,
    input_offset: usize,
    output_offset: usize,
    input: Vec<Scalar>,
    output: Scalar,
    output_exec_num: usize,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let r_len = (num_proofs * num_ios).log_2();
    let to_bin_array = |x: usize| (0..r_len).rev().map(|n| (x >> n) & 1).map(|i| Scalar::from(i as u64)).collect::<Vec::<Scalar>>();

    // input indices are 6(%SP) ++ 5(%AS) ++ [2 + input_offset..](others)
    // Filter out all dead inputs
    let mut input_indices: Vec<usize> = (0..input_liveness.len() - 2).map(|i| 2 + input_offset + i).collect();
    if input_liveness[1] {
      // %AS is alive, add entry 5
      input_indices.insert(0, 5);
    }
    if input_liveness[0] {
      // %SP is alive, add entry 6
      input_indices.insert(0, 6);
    }
    assert_eq!(input_liveness.len(), input.len());
    let mut live_input = Vec::new();
    for i in 0..input_liveness.len() {
      if input_liveness[i] {
        live_input.push(input[i].clone());
      }
    }
    input_indices = input_indices[..live_input.len()].to_vec();

    // batch verify all proofs
    let _ = PolyEvalProof::verify_plain_batched_points(
      &self.proofs,
      &vars_gens.gens_pc,
      transcript,
      [
        vec![
          0, // input valid
          output_exec_num * num_ios, // output valid
          2, // input block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1), // output block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1) + output_offset - 1, // output correctness
        ], 
        input_indices // input correctness
      ].concat().iter().map(|i| to_bin_array(*i)).collect(), 
      vec![
        vec![ONE, ONE, input_block_num, output_block_num, output],
        live_input
      ].concat(),
      comm_poly_inputs,
    )?;

    Ok(())
  }
}

// ShiftProofs contains a series of proofs and openings that a list of polynomials / commitments are indeed shifts of another list of polynomials
// We do so by treating both polynomials as univariate and evaluate on a single point C
// Finally, show shifted(C) = orig(C) * C^(shift_size) + rc * openings, where rc * openings are the first few entries of the original poly dot product with the power series of C
#[derive(Serialize, Deserialize, Debug)]
struct ShiftProofs {
  proof: PolyEvalProof,
  C_orig_evals: Vec<CompressedRistretto>,
  C_shifted_evals: Vec<CompressedRistretto>,
  openings: Vec<Vec<CompressedRistretto>>
}

impl ShiftProofs {
  fn prove(
    orig_polys: Vec<&DensePolynomial>,
    shifted_polys: Vec<&DensePolynomial>,
    // For each orig_poly, how many entries at the front of proof 0 are non-zero?
    header_len_list: Vec<usize>,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape
  ) -> ShiftProofs {
    // Assert that all polynomials are of the same size
    let num_circuits = orig_polys.len();
    assert_eq!(num_circuits, shifted_polys.len());
    let max_poly_size = orig_polys.iter().fold(0, |m, p| if p.len() > m { p.len() } else { m });
    let max_poly_size = shifted_polys.iter().fold(max_poly_size, |m, p| if p.len() > m { p.len() } else { m });
    // Open entry 0..header_len_list[p] - 1
    let mut openings = vec![Vec::new(); num_circuits];
    for p in 0..num_circuits {
      for i in 0..header_len_list[p] {
        let entry = orig_polys[p][i].commit(&ZERO, &vars_gens.gens_pc.gens.gens_1).compress();
        entry.append_to_transcript(b"shift_header_entry", transcript);
        openings[p].push(entry);
      }
    }
    let c = transcript.challenge_scalar(b"challenge_c");
    let mut rc = Vec::new();
    let mut next_c = ONE;
    for _ in 0..max_poly_size {
      rc.push(next_c);
      next_c *= c;
    }
    let mut orig_evals = Vec::new();
    let mut shifted_evals = Vec::new();
    let mut C_orig_evals = Vec::new();
    let mut C_shifted_evals = Vec::new();
    for p in 0..num_circuits {
      let orig_poly = orig_polys[p];
      let shifted_poly = shifted_polys[p];
      let orig_eval = (0..orig_poly.len()).fold(ZERO, |a, b| a + orig_poly[b] * rc[b]);
      let shifted_eval = (0..shifted_poly.len()).fold(ZERO, |a, b| a + shifted_poly[b] * rc[b]);
      orig_evals.push(orig_eval);
      shifted_evals.push(shifted_eval);
      C_orig_evals.push(orig_eval.commit(&ZERO, &vars_gens.gens_pc.gens.gens_1).compress());
      C_shifted_evals.push(shifted_eval.commit(&ZERO, &vars_gens.gens_pc.gens.gens_1).compress());
    }
    let (addr_phy_mems_shift_proof, _eval) = PolyEvalProof::prove_uni_batched_polys(
      &[orig_polys, shifted_polys].concat(),
      &c,
      &[orig_evals, shifted_evals].concat(),
      &vars_gens.gens_pc,
      transcript,
      random_tape,
    );

    ShiftProofs {
      proof: addr_phy_mems_shift_proof,
      C_orig_evals,
      C_shifted_evals,
      openings
    }
  }

  fn verify(
    &self,
    orig_comms: Vec<&PolyCommitment>,
    shifted_comms: Vec<&PolyCommitment>,
    poly_size_list: Vec<usize>,
    shift_size_list: Vec<usize>,
    // For each orig_poly, how many entries at the front of proof 0 are non-zero?
    header_len_list: Vec<usize>,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let num_circuits = orig_comms.len();
    // Open entry 0..header_len_list[p] - 1
    for p in 0..num_circuits {
      for i in 0..header_len_list[p] {
        self.openings[p][i].append_to_transcript(b"shift_header_entry", transcript);
      }
    }
    let max_shift_size = shift_size_list.iter().fold(0, |m, i| if *i > m { *i } else { m });
    let c = transcript.challenge_scalar(b"challenge_c");
    let mut rc = Vec::new();
    let mut next_c = ONE;
    for _ in 0..max_shift_size + 1 {
      rc.push(next_c);
      next_c *= c;
    }
    let C_evals_orig_decompressed: Vec<RistrettoPoint> = self.C_orig_evals.iter().map(|i| i.decompress().unwrap()).collect();
    let C_evals_shifted_decompressed: Vec<RistrettoPoint> = self.C_shifted_evals.iter().map(|i| i.decompress().unwrap()).collect();
    // shifted(C) = orig(C) * C^(shift_size) + rc * openings
    for p in 0..num_circuits {
      let orig = C_evals_orig_decompressed[p];
      let shifted = C_evals_shifted_decompressed[p];
      let reverse_shifted = (0..header_len_list[p]).fold(shifted * rc[shift_size_list[p]], |s, i| s + rc[i] * self.openings[p][i].decompress().unwrap());
      assert_eq!(orig, reverse_shifted);
    }
    // Proof of opening
    self.proof.verify_uni_batched_polys(
      &vars_gens.gens_pc,
      transcript,
      &c,
      &[C_evals_orig_decompressed, C_evals_shifted_decompressed].concat(),
      &vec![orig_comms, shifted_comms].concat(),
      [poly_size_list.clone(), poly_size_list].concat(),
    )?;
    Ok(())
  }
}

// Information regarding one witness sec
#[derive(Clone)]
struct ProverWitnessSecInfo {
  // Number of inputs per block
  num_inputs: Vec<usize>,
  // num_circuits x num_proofs x num_inputs hypermatrix for all values
  w_mat: Vec<Vec<Vec<Scalar>>>,
  // One dense polynomial per circuit
  poly_w: Vec<DensePolynomial>,
}

impl ProverWitnessSecInfo {
  fn new(w_mat: Vec<Vec<Vec<Scalar>>>, poly_w: Vec<DensePolynomial>) -> ProverWitnessSecInfo {
    ProverWitnessSecInfo {
      num_inputs: w_mat.iter().map(|i| i[0].len()).collect(),
      w_mat,
      poly_w,
    }
  }

  // Whether the wit sec is the same for all circuits and all proofs
  fn is_single(&self) -> bool {
    return self.w_mat.len() == 1 && self.w_mat[0].len() == 1;
  }

  // Empty ProverWitnessSecInfo
  fn dummy() -> ProverWitnessSecInfo {
    ProverWitnessSecInfo {
      num_inputs: vec![],
      w_mat: Vec::new(),
      poly_w: Vec::new(),
    }
  }

  // Zero ProverWitnessSecInfo
  fn pad() -> ProverWitnessSecInfo {
    ProverWitnessSecInfo {
      num_inputs: vec![1],
      w_mat: vec![vec![vec![ZERO]]],
      poly_w: vec![DensePolynomial::new(vec![ZERO])],
    }
  }

  // Concatenate the components in the given order to a new prover witness sec
  fn concat(components: Vec<&ProverWitnessSecInfo>) -> ProverWitnessSecInfo {
    let mut num_inputs = Vec::new();
    let mut w_mat = Vec::new();
    let mut poly_w = Vec::new();

    for c in components {
      num_inputs.extend(c.num_inputs.clone());
      w_mat.extend(c.w_mat.clone());
      poly_w.extend(c.poly_w.clone());
    }

    ProverWitnessSecInfo {
      num_inputs,
      w_mat,
      poly_w,
    }
  }
}

// Information regarding one witness sec
#[derive(Clone)]
struct VerifierWitnessSecInfo {
  // Number of inputs per block
  num_inputs: Vec<usize>,
  // Number of proofs per block, used by merge
  num_proofs: Vec<usize>,
  // One commitment per circuit
  comm_w: Vec<PolyCommitment>
}

impl VerifierWitnessSecInfo {
  // Unfortunately, cannot obtain all metadata from the commitment
  fn new(num_inputs: Vec<usize>, num_proofs: &Vec<usize>, comm_w: Vec<PolyCommitment>) -> VerifierWitnessSecInfo {
    assert!(comm_w.len() == 0 || (num_inputs.len() == comm_w.len() && num_proofs.len() >= comm_w.len()));
    VerifierWitnessSecInfo {
      num_inputs,
      num_proofs: num_proofs[..comm_w.len()].to_vec(),
      comm_w: comm_w,
    }
  }

  fn dummy() -> VerifierWitnessSecInfo {
    VerifierWitnessSecInfo {
      num_inputs: Vec::new(),
      num_proofs: Vec::new(),
      comm_w: Vec::new(),
    }
  }

  fn pad() -> VerifierWitnessSecInfo {
    VerifierWitnessSecInfo {
      num_inputs: vec![1],
      num_proofs: vec![1],
      comm_w: vec![PolyCommitment::empty()],
    }
  }

  // Concatenate the components in the given order to a new verifier witness sec
  fn concat(components: Vec<&VerifierWitnessSecInfo>) -> VerifierWitnessSecInfo {
    let mut num_inputs = Vec::new();
    let mut num_proofs = Vec::new();
    let mut comm_w = Vec::new();

    for c in components {
      num_inputs.extend(c.num_inputs.clone());
      num_proofs.extend(c.num_proofs.clone());
      comm_w.extend(c.comm_w.clone());
    }

    VerifierWitnessSecInfo {
      num_inputs,
      num_proofs,
      comm_w,
    }
  }
}

/// `SNARK` holds a proof produced by Spartan SNARK
#[derive(Serialize, Deserialize, Debug)]
pub struct SNARK {
  block_comm_vars_list: Vec<PolyCommitment>,
  exec_comm_inputs: Vec<PolyCommitment>,
  // comm_init_mems: Vec<PolyCommitment>, HANDLED BY THE VERIFIER
  addr_comm_phy_mems: PolyCommitment,
  addr_comm_phy_mems_shifted: PolyCommitment,
  addr_comm_vir_mems: PolyCommitment,
  addr_comm_vir_mems_shifted: PolyCommitment,
  addr_comm_ts_bits: PolyCommitment,

  perm_exec_comm_w2_list: PolyCommitment,
  perm_exec_comm_w3_list: PolyCommitment,
  perm_exec_comm_w3_shifted: PolyCommitment,

  block_comm_w2_list: Vec<PolyCommitment>,
  block_comm_w3_list: Vec<PolyCommitment>,
  block_comm_w3_list_shifted: Vec<PolyCommitment>,

  init_phy_mem_comm_w2: PolyCommitment,
  init_phy_mem_comm_w3: PolyCommitment,
  init_phy_mem_comm_w3_shifted: PolyCommitment,

  init_vir_mem_comm_w2: PolyCommitment,
  init_vir_mem_comm_w3: PolyCommitment,
  init_vir_mem_comm_w3_shifted: PolyCommitment,

  phy_mem_addr_comm_w2: PolyCommitment,
  phy_mem_addr_comm_w3: PolyCommitment,
  phy_mem_addr_comm_w3_shifted: PolyCommitment,

  vir_mem_addr_comm_w2: PolyCommitment,
  vir_mem_addr_comm_w3: PolyCommitment,
  vir_mem_addr_comm_w3_shifted: PolyCommitment,

  block_r1cs_sat_proof: R1CSProof,
  block_inst_evals_bound_rp: [Scalar; 3],
  // Only valid when using sparse commit
  block_inst_evals_list: Vec<Scalar>,
  block_r1cs_eval_proof_list: Vec<R1CSEvalProof>,

  pairwise_check_r1cs_sat_proof: R1CSProof,
  pairwise_check_inst_evals_bound_rp: [Scalar; 3],

  // Product proof for permutation
  perm_poly_eval_list: Vec<Scalar>,
  proof_eval_perm_poly_prod_list: Vec<PolyEvalProof>,

  shift_proof: ShiftProofs,
  io_proof: IOProofs,
}

impl SNARK {
  fn protocol_name() -> &'static [u8] {
    b"Spartan SNARK proof"
  }

  // Computes proof size by commitment / non-commitment
  fn compute_size(&self) -> (usize, usize) {
    let commit_size = bincode::serialize(&self.block_comm_vars_list).unwrap().len()
                           + bincode::serialize(&self.exec_comm_inputs).unwrap().len()
                           + bincode::serialize(&self.addr_comm_phy_mems).unwrap().len()
                           + bincode::serialize(&self.addr_comm_phy_mems_shifted).unwrap().len()
                           + bincode::serialize(&self.addr_comm_vir_mems).unwrap().len()
                           + bincode::serialize(&self.addr_comm_vir_mems_shifted).unwrap().len()
                           + bincode::serialize(&self.addr_comm_ts_bits).unwrap().len()
              
                           + bincode::serialize(&self.perm_exec_comm_w2_list).unwrap().len()
                           + bincode::serialize(&self.perm_exec_comm_w3_list).unwrap().len()
                           + bincode::serialize(&self.perm_exec_comm_w3_shifted).unwrap().len()
              
                           + bincode::serialize(&self.block_comm_w2_list).unwrap().len()
                           + bincode::serialize(&self.block_comm_w3_list).unwrap().len()
                           + bincode::serialize(&self.block_comm_w3_list_shifted).unwrap().len()
              
                           + bincode::serialize(&self.init_phy_mem_comm_w2).unwrap().len()
                           + bincode::serialize(&self.init_phy_mem_comm_w3).unwrap().len()
                           + bincode::serialize(&self.init_phy_mem_comm_w3_shifted).unwrap().len()
              
                           + bincode::serialize(&self.init_vir_mem_comm_w2).unwrap().len()
                           + bincode::serialize(&self.init_vir_mem_comm_w3).unwrap().len()
                           + bincode::serialize(&self.init_vir_mem_comm_w3_shifted).unwrap().len()
              
                           + bincode::serialize(&self.phy_mem_addr_comm_w2).unwrap().len()
                           + bincode::serialize(&self.phy_mem_addr_comm_w3).unwrap().len()
                           + bincode::serialize(&self.phy_mem_addr_comm_w3_shifted).unwrap().len()
              
                           + bincode::serialize(&self.vir_mem_addr_comm_w2).unwrap().len()
                           + bincode::serialize(&self.vir_mem_addr_comm_w3).unwrap().len()
                           + bincode::serialize(&self.vir_mem_addr_comm_w3_shifted).unwrap().len();
    
    let noncommit_size = bincode::serialize(&self.block_r1cs_sat_proof).unwrap().len()
                              + bincode::serialize(&self.block_inst_evals_bound_rp).unwrap().len()
                              + bincode::serialize(&self.block_inst_evals_list).unwrap().len()
                              + bincode::serialize(&self.block_r1cs_eval_proof_list).unwrap().len()

                              + bincode::serialize(&self.pairwise_check_r1cs_sat_proof).unwrap().len()
                              + bincode::serialize(&self.pairwise_check_inst_evals_bound_rp).unwrap().len()

                              + bincode::serialize(&self.perm_poly_eval_list).unwrap().len()
                              + bincode::serialize(&self.proof_eval_perm_poly_prod_list).unwrap().len()

                              + bincode::serialize(&self.shift_proof).unwrap().len()
                              + bincode::serialize(&self.io_proof).unwrap().len();
    (commit_size, noncommit_size)
  }

  /// A public computation to create a commitment to a list of R1CS instances
  pub fn multi_encode(
    inst: &Instance,
    gens: &SNARKGens,
  ) -> (Vec<Vec<usize>>, Vec<ComputationCommitment>, Vec<ComputationDecommitment>) {
    let timer_encode = Timer::new("SNARK::encode");
    let (label_map, mut comm, mut decomm) = inst.inst.multi_commit(&gens.gens_r1cs_eval);
    timer_encode.stop();
    (
      label_map,
      comm.drain(..).map(|i| ComputationCommitment { comm: i }).collect(),
      decomm.drain(..).map(|i| ComputationDecommitment { decomm: i }).collect(),
    )
  }

  /// A public computation to create a commitment to a single R1CS instance
  pub fn encode(
    inst: &Instance,
    gens: &SNARKGens,
  ) -> (ComputationCommitment, ComputationDecommitment) {
    let timer_encode = Timer::new("SNARK::encode");
    let (comm, decomm) = inst.inst.commit(&gens.gens_r1cs_eval);
    timer_encode.stop();
    (
      ComputationCommitment { comm },
      ComputationDecommitment { decomm },
    )
  }

  // Given information regarding a group of memory assignments, generate w2, w3, and w3_shifted
  // if IS_VIR, need to process ts and ls
  fn mem_gen_prover<const MEM_WIDTH: usize, const IS_VIR: bool>(
    compact_shift: bool, // if compact_shift, w3 and w3_shifted are committed together
    total_num_mem_accesses: usize,
    mems_list: &Vec<Vec<Scalar>>,
    comb_r: &Scalar,
    comb_tau: &Scalar,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> (
    ProverWitnessSecInfo,
    PolyCommitment,
    ProverWitnessSecInfo,
    PolyCommitment,
    ProverWitnessSecInfo,
    PolyCommitment,
  ) {
    if total_num_mem_accesses > 0 {
      // init_mem_w2 is (I, O, ZO, r * data, 0, 0)
      // where ZO = 0,
      
      let mut mem_w2 = Vec::new();
      for q in 0..total_num_mem_accesses {
        mem_w2.push(vec![ZERO; MEM_WIDTH]);
        mem_w2[q][3] = comb_r * mems_list[q][3];
        if IS_VIR {
          mem_w2[q][4] = comb_r * comb_r * mems_list[q][4];
          mem_w2[q][5] = comb_r * comb_r * comb_r * mems_list[q][5];
        }
      }
      // init_mems_w3 is (v, x, pi, D, I, O)
      // where I = v * (v + addr + r * data + r^2 * ls + r^3 * ts),
      //       O = v * v = v
      // are used by (dummy) consistency check
      let mut mem_w3 = vec![
        vec![ZERO; if compact_shift { 2 * W3_WIDTH } else { W3_WIDTH }]; 
        total_num_mem_accesses
      ];
      for q in (0..total_num_mem_accesses).rev() {
        // v
        mem_w3[q][0] = mems_list[q][0];
        // x = v * (tau - addr - r * data - r^2 * ls - r^3 * ts)
        mem_w3[q][1] = mems_list[q][0] * (
          comb_tau 
          - mems_list[q][2] 
          - mem_w2[q][3]
          - if IS_VIR { mem_w2[q][4] + mem_w2[q][5] } else { ZERO }
        );
        // pi and D
        if q != total_num_mem_accesses - 1 {
          mem_w3[q][3] = mem_w3[q][1] * (mem_w3[q + 1][2] + ONE - mem_w3[q + 1][0]);
        } else {
          mem_w3[q][3] = mem_w3[q][1];
        }
        mem_w3[q][2] = mem_w3[q][0] * mem_w3[q][3];
        mem_w3[q][4] = mems_list[q][0] * (
          mems_list[q][0] 
          + mems_list[q][2] 
          + mem_w2[q][3]
          + if IS_VIR { mem_w2[q][4] + mem_w2[q][5] } else { ZERO }
        );
        mem_w3[q][5] = mems_list[q][0];
      }
      // if compact_shift, copy mem_w3[k+1][0..8] to mem_w3[k][8..16]
      if compact_shift {
        for q in 0..total_num_mem_accesses - 1 {
          for i in 0..W3_WIDTH {
            mem_w3[q][W3_WIDTH + i] = mem_w3[q + 1][i];
          }
        }
      }

      let (
        mem_w2_prover,
        mem_comm_w2,
        mem_w3_prover,
        mem_comm_w3,
        mem_w3_shifted_prover,
        mem_comm_w3_shifted
      ) = {
        let (mem_w2_prover, mem_comm_w2) = {
          // Flatten the witnesses into a Q_i * X list
          let w2_list_p = mem_w2.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let mem_poly_w2 = DensePolynomial::new(w2_list_p);

          // produce a commitment to the satisfying assignment
          let (mem_comm_w2, _blinds_vars) = mem_poly_w2.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          mem_comm_w2.append_to_transcript(b"poly_commitment", transcript);
          let mem_w2_prover = ProverWitnessSecInfo::new(vec![mem_w2], vec![mem_poly_w2]);
          (mem_w2_prover, mem_comm_w2)
        };
        
        let (mem_w3_prover, mem_comm_w3) = {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = mem_w3.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let mem_poly_w3 = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (mem_comm_w3, _blinds_vars) = mem_poly_w3.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          mem_comm_w3.append_to_transcript(b"poly_commitment", transcript);
          let mem_w3_prover = ProverWitnessSecInfo::new(vec![mem_w3.clone()], vec![mem_poly_w3]);
          (mem_w3_prover, mem_comm_w3)
        };

        let (mem_w3_shifted_prover, mem_comm_w3_shifted) = if compact_shift {
          (ProverWitnessSecInfo::dummy(), PolyCommitment::empty())
        } else {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = [mem_w3[1..].to_vec().clone().into_iter().flatten().collect(), vec![ZERO; W3_WIDTH]].concat();
          // create a multilinear polynomial using the supplied assignment for variables
          let mem_poly_w3_shifted = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (mem_comm_w3_shifted, _blinds_vars) = mem_poly_w3_shifted.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          mem_comm_w3_shifted.append_to_transcript(b"poly_commitment", transcript);
          let mem_w3_shifted_prover = ProverWitnessSecInfo::new(vec![[mem_w3[1..].to_vec(), vec![vec![ZERO; W3_WIDTH]]].concat()], vec![mem_poly_w3_shifted]);
          (mem_w3_shifted_prover, mem_comm_w3_shifted)
        };

        (
          mem_w2_prover,
          mem_comm_w2,
          mem_w3_prover,
          mem_comm_w3,
          mem_w3_shifted_prover,
          mem_comm_w3_shifted,
        )
      };

      (
        mem_w2_prover,
        mem_comm_w2,
        mem_w3_prover,
        mem_comm_w3,
        mem_w3_shifted_prover,
        mem_comm_w3_shifted
      )
    } else {
      (
        ProverWitnessSecInfo::dummy(),
        PolyCommitment::empty(),
        ProverWitnessSecInfo::dummy(),
        PolyCommitment::empty(),
        ProverWitnessSecInfo::dummy(),
        PolyCommitment::empty()
      )
    }
  }
  
  fn mem_gen_verifier<const MEM_WIDTH: usize>(
    compact_shift: bool, // if compact_shift, w3 and w3_shifted are committed together
    total_num_mem_accesses: usize,
    comm_w2: &PolyCommitment,
    comm_w3: &PolyCommitment,
    comm_w3_shifted: &PolyCommitment,
    transcript: &mut Transcript,
  ) -> (
    VerifierWitnessSecInfo,
    VerifierWitnessSecInfo,
    VerifierWitnessSecInfo,
  ) {
    if total_num_mem_accesses > 0 {
      let w2_verifier = {
        comm_w2.append_to_transcript(b"poly_commitment", transcript);
        VerifierWitnessSecInfo::new(vec![MEM_WIDTH], &vec![total_num_mem_accesses], vec![comm_w2.clone()])
      };
      let w3_verifier = {
        comm_w3.append_to_transcript(b"poly_commitment", transcript);
        VerifierWitnessSecInfo::new(vec![if compact_shift { 2 * W3_WIDTH } else { W3_WIDTH }], &vec![total_num_mem_accesses], vec![comm_w3.clone()])
      };
      let w3_shifted_verifier = if compact_shift {
        VerifierWitnessSecInfo::dummy()
      } else {
        comm_w3_shifted.append_to_transcript(b"poly_commitment", transcript);
        VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![total_num_mem_accesses], vec![comm_w3_shifted.clone()])
      };
      (
        w2_verifier,
        w3_verifier,
        w3_shifted_verifier,
      )
    } else {
      (
        VerifierWitnessSecInfo::dummy(),
        VerifierWitnessSecInfo::dummy(),
        VerifierWitnessSecInfo::dummy(),
      )
    }
  }

  /// A method to produce a SNARK proof of the satisfiability of an R1CS instance
  pub fn prove(
    sparse_commit: bool,
    compact_shift: bool,
    
    input_block_num: usize,
    output_block_num: usize,
    input_liveness: &Vec<bool>,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    max_block_num_phy_ops: usize,
    block_num_phy_ops: &Vec<usize>,
    max_block_num_vir_ops: usize,
    block_num_vir_ops: &Vec<usize>,
    mem_addr_ts_bits_size: usize,
    num_inputs_unpadded: usize,
    block_num_vars: &Vec<usize>,

    block_num_circuits_bound: usize,
    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_inst: &mut Instance,
    block_comm_map: &Vec<Vec<usize>>,
    block_comm_list: &Vec<ComputationCommitment>,
    block_decomm_list: &Vec<ComputationDecommitment>,
    block_gens: &SNARKGens,

    consis_num_proofs: usize,
    total_num_init_phy_mem_accesses: usize,
    total_num_init_vir_mem_accesses: usize,
    total_num_phy_mem_accesses: usize,
    total_num_vir_mem_accesses: usize,
    pairwise_check_inst: &mut Instance,
    pairwise_check_comm: &ComputationCommitment,

    block_vars_mat: Vec<Vec<VarsAssignment>>,
    exec_inputs_list: Vec<InputsAssignment>,
    init_phy_mems_list: Vec<MemsAssignment>,
    init_vir_mems_list: Vec<MemsAssignment>,
    addr_phy_mems_list: Vec<MemsAssignment>,
    addr_vir_mems_list: Vec<MemsAssignment>,
    addr_ts_bits_list: Vec<MemsAssignment>,

    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Self {
    let timer_prove = Timer::new("SNARK::prove");

    // we create a Transcript object seeded with a random Scalar
    // to aid the prover produce its randomness
    let mut random_tape = RandomTape::new(b"proof");

    transcript.append_protocol_name(SNARK::protocol_name());

    // --
    // ASSERTIONS
    // --
    assert!(0 < consis_num_proofs);
    for p in 0..block_num_circuits_bound {
      assert!(block_num_proofs[p] <= block_max_num_proofs);
    }
    let io_width = 2 * num_inputs_unpadded;

    // --
    // PREPROCESSING
    // --
    // unwrap the assignments
    let mut block_vars_mat = block_vars_mat.into_iter().map(|a| a.into_iter().map(|v| v.assignment).collect_vec()).collect_vec();
    let mut exec_inputs_list = exec_inputs_list.into_iter().map(|v| v.assignment).collect_vec();
    let mut init_phy_mems_list = init_phy_mems_list.into_iter().map(|v| v.assignment).collect_vec();
    let mut init_vir_mems_list = init_vir_mems_list.into_iter().map(|v| v.assignment).collect_vec();
    let mut addr_phy_mems_list = addr_phy_mems_list.into_iter().map(|v| v.assignment).collect_vec();
    let mut addr_vir_mems_list = addr_vir_mems_list.into_iter().map(|v| v.assignment).collect_vec();
    let mut addr_ts_bits_list = addr_ts_bits_list.into_iter().map(|v| v.assignment).collect_vec();

    // --
    // INSTANCE COMMITMENTS
    // --
    let input_block_num = Scalar::from(input_block_num as u64);
    let output_block_num = Scalar::from(output_block_num as u64);
    let input: Vec<Scalar> = input.iter().map(|i| Scalar::from_bytes(i).unwrap()).collect();
    let output: Scalar = Scalar::from_bytes(output).unwrap();
    {
      let timer_commit = Timer::new("inst_commit");
      // Commit public parameters
      Scalar::from(func_input_width as u64).append_to_transcript(b"func_input_width", transcript);
      Scalar::from(input_offset as u64).append_to_transcript(b"input_offset", transcript);
      Scalar::from(output_offset as u64).append_to_transcript(b"output_offset", transcript);
      Scalar::from(output_exec_num as u64).append_to_transcript(b"output_exec_num", transcript);
      Scalar::from(num_ios as u64).append_to_transcript(b"num_ios", transcript);
      for n in block_num_vars {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_vars", transcript);
      }
      Scalar::from(mem_addr_ts_bits_size as u64).append_to_transcript(b"mem_addr_ts_bits_size", transcript);
      Scalar::from(num_inputs_unpadded as u64).append_to_transcript(b"num_inputs_unpadded", transcript);
      Scalar::from(block_num_circuits_bound as u64).append_to_transcript(b"block_num_circuits_bound", transcript);
      Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
      for p in block_num_phy_ops {
        Scalar::from(*p as u64).append_to_transcript(b"block_num_phy_ops", transcript);
      }
      for v in block_num_vir_ops {
        Scalar::from(*v as u64).append_to_transcript(b"block_num_vir_ops", transcript);
      }
      Scalar::from(total_num_init_phy_mem_accesses as u64).append_to_transcript(b"total_num_init_phy_mem_accesses", transcript);
      Scalar::from(total_num_init_vir_mem_accesses as u64).append_to_transcript(b"total_num_init_vir_mem_accesses", transcript);
      Scalar::from(total_num_phy_mem_accesses as u64).append_to_transcript(b"total_num_phy_mem_accesses", transcript);
      Scalar::from(total_num_vir_mem_accesses as u64).append_to_transcript(b"total_num_vir_mem_accesses", transcript);
      
      // commit num_proofs
      Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
      for n in block_num_proofs {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_proofs", transcript);
      }

      // append a commitment to the computation to the transcript
      for b in block_comm_map {
        for l in b {
          Scalar::from(*l as u64).append_to_transcript(b"block_comm_map", transcript);
        }
      }
      for c in block_comm_list {
        c.comm.append_to_transcript(b"block_comm", transcript);
      }
      pairwise_check_comm.comm.append_to_transcript(b"pairwise_comm", transcript);

      // Commit io
      input_block_num.append_to_transcript(b"input_block_num", transcript);
      output_block_num.append_to_transcript(b"output_block_num", transcript);
      input.append_to_transcript(b"input_list", transcript);
      output.append_to_transcript(b"output_list", transcript);

      timer_commit.stop();
    }

    // --
    // INST_TRUNCATE
    // --
    let timer_truncate = Timer::new("inst_truncate");
    // Block
    let block_num_proofs_circuit = block_num_proofs.clone();
    let block_inst_untruncated = block_inst.clone();
    block_inst.truncate(&block_num_proofs_circuit);
    let (block_num_circuits, mut block_num_proofs, block_num_phy_ops, block_num_vir_ops) = {
      let mut block_num_proofs = Vec::new();
      let mut block_num_phy_ops_t = Vec::new();
      let mut block_num_vir_ops_t = Vec::new();
      for i in 0..block_num_proofs_circuit.len() {
        if block_num_proofs_circuit[i] > 0 {
          block_num_proofs.push(block_num_proofs_circuit[i]);
          block_num_phy_ops_t.push(block_num_phy_ops[i]);
          block_num_vir_ops_t.push(block_num_vir_ops[i]);
        }
      }
      (block_num_proofs.len(), block_num_proofs, block_num_phy_ops_t, block_num_vir_ops_t)
    };
    // Pairwise
    let pairwise_num_proofs_circuit = vec![consis_num_proofs, total_num_phy_mem_accesses, total_num_vir_mem_accesses, total_num_init_phy_mem_accesses, total_num_init_vir_mem_accesses, total_num_phy_mem_accesses, total_num_vir_mem_accesses];
    pairwise_check_inst.truncate(&pairwise_num_proofs_circuit);

    // --
    // PADDING
    // --
    let dummy_inputs = vec![ZERO; num_ios];
    // For every block that num_proofs is not a power of 2, pad vars_mat and inputs_mat until the length is a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();

    for i in 0..block_num_circuits {
      let dummy_vars = vec![ZERO; block_vars_mat[i][0].len()];
      let gap = block_num_proofs[i].next_power_of_two() - block_num_proofs[i];
      block_vars_mat[i].extend(vec![dummy_vars.clone(); gap]);
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad exec_inputs with dummys so the length is a power of 2
    exec_inputs_list.extend(vec![dummy_inputs; consis_num_proofs.next_power_of_two() - consis_num_proofs]);
    let consis_num_proofs = consis_num_proofs.next_power_of_two();
    
    // Pad init_mems with dummys so the length is a power of 2
    if total_num_init_phy_mem_accesses > 0 {
      let dummy_addr = vec![ZERO; INIT_PHY_MEM_WIDTH];
      init_phy_mems_list.extend(vec![dummy_addr; total_num_init_phy_mem_accesses.next_power_of_two() - total_num_init_phy_mem_accesses]);
    }
    let total_num_init_phy_mem_accesses = if total_num_init_phy_mem_accesses == 0 { 0 } else { total_num_init_phy_mem_accesses.next_power_of_two() };
    if total_num_init_vir_mem_accesses > 0 {
      let dummy_addr = vec![ZERO; INIT_VIR_MEM_WIDTH];
      init_vir_mems_list.extend(vec![dummy_addr; total_num_init_vir_mem_accesses.next_power_of_two() - total_num_init_vir_mem_accesses]);
    }
    let total_num_init_vir_mem_accesses = if total_num_init_vir_mem_accesses == 0 { 0 } else { total_num_init_vir_mem_accesses.next_power_of_two() };
    // Pad addr_phy_mems with dummys so the length is a power of 2
    if total_num_phy_mem_accesses > 0 {
      let dummy_addr = vec![ZERO; PHY_MEM_WIDTH];
      addr_phy_mems_list.extend(vec![dummy_addr; total_num_phy_mem_accesses.next_power_of_two() - total_num_phy_mem_accesses]);
    }
    let total_num_phy_mem_accesses = if total_num_phy_mem_accesses == 0 { 0 } else { total_num_phy_mem_accesses.next_power_of_two() };
    // Pad addr_vir_mems with dummys so the length is a power of 2
    if total_num_vir_mem_accesses > 0 {
      let dummy_addr = vec![ZERO; VIR_MEM_WIDTH];
      addr_vir_mems_list.extend(vec![dummy_addr; total_num_vir_mem_accesses.next_power_of_two() - total_num_vir_mem_accesses]);
      let dummy_ts = vec![ZERO; mem_addr_ts_bits_size];
      addr_ts_bits_list.extend(vec![dummy_ts; total_num_vir_mem_accesses.next_power_of_two() - total_num_vir_mem_accesses]);
    }
    let total_num_vir_mem_accesses = if total_num_vir_mem_accesses == 0 { 0 } else { total_num_vir_mem_accesses.next_power_of_two() };
    let block_num_proofs = &block_num_proofs;

    timer_truncate.stop();

    // --
    // CHALLENGES AND WITNESSES FOR PERMUTATION
    // --
    let timer_gen = Timer::new("witness_gen");
    // Block
    let timer_sec_gen = Timer::new("block_witness_gen");
    let (
      comb_tau,
      comb_r,
      perm_r_prover,
      // perm_exec
      perm_exec_w2_prover,
      perm_exec_comm_w2_list,
      perm_exec_w3_prover,
      perm_exec_comm_w3_list,
      perm_exec_w3_shifted_prover, // shifted by W3_WIDTH
      perm_exec_comm_w3_shifted,
      // input_block_w2 | phy_mem_block_w2 | vir_mem_block_w2
      block_w2_prover,
      block_comm_w2_list,
      // block_w3
      block_w3_prover,
      block_comm_w3_list,
      block_w3_shifted_prover, // shifted by W3_WIDTH
      block_comm_w3_list_shifted,
    ) = {
      let comb_tau = transcript.challenge_scalar(b"challenge_tau");
      let comb_r = transcript.challenge_scalar(b"challenge_r");
      
      // PERM_R
      //r is (tau, r, r^2, ...) for the first 2 * num_inputs_unpadded entries
      // set the first entry to 1 for multiplication and later revert it to tau
      let perm_r = {
        let mut perm_r = vec![comb_tau];
        let mut r_tmp = comb_r;
        for _ in 1..2 * num_inputs_unpadded {
          perm_r.push(r_tmp);
          r_tmp *= comb_r;
        }
        perm_r.extend(vec![ZERO; num_ios - 2 * num_inputs_unpadded]);
        perm_r
      };
      // create a multilinear polynomial using the supplied assignment for variables
      let perm_poly_r = DensePolynomial::new(perm_r.clone());
      // produce a commitment to the satisfying assignment
      let (perm_comm_r, _blinds_vars) = perm_poly_r.commit(&vars_gens.gens_pc, None);
      // add the commitment to the prover's transcript
      perm_comm_r.append_to_transcript(b"poly_commitment", transcript);

      // PERM_EXEC
      // w2 is _, _, ZO, r * i1, r^2 * i2, r^3 * i3, ...
      // where ZO * r^n = r^n * o0 + r^(n + 1) * o1, ...,
      // are used by the consistency check
      let perm_exec_w2 = {
        let mut perm_exec_w2: Vec<Vec<Scalar>> = exec_inputs_list.iter().map(|input|
          [
            vec![ZERO; 3],
            (1..2 * num_inputs_unpadded - 2).map(|j| perm_r[j] * input[j + 2]).collect(),
            vec![ZERO; num_ios - 2 * num_inputs_unpadded]
          ].concat()
        ).collect();
        for q in 0..consis_num_proofs {
          perm_exec_w2[q][0] = exec_inputs_list[q][0];
          perm_exec_w2[q][1] = exec_inputs_list[q][0];
          for i in 0..num_inputs_unpadded - 1 {
            let perm = if i == 0 { ONE } else { perm_r[i] };
            perm_exec_w2[q][0] += perm * exec_inputs_list[q][2 + i];
            perm_exec_w2[q][2] += perm * exec_inputs_list[q][2 + (num_inputs_unpadded - 1) + i];
          }
          perm_exec_w2[q][0] *= exec_inputs_list[q][0];
          let ZO = perm_exec_w2[q][2];
          perm_exec_w2[q][1] += ZO;
          perm_exec_w2[q][1] *= exec_inputs_list[q][0];
        }
        perm_exec_w2
      };
      // w3 is [v, x, pi, D]
      let perm_exec_w3 = {
        let mut perm_exec_w3: Vec<Vec<Scalar>> = vec![Vec::new(); consis_num_proofs];
        for q in (0..consis_num_proofs).rev() {
          perm_exec_w3[q] = vec![ZERO; if compact_shift { 2 * W3_WIDTH } else { W3_WIDTH }];
          perm_exec_w3[q][0] = exec_inputs_list[q][0];
          perm_exec_w3[q][1] = perm_exec_w3[q][0] * (comb_tau - perm_exec_w2[q][3..].iter().fold(ZERO, |a, b| a + b) - exec_inputs_list[q][2]);
          perm_exec_w3[q][4] = perm_exec_w2[q][0];
          perm_exec_w3[q][5] = perm_exec_w2[q][1];
          if q != consis_num_proofs - 1 {
            perm_exec_w3[q][3] = perm_exec_w3[q][1] * (perm_exec_w3[q + 1][2] + ONE - perm_exec_w3[q + 1][0]);
          } else {
            perm_exec_w3[q][3] = perm_exec_w3[q][1];
          }
          perm_exec_w3[q][2] = perm_exec_w3[q][0] * perm_exec_w3[q][3];
        }
        // if compact_shift, copy perm_exec_w3[q + 1][i] to perm_exec_w3[q][W3_WIDTH + i]
        if compact_shift {
          for q in 0..consis_num_proofs - 1 {
            for i in 0..W3_WIDTH {
              perm_exec_w3[q][W3_WIDTH + i] = perm_exec_w3[q + 1][i];
            }
          }
        }
        perm_exec_w3
      };
      // commit the witnesses and inputs separately circuit-by-circuit
      let (
        perm_exec_w2_prover,
        perm_exec_comm_w2,
        perm_exec_w3_prover,
        perm_exec_comm_w3,
        perm_exec_w3_shifted_prover,
        perm_exec_comm_w3_shifted,
      ) = {
        let (perm_exec_w2_prover, perm_exec_comm_w2) = {
          // Flatten the witnesses into a Q_i * X list
          let w2_list_p = perm_exec_w2.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_exec_poly_w2 = DensePolynomial::new(w2_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_exec_comm_w2, _blinds_vars) = perm_exec_poly_w2.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_exec_comm_w2.append_to_transcript(b"poly_commitment", transcript);
          let perm_exec_w2_prover = ProverWitnessSecInfo::new(vec![perm_exec_w2], vec![perm_exec_poly_w2]);
          (perm_exec_w2_prover, perm_exec_comm_w2)
        };

        let (perm_exec_w3_prover, perm_exec_comm_w3) = {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = perm_exec_w3.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_exec_poly_w3 = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_exec_comm_w3, _blinds_vars) = perm_exec_poly_w3.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_exec_comm_w3.append_to_transcript(b"poly_commitment", transcript);
          let perm_exec_w3_prover = ProverWitnessSecInfo::new(vec![perm_exec_w3.clone()], vec![perm_exec_poly_w3]);
          (perm_exec_w3_prover, perm_exec_comm_w3)
        };

        let (perm_exec_w3_shifted_prover, perm_exec_comm_w3_shifted) = if compact_shift {
          (ProverWitnessSecInfo::dummy(), PolyCommitment::empty())
        } else {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = [perm_exec_w3[1..].to_vec().clone().into_iter().flatten().collect(), vec![ZERO; W3_WIDTH]].concat();
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_exec_poly_w3_shifted = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_exec_comm_w3_shifted, _blinds_vars) = perm_exec_poly_w3_shifted.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_exec_comm_w3_shifted.append_to_transcript(b"poly_commitment", transcript);
          let perm_exec_w3_shifted_prover = ProverWitnessSecInfo::new(vec![[perm_exec_w3[1..].to_vec(), vec![vec![ZERO; W3_WIDTH]]].concat()], vec![perm_exec_poly_w3_shifted]);
          (perm_exec_w3_shifted_prover, perm_exec_comm_w3_shifted)
        };

        (
          perm_exec_w2_prover,
          perm_exec_comm_w2,
          perm_exec_w3_prover,
          perm_exec_comm_w3,
          perm_exec_w3_shifted_prover,
          perm_exec_comm_w3_shifted,
        )
      };

      // INPUT_BLOCK_W2 | PHY_MEM_BLOCK_W2 & VIR_MEM_BLOCK_W2
      // BLOCK_W3
      //           INPUT      PHY    VIR
      // w3 is [v, x, pi, D, pi, D, pi, D]
      let mut block_w3: Vec<Vec<Vec<Scalar>>> = Vec::new();
      let (block_w2_prover, block_comm_w2_list) = {
        let mut block_w2 = Vec::new();
        let block_w2_size_list: Vec<usize> = (0..block_num_circuits).map(|i| (2 * num_inputs_unpadded + 2 * block_num_phy_ops[i] + 4 * block_num_vir_ops[i]).next_power_of_two()).collect();

        // PHY_MEM
        // w2 is (MR, MC, MR, MC, MR, MC, ...)
        // w3 is (V, X, PI, D)
        let V_PA = |i: usize| 2 * i;
        let V_PD = |i: usize| 2 * i + 1;
        let V_PMR = |i: usize| 2 * num_inputs_unpadded + 2 * i;
        let V_PMC = |i: usize| 2 * num_inputs_unpadded + 2 * i + 1;
        // VIR_MEM
        // w2 is (MR1, MR2, MR3, MC, MR1, MR2, MR3, MC, ...)
        // w3 is (V, X, PI, D)
        let V_VA = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i;
        let V_VD = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i + 1;
        let V_VL = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i + 2;
        let V_VT = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i + 3;
        let V_VMR1 = |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i;
        let V_VMR2 = |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i + 1;
        let V_VMR3 = |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i + 2;
        let V_VMC = |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i + 3;

        for p in 0..block_num_circuits {
          block_w2.push(vec![Vec::new(); block_num_proofs[p]]);
          block_w3.push(vec![Vec::new(); block_num_proofs[p]]);
          for q in (0..block_num_proofs[p]).rev() {
            let V_CNST = block_vars_mat[p][q][0];
            // For INPUT
            block_w2[p][q] = vec![ZERO; block_w2_size_list[p]];
            
            block_w2[p][q][0] = block_vars_mat[p][q][0];
            block_w2[p][q][1] = block_vars_mat[p][q][0];
            for i in 1..2 * (num_inputs_unpadded - 1) {
              block_w2[p][q][2 + i] += perm_r[i] * block_vars_mat[p][q][i + 2];
            }
            for i in 0..num_inputs_unpadded - 1 {
              let perm = if i == 0 { ONE } else { perm_r[i] };
              block_w2[p][q][0] += perm * block_vars_mat[p][q][2 + i];
              block_w2[p][q][2] += perm * block_vars_mat[p][q][2 + (num_inputs_unpadded - 1) + i];
            }
            block_w2[p][q][0] *= block_vars_mat[p][q][0];
            let ZO = block_w2[p][q][2];
            block_w2[p][q][1] += ZO;
            block_w2[p][q][1] *= block_vars_mat[p][q][0];
            block_w3[p][q] = vec![ZERO; if compact_shift { 2 * W3_WIDTH } else { W3_WIDTH }];
            block_w3[p][q][0] = block_vars_mat[p][q][0];
            block_w3[p][q][1] = block_w3[p][q][0] * (comb_tau - block_w2[p][q][3..].iter().fold(ZERO, |a, b| a + b) - block_vars_mat[p][q][2]);
            if q != block_num_proofs[p] - 1 {
              block_w3[p][q][3] = block_w3[p][q][1] * (block_w3[p][q + 1][2] + ONE - block_w3[p][q + 1][0]);
            } else {
              block_w3[p][q][3] = block_w3[p][q][1];
            }
            block_w3[p][q][2] = block_w3[p][q][0] * block_w3[p][q][3];

            // For PHY
            // Compute PMR, PMC
            for i in 0..block_num_phy_ops[p] {
              // PMR = r * PD
              block_w2[p][q][V_PMR(i)] = comb_r * block_vars_mat[p][q][io_width + V_PD(i)];
              // PMC = (1 or PMC[i-1]) * (tau - PA - PMR)
              let t = if i == 0 { V_CNST } else {block_w2[p][q][V_PMC(i - 1)] };
              block_w2[p][q][V_PMC(i)] = t * (comb_tau - block_vars_mat[p][q][io_width + V_PA(i)] - block_w2[p][q][V_PMR(i)]);
            }
            // Compute x
            let px = if block_num_phy_ops[p] == 0 { V_CNST } else { block_w2[p][q][V_PMC(block_num_phy_ops[p] - 1)] };
            // Compute D and pi
            if q != block_num_proofs[p] - 1 {
              block_w3[p][q][5] = px * (block_w3[p][q + 1][4] + ONE - block_w3[p][q + 1][0]);
            } else {
              block_w3[p][q][5] = px;
            }
            block_w3[p][q][4] = V_CNST * block_w3[p][q][5];

            // For VIR
            // Compute VMR1, VMR2, VMR3, VMC
            for i in 0..block_num_vir_ops[p] {
              // VMR1 = r * VD
              block_w2[p][q][V_VMR1(p, i)] = comb_r * block_vars_mat[p][q][io_width + V_VD(p, i)];
              // VMR2 = r^2 * VL
              block_w2[p][q][V_VMR2(p, i)] = comb_r * comb_r * block_vars_mat[p][q][io_width + V_VL(p, i)];
              // VMR1 = r^3 * VT
              block_w2[p][q][V_VMR3(p, i)] = comb_r * comb_r * comb_r * block_vars_mat[p][q][io_width + V_VT(p, i)];
              // VMC = (1 or VMC[i-1]) * (tau - VA - VMR1 - VMR2 - VMR3)
              let t = if i == 0 { V_CNST } else { block_w2[p][q][V_VMC(p, i - 1)] };
              block_w2[p][q][V_VMC(p, i)] = t * (
                comb_tau 
                - block_vars_mat[p][q][io_width + V_VA(p, i)] 
                - block_w2[p][q][V_VMR1(p, i)] 
                - block_w2[p][q][V_VMR2(p, i)] 
                - block_w2[p][q][V_VMR3(p, i)]
              );
            }
            // Compute x
            let vx = if block_num_vir_ops[p] == 0 { V_CNST } else { block_w2[p][q][V_VMC(p, block_num_vir_ops[p] - 1)] };
            // Compute D and pi
            if q != block_num_proofs[p] - 1 {
              block_w3[p][q][7] = vx * (block_w3[p][q + 1][6] + ONE - block_w3[p][q + 1][0]);
            } else {
              block_w3[p][q][7] = vx;
            }
            block_w3[p][q][6] = V_CNST * block_w3[p][q][7];
          }
          // If compact_shift, copy the next row of block_w3 forward
          if compact_shift {
            for q in 0..block_num_proofs[p] - 1 {
              for i in 0..W3_WIDTH {
                block_w3[p][q][W3_WIDTH + i] = block_w3[p][q + 1][i];
              }
            }
          }
        }

        // commit the witnesses and inputs separately circuit-by-circuit
        let mut block_poly_w2_list = Vec::new();
        let mut block_comm_w2_list = Vec::new();

        for p in 0..block_num_circuits {
          let (block_poly_w2, block_comm_w2) = {
            // Flatten the witnesses into a Q_i * X list
            let w2_list_p = block_w2[p].clone().into_iter().flatten().collect();
            // create a multilinear polynomial using the supplied assignment for variables
            let block_poly_w2 = DensePolynomial::new(w2_list_p);
            // produce a commitment to the satisfying assignment
            let (block_comm_w2, _blinds_vars) = block_poly_w2.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            block_comm_w2.append_to_transcript(b"poly_commitment", transcript);
            (block_poly_w2, block_comm_w2)
          };
          block_poly_w2_list.push(block_poly_w2);
          block_comm_w2_list.push(block_comm_w2);
        }

        let block_w2_prover = ProverWitnessSecInfo::new(block_w2.clone(), block_poly_w2_list);
        (
          block_w2_prover,
          block_comm_w2_list,
        )
      };

      let (
        block_w3_prover,
        block_comm_w3_list,
        block_w3_shifted_prover,
        block_comm_w3_list_shifted
      ) = {
        let mut block_poly_w3_list = Vec::new();
        let mut block_comm_w3_list = Vec::new();
        let mut block_poly_w3_list_shifted = Vec::new();
        let mut block_comm_w3_list_shifted = Vec::new();

        for p in 0..block_num_circuits {
          let (block_poly_w3, block_comm_w3) = {
            // Flatten the witnesses into a Q_i * X list
            let w3_list_p = block_w3[p].clone().into_iter().flatten().collect();
            // create a multilinear polynomial using the supplied assignment for variables
            let block_poly_w3 = DensePolynomial::new(w3_list_p);

            // produce a commitment to the satisfying assignment
            let (block_comm_w3, _blinds_vars) = block_poly_w3.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            block_comm_w3.append_to_transcript(b"poly_commitment", transcript);
            (block_poly_w3, block_comm_w3)
          };
          block_poly_w3_list.push(block_poly_w3);
          block_comm_w3_list.push(block_comm_w3);

          if !compact_shift {
            let (block_poly_w3_shifted, block_comm_w3_shifted) = {
              // Flatten the witnesses into a Q_i * X list
              let w3_list_p = [block_w3[p][1..].to_vec().clone().into_iter().flatten().collect(), vec![ZERO; W3_WIDTH]].concat();
              // create a multilinear polynomial using the supplied assignment for variables
              let block_poly_w3_shifted = DensePolynomial::new(w3_list_p);

              // produce a commitment to the satisfying assignment
              let (block_comm_w3_shifted, _blinds_vars) = block_poly_w3_shifted.commit(&vars_gens.gens_pc, None);

              // add the commitment to the prover's transcript
              block_comm_w3_shifted.append_to_transcript(b"poly_commitment", transcript);
              (block_poly_w3_shifted, block_comm_w3_shifted)
            };
            block_poly_w3_list_shifted.push(block_poly_w3_shifted);
            block_comm_w3_list_shifted.push(block_comm_w3_shifted);
          }
        }
        let block_w3_prover = ProverWitnessSecInfo::new(block_w3.clone(), block_poly_w3_list);
        let block_w3_shifted_prover = if compact_shift {
          ProverWitnessSecInfo::dummy()
        } else {
          ProverWitnessSecInfo::new(
            block_w3.iter().map(|i| [i[1..].to_vec(), vec![vec![ZERO; W3_WIDTH]]].concat()).collect(), 
            block_poly_w3_list_shifted
          )
        };

        (
          block_w3_prover,
          block_comm_w3_list,
          block_w3_shifted_prover,
          block_comm_w3_list_shifted
        )
      };

      let perm_r_prover = ProverWitnessSecInfo::new(vec![vec![perm_r]], vec![perm_poly_r]);
      (
        comb_tau,
        comb_r,

        perm_r_prover,
        perm_exec_w2_prover,
        perm_exec_comm_w2,
        perm_exec_w3_prover,
        perm_exec_comm_w3,
        perm_exec_w3_shifted_prover,
        perm_exec_comm_w3_shifted,
        
        block_w2_prover, 
        block_comm_w2_list,
        block_w3_prover,
        block_comm_w3_list,
        block_w3_shifted_prover,
        block_comm_w3_list_shifted,
      )
    };
    timer_sec_gen.stop();

    // Initial Physical Memory-as-a-whole
    let timer_sec_gen = Timer::new("init_phy_mem_witness_gen");
    let (
      init_phy_mem_w2_prover,
      init_phy_mem_comm_w2,
      init_phy_mem_w3_prover,
      init_phy_mem_comm_w3,
      init_phy_mem_w3_shifted_prover,
      init_phy_mem_comm_w3_shifted
    ) = Self::mem_gen_prover::<INIT_PHY_MEM_WIDTH, false>(compact_shift, total_num_init_phy_mem_accesses, &init_phy_mems_list, &comb_r, &comb_tau, &vars_gens, transcript);
    timer_sec_gen.stop();

    // Initial Virtual Memory-as-a-whole
    let timer_sec_gen = Timer::new("init_vir_mem_witness_gen");
    let (
      init_vir_mem_w2_prover,
      init_vir_mem_comm_w2,
      init_vir_mem_w3_prover,
      init_vir_mem_comm_w3,
      init_vir_mem_w3_shifted_prover,
      init_vir_mem_comm_w3_shifted
    // IS_VIR set to false since ts and ls will always be 0
    ) = Self::mem_gen_prover::<INIT_VIR_MEM_WIDTH, false>(compact_shift, total_num_init_vir_mem_accesses, &init_vir_mems_list, &comb_r, &comb_tau, &vars_gens, transcript);
    timer_sec_gen.stop();

    // Physical Memory-as-a-whole
    let timer_sec_gen = Timer::new("phy_mem_addr_witness_gen");
    let (
      phy_mem_addr_w2_prover,
      phy_mem_addr_comm_w2,
      phy_mem_addr_w3_prover,
      phy_mem_addr_comm_w3,
      phy_mem_addr_w3_shifted_prover,
      phy_mem_addr_comm_w3_shifted
    ) = Self::mem_gen_prover::<PHY_MEM_WIDTH, false>(compact_shift, total_num_phy_mem_accesses, &addr_phy_mems_list, &comb_r, &comb_tau, &vars_gens, transcript);
    timer_sec_gen.stop();
    
    // Virtual Memory-as-a-whole
    let timer_sec_gen = Timer::new("vir_mem_addr_witness_gen");
    let (
      vir_mem_addr_w2_prover,
      vir_mem_addr_comm_w2,
      vir_mem_addr_w3_prover,
      vir_mem_addr_comm_w3,
      vir_mem_addr_w3_shifted_prover,
      vir_mem_addr_comm_w3_shifted
    ) = Self::mem_gen_prover::<VIR_MEM_WIDTH, true>(compact_shift, total_num_vir_mem_accesses, &addr_vir_mems_list, &comb_r, &comb_tau, &vars_gens, transcript);
    timer_sec_gen.stop();

    // Pad phy_mems to size 8
    let (init_phy_mems_list, init_vir_mems_list, addr_phy_mems_list, addr_vir_mems_list) = {
      let init_phy_mems_list: Vec<Vec<Scalar>> = init_phy_mems_list.into_iter().map(|e| {
        let pad_size = INIT_PHY_MEM_WIDTH - e.len();
        [e, vec![ZERO; pad_size]].concat()
      }).collect();
      let init_vir_mems_list: Vec<Vec<Scalar>> = init_vir_mems_list.into_iter().map(|e| {
        let pad_size = INIT_VIR_MEM_WIDTH - e.len();
        [e, vec![ZERO; pad_size]].concat()
      }).collect();
      let mut addr_phy_mems_list: Vec<Vec<Scalar>> = addr_phy_mems_list.into_iter().map(|e| {
        let pad_size = PHY_MEM_WIDTH - e.len();
        [e, vec![ZERO; pad_size]].concat()
      }).collect();
      let mut addr_vir_mems_list = addr_vir_mems_list;
      if compact_shift {
        // Expand addr_phy_mems and addr_vir_mems to include their next entry
        for i in 0..total_num_phy_mem_accesses {
          if i == total_num_phy_mem_accesses - 1 {
            addr_phy_mems_list[i].extend(vec![ZERO; PHY_MEM_WIDTH]);
          } else {
            let next_phy = addr_phy_mems_list[i + 1].clone();
            addr_phy_mems_list[i].extend(&next_phy);
          }
        }
        for i in 0..total_num_vir_mem_accesses {
          if i == total_num_vir_mem_accesses - 1 {
            addr_vir_mems_list[i].extend(vec![ZERO; VIR_MEM_WIDTH]);
          } else {
            let next_vir = addr_vir_mems_list[i + 1].clone();
            addr_vir_mems_list[i].extend(&next_vir);
          }
        }
      }
      (init_phy_mems_list, init_vir_mems_list, addr_phy_mems_list, addr_vir_mems_list)
    };
    timer_gen.stop();

    // --
    // WITNESS COMMITMENTS
    // --
    let timer_commit = Timer::new("input_commit");
    let (
      block_poly_vars_list,
      block_comm_vars_list,
      exec_poly_inputs,
      exec_comm_inputs
    ) = {
      // commit the witnesses and inputs separately circuit-by-circuit
      let mut block_poly_vars_list = Vec::new();
      let mut block_comm_vars_list = Vec::new();

      for p in 0..block_num_circuits {
        let (block_poly_vars, block_comm_vars) = {
          // Flatten the witnesses into a Q_i * X list
          let vars_list_p: Vec<Scalar> = block_vars_mat[p].clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let block_poly_vars = DensePolynomial::new(vars_list_p);

          // produce a commitment to the satisfying assignment
          let (block_comm_vars, _blinds_vars) = block_poly_vars.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          block_comm_vars.append_to_transcript(b"poly_commitment", transcript);
          (block_poly_vars, block_comm_vars)
        };
        block_poly_vars_list.push(block_poly_vars);
        block_comm_vars_list.push(block_comm_vars);
      }

      let (exec_poly_inputs, exec_comm_inputs) = {
        let exec_inputs = exec_inputs_list.clone().into_iter().flatten().collect();
        // create a multilinear polynomial using the supplied assignment for variables
        let exec_poly_inputs = DensePolynomial::new(exec_inputs);

        // produce a commitment to the satisfying assignment
        let (exec_comm_inputs, _blinds_inputs) = exec_poly_inputs.commit(&vars_gens.gens_pc, None);

        // add the commitment to the prover's transcript
        exec_comm_inputs.append_to_transcript(b"poly_commitment", transcript);
        (exec_poly_inputs, exec_comm_inputs)
      };

      (
        block_poly_vars_list,
        block_comm_vars_list,
        vec![exec_poly_inputs],
        vec![exec_comm_inputs]
      )
    };
    let (
      poly_init_phy_mems,
      _comm_init_phy_mems,
    ) = {
      if total_num_init_phy_mem_accesses > 0 {
        let (poly_init_mems, comm_init_mems) = {
          let init_mems = init_phy_mems_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let poly_init_mems = DensePolynomial::new(init_mems);

          // produce a commitment to the satisfying assignment
          let (comm_init_mems, _blinds_inputs) = poly_init_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          comm_init_mems.append_to_transcript(b"poly_commitment", transcript);
          (poly_init_mems, comm_init_mems)
        };
        (
          vec![poly_init_mems], 
          vec![comm_init_mems],
        )
      } else {
        (
          Vec::new(),
          Vec::new(),
        )
      }
    };
    let (
      poly_init_vir_mems,
      _comm_init_vir_mems,
    ) = {
      if total_num_init_vir_mem_accesses > 0 {
        let (poly_init_mems, comm_init_mems) = {
          let init_mems = init_vir_mems_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let poly_init_mems = DensePolynomial::new(init_mems);

          // produce a commitment to the satisfying assignment
          let (comm_init_mems, _blinds_inputs) = poly_init_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          comm_init_mems.append_to_transcript(b"poly_commitment", transcript);
          (poly_init_mems, comm_init_mems)
        };
        (
          vec![poly_init_mems], 
          vec![comm_init_mems],
        )
      } else {
        (
          Vec::new(),
          Vec::new(),
        )
      }
    };
    
    let (
      addr_poly_phy_mems,
      addr_comm_phy_mems,
      addr_phy_mems_shifted_prover,
      addr_comm_phy_mems_shifted,
    ) = {
      if total_num_phy_mem_accesses > 0 {
        let (addr_poly_phy_mems, addr_comm_phy_mems) = {
          let addr_phy_mems = addr_phy_mems_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_phy_mems = DensePolynomial::new(addr_phy_mems);

          // produce a commitment to the satisfying assignment
          let (addr_comm_phy_mems, _blinds_inputs) = addr_poly_phy_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          addr_comm_phy_mems.append_to_transcript(b"poly_commitment", transcript);
          (addr_poly_phy_mems, addr_comm_phy_mems)
        };
        // Remove the first entry and shift the remaining entries up by one
        // Used later by coherence check
        let (addr_phy_mems_shifted_prover, addr_comm_phy_mems_shifted) = if compact_shift {
          (ProverWitnessSecInfo:: dummy(), PolyCommitment::empty())
        } else {
          let addr_phy_mems_shifted = [addr_phy_mems_list[1..].to_vec().clone().into_iter().flatten().collect(), vec![ZERO; PHY_MEM_WIDTH]].concat();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_phy_mems_shifted = DensePolynomial::new(addr_phy_mems_shifted);

          // produce a commitment to the satisfying assignment
          let (addr_comm_phy_mems_shifted, _blinds_inputs) = addr_poly_phy_mems_shifted.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          addr_comm_phy_mems_shifted.append_to_transcript(b"poly_commitment", transcript);

          let addr_phy_mems_shifted_prover = ProverWitnessSecInfo::new(vec![[addr_phy_mems_list[1..].to_vec(), vec![vec![ZERO; PHY_MEM_WIDTH]]].concat()], vec![addr_poly_phy_mems_shifted]);

          (addr_phy_mems_shifted_prover, addr_comm_phy_mems_shifted)
        };
        (
          vec![addr_poly_phy_mems], 
          addr_comm_phy_mems,
          addr_phy_mems_shifted_prover, 
          addr_comm_phy_mems_shifted,
        )
      } else {
        (
          Vec::new(),
          PolyCommitment::empty(),
          ProverWitnessSecInfo::dummy(),
          PolyCommitment::empty()
        )
      }
    };
    let (
      addr_poly_vir_mems,
      addr_comm_vir_mems,
      addr_vir_mems_shifted_prover,
      addr_comm_vir_mems_shifted,
      addr_ts_bits_prover,
      addr_comm_ts_bits,
    ) = {
      if total_num_vir_mem_accesses > 0 {
        let (addr_poly_vir_mems, addr_comm_vir_mems) = {
          let addr_vir_mems = addr_vir_mems_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_vir_mems = DensePolynomial::new(addr_vir_mems);

          // produce a commitment to the satisfying assignment
          let (addr_comm_vir_mems, _blinds_inputs) = addr_poly_vir_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          addr_comm_vir_mems.append_to_transcript(b"poly_commitment", transcript);
          (addr_poly_vir_mems, addr_comm_vir_mems)
        };
        // Remove the first entry and shift the remaining entries up by one
        // Used later by coherence check
        let (addr_vir_mems_shifted_prover, addr_comm_vir_mems_shifted) = if compact_shift {
          (ProverWitnessSecInfo:: dummy(), PolyCommitment::empty())
        } else {
          let addr_vir_mems_shifted = [addr_vir_mems_list[1..].to_vec().clone().into_iter().flatten().collect(), vec![ZERO; VIR_MEM_WIDTH]].concat();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_vir_mems_shifted = DensePolynomial::new(addr_vir_mems_shifted);

          // produce a commitment to the satisfying assignment
          let (addr_comm_vir_mems_shifted, _blinds_inputs) = addr_poly_vir_mems_shifted.commit(&vars_gens.gens_pc, None);
          // add the commitment to the prover's transcript
          addr_comm_vir_mems_shifted.append_to_transcript(b"poly_commitment", transcript);

          let addr_vir_mems_shifted_prover = ProverWitnessSecInfo::new(vec![[addr_vir_mems_list[1..].to_vec(), vec![vec![ZERO; VIR_MEM_WIDTH]]].concat()], vec![addr_poly_vir_mems_shifted]);
          (addr_vir_mems_shifted_prover, addr_comm_vir_mems_shifted)
        };
        let (addr_ts_bits_prover, addr_comm_ts_bits) = {
          let addr_ts_bits = addr_ts_bits_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_ts_bits = DensePolynomial::new(addr_ts_bits);

          // produce a commitment to the satisfying assignment
          let (addr_comm_ts_bits, _blinds_inputs) = addr_poly_ts_bits.commit(&vars_gens.gens_pc, None);
          // add the commitment to the prover's transcript
          addr_comm_ts_bits.append_to_transcript(b"poly_commitment", transcript);

          let addr_ts_bits_prover = ProverWitnessSecInfo::new(vec![addr_ts_bits_list], vec![addr_poly_ts_bits]);
          (addr_ts_bits_prover, addr_comm_ts_bits)
        };
        (
          vec![addr_poly_vir_mems], 
          addr_comm_vir_mems,
          addr_vir_mems_shifted_prover, 
          addr_comm_vir_mems_shifted,
          addr_ts_bits_prover,
          addr_comm_ts_bits
        )
      } else {
        (
          Vec::new(),
          PolyCommitment::empty(),
          ProverWitnessSecInfo::dummy(),
          PolyCommitment::empty(),
          ProverWitnessSecInfo::dummy(),
          PolyCommitment::empty()
        )
      }
    };
    let block_vars_prover = ProverWitnessSecInfo::new(block_vars_mat, block_poly_vars_list);
    let exec_inputs_prover = ProverWitnessSecInfo::new(vec![exec_inputs_list], exec_poly_inputs);
    let init_phy_mems_prover = if total_num_init_phy_mem_accesses > 0 {
      ProverWitnessSecInfo::new(vec![init_phy_mems_list.clone()], poly_init_phy_mems)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    let init_vir_mems_prover = if total_num_init_vir_mem_accesses > 0 {
      ProverWitnessSecInfo::new(vec![init_vir_mems_list.clone()], poly_init_vir_mems)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    let addr_phy_mems_prover = if total_num_phy_mem_accesses > 0 {
      ProverWitnessSecInfo::new(vec![addr_phy_mems_list.clone()], addr_poly_phy_mems)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    let addr_vir_mems_prover = if total_num_vir_mem_accesses > 0 {
      ProverWitnessSecInfo::new(vec![addr_vir_mems_list.clone()], addr_poly_vir_mems)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    timer_commit.stop();

    // --
    // BLOCK_CORRECTNESS_EXTRACT
    // --
    let timer_proof = Timer::new("Block Correctness Extract");
    let block_wit_secs = if compact_shift {
      vec![&block_vars_prover, &block_w2_prover, &perm_r_prover, &block_w3_prover]
    } else {
      vec![&block_vars_prover, &block_w2_prover, &perm_r_prover, &block_w3_prover, &block_w3_shifted_prover]
    };
    let (block_r1cs_sat_proof, block_challenges) = {
      let (proof, block_challenges) = {
        R1CSProof::prove(
          block_num_circuits,
          block_max_num_proofs,
          block_num_proofs,
          num_vars,
          block_wit_secs,
          &block_inst.inst,
          &vars_gens,
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, block_challenges)
    };

    // Final evaluation on BLOCK
    let (block_inst_evals_bound_rp, block_inst_evals_list, block_r1cs_eval_proof_list) = {
      let [rp, _, rx, ry] = block_challenges;
      let timer_eval = Timer::new("eval_sparse_polys");
      // RP-bound evaluation is truncated
      let inst_evals_bound_rp = block_inst.inst.multi_evaluate_bound_rp::<true>(compact_shift, &rp, &rx, &ry, 1);

      let (inst_evals_list, r1cs_eval_proof_list) = if sparse_commit {
        // Per instance evaluation is untruncated
        let inst_evals_list = block_inst_untruncated.inst.multi_evaluate::<true>(compact_shift, &rx, &ry);

        for r in &inst_evals_list {
          r.append_to_transcript(b"ABCr_claim", transcript);
        }
        // Sample random combinations of A, B, C for inst_evals_bound_rp check in the Verifier
        // The random values are not used by the prover, but need to be appended to the transcript
        let _ = transcript.challenge_scalar(b"challenge_c0");
        let _ = transcript.challenge_scalar(b"challenge_c1");
        let _ = transcript.challenge_scalar(b"challenge_c2");
        
        let r1cs_eval_proof_list = {
          let mut r1cs_eval_proof_list = Vec::new();
          for i in 0..block_comm_list.len() {
            let proof = R1CSEvalProof::prove::<true>(
              compact_shift,
              &block_decomm_list[i].decomm,
              &rx,
              &ry,
              &block_comm_map[i].iter().map(|i| inst_evals_list[*i]).collect(),
              &block_gens.gens_r1cs_eval,
              transcript,
              &mut random_tape,
            );
            let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
            Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
            
            r1cs_eval_proof_list.push(proof);
          }
          r1cs_eval_proof_list
        };
        (inst_evals_list, r1cs_eval_proof_list)
      } else {
        (Vec::new(), Vec::new())
      };
      timer_eval.stop();

      ([inst_evals_bound_rp.0, inst_evals_bound_rp.1, inst_evals_bound_rp.2], inst_evals_list, r1cs_eval_proof_list)
    };
    timer_proof.stop();

    // --
    // PAIRWISE_CHECK
    // --
    let timer_proof = Timer::new("Pairwise Check");
    // Truncate the witness
    let (
      pairwise_prover_w0, 
      pairwise_prover_w1, 
      pairwise_prover_w2, 
      pairwise_prover_w4, 
      pairwise_num_proofs
    ) = {
      let mut pairwise_num_proofs = vec![consis_num_proofs];
      let dummy_w = ProverWitnessSecInfo::pad();
      // perm_root_consis
      let mut w0_concat = vec![&exec_inputs_prover];
      let mut w1_concat = vec![&perm_exec_w2_prover];
      let mut w2_concat = vec![&perm_exec_w3_prover];
      let mut w4_concat = vec![&perm_exec_w3_shifted_prover];
      // phy_mem_cohere
      if total_num_phy_mem_accesses > 0 {
        pairwise_num_proofs.push(total_num_phy_mem_accesses);
        w0_concat.push(&addr_phy_mems_prover);
        w1_concat.push(if compact_shift { &dummy_w } else { &addr_phy_mems_shifted_prover });
        w2_concat.push(&dummy_w);
        w4_concat.push(&dummy_w);
      }
      // vir_mem_cohere
      if total_num_vir_mem_accesses > 0 {
        pairwise_num_proofs.push(total_num_vir_mem_accesses);
        w0_concat.push(&addr_ts_bits_prover);
        w1_concat.push(&addr_vir_mems_prover);
        w2_concat.push(if compact_shift { &dummy_w } else { &addr_vir_mems_shifted_prover });
        w4_concat.push(&dummy_w);
      }
      // perm_root_mem
      if total_num_init_phy_mem_accesses > 0 {
        pairwise_num_proofs.push(total_num_init_phy_mem_accesses);
        w0_concat.push(&init_phy_mems_prover);
        w1_concat.push(&init_phy_mem_w2_prover);
        w2_concat.push(&init_phy_mem_w3_prover);
        w4_concat.push(&init_phy_mem_w3_shifted_prover);
      }
      if total_num_init_vir_mem_accesses > 0 {
        pairwise_num_proofs.push(total_num_init_vir_mem_accesses);
        w0_concat.push(&init_vir_mems_prover);
        w1_concat.push(&init_vir_mem_w2_prover);
        w2_concat.push(&init_vir_mem_w3_prover);
        w4_concat.push(&init_vir_mem_w3_shifted_prover);
      }
      if total_num_phy_mem_accesses > 0 {
        pairwise_num_proofs.push(total_num_phy_mem_accesses);
        w0_concat.push(&addr_phy_mems_prover);
        w1_concat.push(&phy_mem_addr_w2_prover);
        w2_concat.push(&phy_mem_addr_w3_prover);
        w4_concat.push(&phy_mem_addr_w3_shifted_prover);
      }
      if total_num_vir_mem_accesses > 0 {
        pairwise_num_proofs.push(total_num_vir_mem_accesses);
        w0_concat.push(&addr_vir_mems_prover);
        w1_concat.push(&vir_mem_addr_w2_prover);
        w2_concat.push(&vir_mem_addr_w3_prover);
        w4_concat.push(&vir_mem_addr_w3_shifted_prover);
      }
      (
        ProverWitnessSecInfo::concat(w0_concat),
        ProverWitnessSecInfo::concat(w1_concat),
        ProverWitnessSecInfo::concat(w2_concat),
        ProverWitnessSecInfo::concat(w4_concat),
        pairwise_num_proofs,
      )
    };
    let pairwise_witness_sec = if compact_shift {
      vec![&pairwise_prover_w0, &pairwise_prover_w1, &pairwise_prover_w2, &perm_r_prover]
    } else {
      vec![&pairwise_prover_w0, &pairwise_prover_w1, &pairwise_prover_w2, &perm_r_prover, &pairwise_prover_w4]
    };
    let pairwise_max_num_proofs = pairwise_num_proofs.iter().max().unwrap().clone();
    let pairwise_num_circuits = pairwise_num_proofs.len();

    let (pairwise_check_r1cs_sat_proof, pairwise_check_challenges) = {
      let (proof, pairwise_check_challenges) = {
        R1CSProof::prove(
          pairwise_num_circuits,
          pairwise_max_num_proofs,
          &pairwise_num_proofs,
          max(num_ios, mem_addr_ts_bits_size),
          pairwise_witness_sec,
          &pairwise_check_inst.inst,
          &vars_gens,
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, pairwise_check_challenges)
    };

    // Final evaluation on PAIRWISE_CHECK
    let pairwise_check_inst_evals_bound_rp = {
      let [rp, _, rx, ry] = pairwise_check_challenges;
      let timer_eval = Timer::new("eval_sparse_polys");

      // RP-bound evaluation
      let inst_evals_bound_rp = pairwise_check_inst.inst.multi_evaluate_bound_rp::<false>(compact_shift, &rp, &rx, &ry, 1);
      // No commitment opening, verifier directly opens polynomial
      timer_eval.stop();
      [inst_evals_bound_rp.0, inst_evals_bound_rp.1, inst_evals_bound_rp.2]
    };
    // Correctness of the shift will be handled in SHIFT_PROOFS
    timer_proof.stop();

    // --
    // PERM_PRODUCT_PROOF
    // --
    let timer_proof = Timer::new("Perm Product");
    // Record the prod of exec, blocks, mem_block, & mem_addr
    let (perm_poly_eval_list, proof_eval_perm_poly_prod_list) = {
      let two_b = vec![ONE, ZERO];
      let four_b = vec![ONE, ZERO, ZERO];
      let six_b = vec![ONE, ONE, ZERO];
      let (poly_list, eval_list, r_list) = {
        let mut poly_list = vec![&perm_exec_w3_prover.poly_w[0]];
        let mut eval_list = vec![perm_exec_w3_prover.poly_w[0][2]];
        let mut r_list = vec![&two_b];
        if total_num_init_phy_mem_accesses > 0 {
          poly_list.push(&init_phy_mem_w3_prover.poly_w[0]);
          eval_list.push(init_phy_mem_w3_prover.poly_w[0][2]);
          r_list.push(&two_b);
        }
        if total_num_init_vir_mem_accesses > 0 {
          poly_list.push(&init_vir_mem_w3_prover.poly_w[0]);
          eval_list.push(init_vir_mem_w3_prover.poly_w[0][2]);
          r_list.push(&two_b);
        }
        if total_num_phy_mem_accesses > 0 {
          poly_list.push(&phy_mem_addr_w3_prover.poly_w[0]);
          eval_list.push(phy_mem_addr_w3_prover.poly_w[0][2]);
          r_list.push(&two_b);
        }
        if total_num_vir_mem_accesses > 0 {
          poly_list.push(&vir_mem_addr_w3_prover.poly_w[0]);
          eval_list.push(vir_mem_addr_w3_prover.poly_w[0][2]);
          r_list.push(&two_b);
        }
        poly_list.extend(&block_w3_prover.poly_w);
        eval_list.extend(block_w3_prover.poly_w.iter().map(|p| p[2]));
        r_list.extend(vec![&two_b; block_num_circuits]);
        if max_block_num_phy_ops > 0 {
          poly_list.extend(&block_w3_prover.poly_w);
          eval_list.extend(block_w3_prover.poly_w.iter().map(|p| p[4]));
          r_list.extend(vec![&four_b; block_num_circuits]);
        }
        if max_block_num_vir_ops > 0 {
          poly_list.extend(&block_w3_prover.poly_w);
          eval_list.extend(block_w3_prover.poly_w.iter().map(|p| p[6]));
          r_list.extend(vec![&six_b; block_num_circuits]);
        }
        (poly_list, eval_list, r_list)
      };
      let prod_list = PolyEvalProof::prove_batched_polys(
        &poly_list,
        None,
        r_list,
        &eval_list,
        None,
        &vars_gens.gens_pc,
        transcript,
        &mut random_tape,
      );
      (eval_list, prod_list)
    };
    timer_proof.stop();

    // --
    // SHIFT_PROOFS
    // --
    // Prove in the order of
    // - perm_block_w3 => shift by 4
    // - perm_exec_w3 => shift by 8
    // - (if exist) init_mem_w3 => shift by 8
    // - (if exist) addr_phy_mems => shift by 4
    // - (if exist) phy_mem_addr_w3 => shift by 8
    // - (if exist) addr_vir_mems => shift by 8
    // - (if exist) vir_mem_addr_w3 => shift by 8
    let timer_proof = Timer::new("Shift Proofs");
    let shift_proof = {
      if compact_shift {
        let W = W3_WIDTH;
        // perm_exec_w3
        let mut polys = vec![&perm_exec_w3_prover.poly_w[0]];
        let mut N_list = vec![consis_num_proofs];
        // block_w3
        for (i, poly) in block_w3_prover.poly_w.iter().enumerate() {
          polys.push(poly);
          N_list.push(block_num_proofs[i]);
        }
        // init_phy_mem_w3, init_vir_mem_w3
        if total_num_init_phy_mem_accesses > 0 {
          polys.push(&init_phy_mem_w3_prover.poly_w[0]);
          N_list.push(total_num_init_phy_mem_accesses);
        }
        if total_num_init_vir_mem_accesses > 0 {
          polys.push(&init_vir_mem_w3_prover.poly_w[0]);
          N_list.push(total_num_init_vir_mem_accesses);
        }
        // phy_mem_addr, phy_mem_addr_w3
        if total_num_phy_mem_accesses > 0 {
          polys.extend([&addr_phy_mems_prover.poly_w[0], &phy_mem_addr_w3_prover.poly_w[0]]);
          N_list.extend([total_num_phy_mem_accesses; 2]);
        }
        // vir_mem_addr, vir_mem_addr_w3
        if total_num_vir_mem_accesses > 0 {
          polys.extend([&addr_vir_mems_prover.poly_w[0], &vir_mem_addr_w3_prover.poly_w[0]]);
          N_list.extend([total_num_vir_mem_accesses; 2]);
        }
        let (proof, header, comm_Zr) = PolyEvalProof::prove_row_shift_batched(
          &polys, 
          W, 
          N_list, 
          &vars_gens.gens_pc, 
          transcript, 
          &mut random_tape
        );
        ShiftProofs {
          proof,
          C_orig_evals: comm_Zr.0,
          C_shifted_evals: comm_Zr.1,
          openings: header,
        }
      } else {
        // perm_exec_w3
        let mut orig_polys = vec![&perm_exec_w3_prover.poly_w[0]];
        let mut shifted_polys = vec![&perm_exec_w3_shifted_prover.poly_w[0]];
        let mut header_len_list = vec![6];
        // block_w3
        for poly in &block_w3_prover.poly_w {
          orig_polys.push(poly);
        }
        for poly in &block_w3_shifted_prover.poly_w {
          shifted_polys.push(poly);
        }
        header_len_list.extend(vec![8; block_num_circuits]);
        // init_phy_mem_w3, init_vir_mem_w3
        if total_num_init_phy_mem_accesses > 0 {
          orig_polys.push(&init_phy_mem_w3_prover.poly_w[0]);
          shifted_polys.push(&init_phy_mem_w3_shifted_prover.poly_w[0]);
          header_len_list.push(6);
        }
        if total_num_init_vir_mem_accesses > 0 {
          orig_polys.push(&init_vir_mem_w3_prover.poly_w[0]);
          shifted_polys.push(&init_vir_mem_w3_shifted_prover.poly_w[0]);
          header_len_list.push(6);
        }
        // addr_phy_mems, phy_mem_addr_w3
        if total_num_phy_mem_accesses > 0 {
          orig_polys.push(&addr_phy_mems_prover.poly_w[0]);
          shifted_polys.push(&addr_phy_mems_shifted_prover.poly_w[0]);
          header_len_list.push(4);
          orig_polys.push(&phy_mem_addr_w3_prover.poly_w[0]);
          shifted_polys.push(&phy_mem_addr_w3_shifted_prover.poly_w[0]);
          header_len_list.push(6);
        }
        // addr_vir_mems, vir_mem_addr_w3
        if total_num_vir_mem_accesses > 0 {
          orig_polys.push(&addr_vir_mems_prover.poly_w[0]);
          shifted_polys.push(&addr_vir_mems_shifted_prover.poly_w[0]);
          header_len_list.push(6);
          orig_polys.push(&vir_mem_addr_w3_prover.poly_w[0]);
          shifted_polys.push(&vir_mem_addr_w3_shifted_prover.poly_w[0]);
          header_len_list.push(6);
        }
        let shift_proof = ShiftProofs::prove(
          orig_polys,
          shifted_polys,
          header_len_list,
          vars_gens,
          transcript,
          &mut random_tape
        );
        shift_proof
      }
    };
    timer_proof.stop();

    // --
    // IO_PROOFS
    // --

    let timer_proof = Timer::new("IO Proofs");
    let io_proof = IOProofs::prove(
      &exec_inputs_prover.poly_w[0],
      num_ios,
      num_inputs_unpadded,
      consis_num_proofs,
      input_block_num,
      output_block_num,
      input_liveness,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      vars_gens,
      transcript,
      &mut random_tape
    );
    timer_proof.stop();

    timer_prove.stop();
    SNARK {
      block_comm_vars_list,
      exec_comm_inputs,
      addr_comm_phy_mems,
      addr_comm_phy_mems_shifted,
      addr_comm_vir_mems,
      addr_comm_vir_mems_shifted,
      addr_comm_ts_bits,

      perm_exec_comm_w2_list,
      perm_exec_comm_w3_list,
      perm_exec_comm_w3_shifted,

      block_comm_w2_list,
      block_comm_w3_list,
      block_comm_w3_list_shifted,

      init_phy_mem_comm_w2,
      init_phy_mem_comm_w3,
      init_phy_mem_comm_w3_shifted,

      init_vir_mem_comm_w2,
      init_vir_mem_comm_w3,
      init_vir_mem_comm_w3_shifted,

      phy_mem_addr_comm_w2,
      phy_mem_addr_comm_w3,
      phy_mem_addr_comm_w3_shifted,

      vir_mem_addr_comm_w2,
      vir_mem_addr_comm_w3,
      vir_mem_addr_comm_w3_shifted,

      block_r1cs_sat_proof,
      block_inst_evals_bound_rp,
      block_inst_evals_list,
      block_r1cs_eval_proof_list,

      pairwise_check_r1cs_sat_proof,
      pairwise_check_inst_evals_bound_rp,

      perm_poly_eval_list,
      proof_eval_perm_poly_prod_list,

      shift_proof,
      io_proof,
    }
  }

  /// A method to verify the SNARK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    sparse_commit: bool,
    compact_shift: bool,

    input_block_num: usize,
    output_block_num: usize,
    input_liveness: &Vec<bool>,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    input_stack: &Vec<[u8; 32]>,
    input_mem: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    max_block_num_phy_ops: usize,
    block_num_phy_ops: &Vec<usize>,
    max_block_num_vir_ops: usize,
    block_num_vir_ops: &Vec<usize>,
    mem_addr_ts_bits_size: usize,

    num_inputs_unpadded: usize,
    // How many variables (witnesses) are used by each block? Round to the next power of 2
    block_num_vars: &Vec<usize>,
    block_num_circuits_bound: usize,

    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_num_cons: usize,
    // Supply inst if not using sparse commit
    block_inst: &mut Instance,
    block_comm_map: &Vec<Vec<usize>>,
    block_comm_list: &Vec<ComputationCommitment>,
    block_gens: &SNARKGens,

    consis_num_proofs: usize,
    total_num_init_phy_mem_accesses: usize,
    total_num_init_vir_mem_accesses: usize,
    total_num_phy_mem_accesses: usize,
    total_num_vir_mem_accesses: usize,
    pairwise_check_num_cons: usize,
    pairwise_check_inst: &mut Instance,
    pairwise_check_comm: &ComputationCommitment,

    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let (proof_commit_size, proof_noncommit_size) = self.compute_size();
    let commit_size = 
      if sparse_commit { 0 } else { bincode::serialize(&block_inst).unwrap().len() } +
      if sparse_commit { bincode::serialize(&block_comm_list).unwrap().len() } else { 0 } + 
      // bincode::serialize(&block_gens).unwrap().len() + 
      bincode::serialize(&pairwise_check_inst).unwrap().len();
      // bincode::serialize(&pairwise_check_comm).unwrap().len() + 
      // bincode::serialize(&pairwise_check_gens).unwrap().len();
    let meta_size = 
      // usize
      19 * std::mem::size_of::<usize>() +
      // Vec<usize> or Vec<Vec<usize>>
      bincode::serialize(block_num_phy_ops).unwrap().len() +
      bincode::serialize(block_num_vir_ops).unwrap().len() +
      bincode::serialize(block_num_vars).unwrap().len() +
      bincode::serialize(block_num_proofs).unwrap().len() +
      bincode::serialize(block_comm_map).unwrap().len() +
      // Other vectors
      bincode::serialize(input).unwrap().len() +
      bincode::serialize(output).unwrap().len();
      // Everything else
      // bincode::serialize(vars_gens).unwrap().len();

    let timer_verify = Timer::new("SNARK::verify");
    transcript.append_protocol_name(SNARK::protocol_name());

    // --
    // ASSERTIONS
    // --
    assert!(0 < consis_num_proofs);
    for p in 0..block_num_circuits_bound {
      assert!(block_num_proofs[p] <= block_max_num_proofs);
    }

    // --
    // COMMITMENTS
    // --
    let input_block_num = Scalar::from(input_block_num as u64);
    let output_block_num = Scalar::from(output_block_num as u64);
    let input: Vec<Scalar> = input.iter().map(|i| Scalar::from_bytes(i).unwrap()).collect();
    let input_stack: Vec<Scalar> = input_stack.iter().map(|i| Scalar::from_bytes(i).unwrap()).collect();
    let input_mem: Vec<Scalar> = input_mem.iter().map(|i| Scalar::from_bytes(i).unwrap()).collect();
    let output: Scalar = Scalar::from_bytes(output).unwrap();
    {
      let timer_commit = Timer::new("inst_commit");
      // Commit public parameters
      Scalar::from(func_input_width as u64).append_to_transcript(b"func_input_width", transcript);
      Scalar::from(input_offset as u64).append_to_transcript(b"input_offset", transcript);
      Scalar::from(output_offset as u64).append_to_transcript(b"output_offset", transcript);
      Scalar::from(output_exec_num as u64).append_to_transcript(b"output_exec_num", transcript);
      Scalar::from(num_ios as u64).append_to_transcript(b"num_ios", transcript);
      for n in block_num_vars {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_vars", transcript);
      }
      Scalar::from(mem_addr_ts_bits_size as u64).append_to_transcript(b"mem_addr_ts_bits_size", transcript);
      Scalar::from(num_inputs_unpadded as u64).append_to_transcript(b"num_inputs_unpadded", transcript);
      Scalar::from(block_num_circuits_bound as u64).append_to_transcript(b"block_num_circuits_bound", transcript);
      Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
      for p in block_num_phy_ops {
        Scalar::from(*p as u64).append_to_transcript(b"block_num_phy_ops", transcript);
      }
      for v in block_num_vir_ops {
        Scalar::from(*v as u64).append_to_transcript(b"block_num_vir_ops", transcript);
      }
      Scalar::from(total_num_init_phy_mem_accesses as u64).append_to_transcript(b"total_num_init_phy_mem_accesses", transcript);
      Scalar::from(total_num_init_vir_mem_accesses as u64).append_to_transcript(b"total_num_init_vir_mem_accesses", transcript);
      Scalar::from(total_num_phy_mem_accesses as u64).append_to_transcript(b"total_num_phy_mem_accesses", transcript);
      Scalar::from(total_num_vir_mem_accesses as u64).append_to_transcript(b"total_num_vir_mem_accesses", transcript);
      
      // commit num_proofs
      Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
      for n in block_num_proofs {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_proofs", transcript);
      }

      // append a commitment to the computation to the transcript
      for b in block_comm_map {
        for l in b {
          Scalar::from(*l as u64).append_to_transcript(b"block_comm_map", transcript);
        }
      }
      for c in block_comm_list {
        c.comm.append_to_transcript(b"block_comm", transcript);
      }
      pairwise_check_comm.comm.append_to_transcript(b"pairwise_comm", transcript);

      // Commit io
      input_block_num.append_to_transcript(b"input_block_num", transcript);
      output_block_num.append_to_transcript(b"output_block_num", transcript);
      input.append_to_transcript(b"input_list", transcript);
      output.append_to_transcript(b"output_list", transcript);

      timer_commit.stop();
    }

    // --
    // INST_TRUNCATE
    // --
    // block_num_circuit is the number of non-zero entries in block_num_proofs
    let timer_truncate = Timer::new("inst_truncate");
    // block
    let block_num_proofs_circuit = block_num_proofs.clone();
    let (block_num_circuits, mut block_num_proofs, block_num_vars, block_num_phy_ops, block_num_vir_ops) = {
      let mut block_num_proofs = Vec::new();
      let mut block_num_vars_t = Vec::new();
      let mut block_num_phy_ops_t = Vec::new();
      let mut block_num_vir_ops_t = Vec::new();
      for i in 0..block_num_proofs_circuit.len() {
        if block_num_proofs_circuit[i] > 0 {
          block_num_proofs.push(block_num_proofs_circuit[i]);
          block_num_vars_t.push(block_num_vars[i]);
          block_num_phy_ops_t.push(block_num_phy_ops[i]);
          block_num_vir_ops_t.push(block_num_vir_ops[i]);
        }
      }
      (block_num_proofs.len(), block_num_proofs, block_num_vars_t, block_num_phy_ops_t, block_num_vir_ops_t)
    };
    if sparse_commit {
      block_inst.truncate(&block_num_proofs_circuit);
    }
    // Pairwise, with only one copy of perm_root_mem
    let pairwise_num_proofs_circuit = vec![
      consis_num_proofs, 
      total_num_phy_mem_accesses, 
      total_num_vir_mem_accesses, 
      *vec![total_num_init_phy_mem_accesses, total_num_init_vir_mem_accesses, total_num_phy_mem_accesses, total_num_vir_mem_accesses].iter().max().unwrap(),
    ];
    pairwise_check_inst.truncate(&pairwise_num_proofs_circuit);

    // --
    // PADDING
    // --
    // Pad entries of block_num_proofs to a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();
    for i in 0..block_num_circuits {
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad exec_inputs, addr_phy_mems, addr_vir_mems with dummys so the length is a power of 2
    let consis_num_proofs = consis_num_proofs.next_power_of_two();
    let total_num_init_phy_mem_accesses = if total_num_init_phy_mem_accesses == 0 { 0 } else { total_num_init_phy_mem_accesses.next_power_of_two() };
    let total_num_init_vir_mem_accesses = if total_num_init_vir_mem_accesses == 0 { 0 } else { total_num_init_vir_mem_accesses.next_power_of_two() };
    let total_num_phy_mem_accesses = if total_num_phy_mem_accesses == 0 { 0 } else { total_num_phy_mem_accesses.next_power_of_two() };
    let total_num_vir_mem_accesses = if total_num_vir_mem_accesses == 0 { 0 } else { total_num_vir_mem_accesses.next_power_of_two() };
    
    // Pad num_proofs with 1 until the next power of 2
    block_num_proofs.extend(vec![1; block_num_circuits.next_power_of_two() - block_num_circuits]);
    let block_num_proofs = &block_num_proofs;
    timer_truncate.stop();

    // --
    // SAMPLE CHALLENGES, COMMIT WITNESSES, & CONSTRUCT WITNESS_SEC_INFO
    // --
    let timer_commit = Timer::new("witness_commit");

    let comb_tau = transcript.challenge_scalar(b"challenge_tau");
    let comb_r = transcript.challenge_scalar(b"challenge_r");

    let (
      perm_r_verifier,
      perm_exec_w2_verifier,
      perm_exec_w3_verifier,
      perm_exec_w3_shifted_verifier,
      
      block_w2_verifier,
      block_w3_verifier,
      block_w3_shifted_verifier,
    ) = {
      // Let the verifier generate perm_r itself
      let mut perm_r = vec![comb_tau];
      let mut r_tmp = comb_r;
      for _ in 1..2 * num_inputs_unpadded {
        perm_r.push(r_tmp);
        r_tmp *= comb_r;
      }
      perm_r.extend(vec![ZERO; num_ios - 2 * num_inputs_unpadded]);
      // create a multilinear polynomial using the supplied assignment for variables
      let perm_poly_r = DensePolynomial::new(perm_r.clone());
      // produce a commitment to the satisfying assignment
      let (perm_comm_r, _blinds_vars) = perm_poly_r.commit(&vars_gens.gens_pc, None);
      // add the commitment to the prover's transcript
      perm_comm_r.append_to_transcript(b"poly_commitment", transcript);

      // perm_exec
      self.perm_exec_comm_w2_list.append_to_transcript(b"poly_commitment", transcript);
      self.perm_exec_comm_w3_list.append_to_transcript(b"poly_commitment", transcript);
      if !compact_shift {
        self.perm_exec_comm_w3_shifted.append_to_transcript(b"poly_commitment", transcript);
      }
      
      // block_w2
      let block_w2_verifier = {
        let block_w2_size_list: Vec<usize> = (0..block_num_circuits).map(|i| (2 * num_inputs_unpadded + 2 * block_num_phy_ops[i] + 4 * block_num_vir_ops[i]).next_power_of_two()).collect();
        for p in 0..block_num_circuits {
          self.block_comm_w2_list[p].append_to_transcript(b"poly_commitment", transcript);
        }
        VerifierWitnessSecInfo::new(block_w2_size_list, &block_num_proofs, self.block_comm_w2_list.clone())
      };
      // block_w3
      for p in 0..block_num_circuits {
        self.block_comm_w3_list[p].append_to_transcript(b"poly_commitment", transcript);
        if !compact_shift {
          self.block_comm_w3_list_shifted[p].append_to_transcript(b"poly_commitment", transcript);
        }
      }
      (
        VerifierWitnessSecInfo::new(vec![num_ios], &vec![1], vec![perm_comm_r.clone()]),
        VerifierWitnessSecInfo::new(vec![num_ios], &vec![consis_num_proofs], vec![self.perm_exec_comm_w2_list.clone()]),
        VerifierWitnessSecInfo::new(vec![if compact_shift { 2 * W3_WIDTH } else { W3_WIDTH }], &vec![consis_num_proofs], vec![self.perm_exec_comm_w3_list.clone()]),
        if compact_shift { VerifierWitnessSecInfo::dummy() } else { VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![consis_num_proofs], vec![self.perm_exec_comm_w3_shifted.clone()]) },
        
        block_w2_verifier,
        VerifierWitnessSecInfo::new(vec![if compact_shift { 2 * W3_WIDTH } else { W3_WIDTH }; block_num_circuits], &block_num_proofs.clone(), self.block_comm_w3_list.clone()),
        if compact_shift { VerifierWitnessSecInfo::dummy() } else { VerifierWitnessSecInfo::new(vec![W3_WIDTH; block_num_circuits], &block_num_proofs.clone(), self.block_comm_w3_list_shifted.clone()) },
      )
    };

    let (
      init_phy_mem_w2_verifier,
      init_phy_mem_w3_verifier,
      init_phy_mem_w3_shifted_verifier
    ) = Self::mem_gen_verifier::<INIT_PHY_MEM_WIDTH,>(
      compact_shift, 
      total_num_init_phy_mem_accesses,
      &self.init_phy_mem_comm_w2,
      &self.init_phy_mem_comm_w3,
      &self.init_phy_mem_comm_w3_shifted,
      transcript,
    );
  
    let (
      init_vir_mem_w2_verifier,
      init_vir_mem_w3_verifier,
      init_vir_mem_w3_shifted_verifier
    ) = Self::mem_gen_verifier::<INIT_VIR_MEM_WIDTH>(
      compact_shift, 
      total_num_init_vir_mem_accesses,
      &self.init_vir_mem_comm_w2,
      &self.init_vir_mem_comm_w3,
      &self.init_vir_mem_comm_w3_shifted,
      transcript,
    );

    let (
      phy_mem_addr_w2_verifier,
      phy_mem_addr_w3_verifier,
      phy_mem_addr_w3_shifted_verifier
    ) = Self::mem_gen_verifier::<PHY_MEM_WIDTH>(
      compact_shift, 
      total_num_phy_mem_accesses,
      &self.phy_mem_addr_comm_w2,
      &self.phy_mem_addr_comm_w3,
      &self.phy_mem_addr_comm_w3_shifted,
      transcript,
    );

    let (
      vir_mem_addr_w2_verifier,
      vir_mem_addr_w3_verifier,
      vir_mem_addr_w3_shifted_verifier
    ) = Self::mem_gen_verifier::<VIR_MEM_WIDTH>(
      compact_shift, 
      total_num_vir_mem_accesses,
      &self.vir_mem_addr_comm_w2,
      &self.vir_mem_addr_comm_w3,
      &self.vir_mem_addr_comm_w3_shifted,
      transcript,
    );

    let (
      block_vars_verifier,
      exec_inputs_verifier,
    ) = {
      // add the commitment to the verifier's transcript
      for p in 0..block_num_circuits {
        self.block_comm_vars_list[p].append_to_transcript(b"poly_commitment", transcript);
      }
      self.exec_comm_inputs[0].append_to_transcript(b"poly_commitment", transcript);
      (
        VerifierWitnessSecInfo::new(block_num_vars, &block_num_proofs, self.block_comm_vars_list.clone()),
        VerifierWitnessSecInfo::new(vec![num_ios], &vec![consis_num_proofs], self.exec_comm_inputs.clone()),
      )
    };

    let init_phy_mems_verifier = {
      if input_stack.len() > 0 {
        assert_eq!(total_num_init_phy_mem_accesses, input_stack.len().next_power_of_two());
        // Let the verifier generate init_mems itself
        let init_stacks = [
          (0..input_stack.len()).map(|i| vec![vec![ONE, ZERO, Scalar::from(i as u64), input_stack[i].clone()], vec![ZERO; INIT_PHY_MEM_WIDTH - 4]].concat()).concat(),
          vec![ZERO; INIT_PHY_MEM_WIDTH * (total_num_init_phy_mem_accesses - input_stack.len())]
        ].concat();
        // create a multilinear polynomial using the supplied assignment for variables
        let poly_init_stacks = DensePolynomial::new(init_stacks.clone());
        // produce a commitment to the satisfying assignment
        let (comm_init_stacks, _blinds_vars) = poly_init_stacks.commit(&vars_gens.gens_pc, None);
        // add the commitment to the prover's transcript
        comm_init_stacks.append_to_transcript(b"poly_commitment", transcript);
        
        VerifierWitnessSecInfo::new(vec![INIT_PHY_MEM_WIDTH], &vec![total_num_init_phy_mem_accesses], vec![comm_init_stacks])
      } else { VerifierWitnessSecInfo::dummy() }
    };
    let init_vir_mems_verifier = {
      if input_mem.len() > 0 {
        assert_eq!(total_num_init_vir_mem_accesses, input_mem.len().next_power_of_two());
        // Let the verifier generate init_mems itself
        let init_mems = [
          (0..input_mem.len()).map(|i| vec![vec![ONE, ZERO, Scalar::from(i as u64), input_mem[i].clone()], vec![ZERO; INIT_VIR_MEM_WIDTH - 4]].concat()).concat(),
          vec![ZERO; INIT_VIR_MEM_WIDTH * (total_num_init_vir_mem_accesses - input_mem.len())]
        ].concat();
        // create a multilinear polynomial using the supplied assignment for variables
        let poly_init_mems = DensePolynomial::new(init_mems.clone());
        // produce a commitment to the satisfying assignment
        let (comm_init_mems, _blinds_vars) = poly_init_mems.commit(&vars_gens.gens_pc, None);
        // add the commitment to the prover's transcript
        comm_init_mems.append_to_transcript(b"poly_commitment", transcript);
        
        VerifierWitnessSecInfo::new(vec![INIT_VIR_MEM_WIDTH], &vec![total_num_init_vir_mem_accesses], vec![comm_init_mems])
      } else { VerifierWitnessSecInfo::dummy() }
    };

    let (
      addr_phy_mems_verifier,
      addr_phy_mems_shifted_verifier
     ) = {
      if total_num_phy_mem_accesses > 0 {
        self.addr_comm_phy_mems.append_to_transcript(b"poly_commitment", transcript);
        let addr_phy_mems_shifted_verifier = if compact_shift {
          VerifierWitnessSecInfo::dummy()
        } else {
          self.addr_comm_phy_mems_shifted.append_to_transcript(b"poly_commitment", transcript);
          VerifierWitnessSecInfo::new(vec![PHY_MEM_WIDTH], &vec![total_num_phy_mem_accesses], vec![self.addr_comm_phy_mems_shifted.clone()])
        };
        (
          VerifierWitnessSecInfo::new(vec![if compact_shift { 2 * PHY_MEM_WIDTH } else { PHY_MEM_WIDTH }], &vec![total_num_phy_mem_accesses], vec![self.addr_comm_phy_mems.clone()]),
          addr_phy_mems_shifted_verifier
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (
      addr_vir_mems_verifier,
      addr_vir_mems_shifted_verifier,
      addr_ts_bits_verifier
     ) = {
      if total_num_vir_mem_accesses > 0 {
        self.addr_comm_vir_mems.append_to_transcript(b"poly_commitment", transcript);
        let addr_vir_mems_shifted_verifier = if compact_shift {
          VerifierWitnessSecInfo::dummy()
        } else {
          self.addr_comm_vir_mems_shifted.append_to_transcript(b"poly_commitment", transcript);
          VerifierWitnessSecInfo::new(vec![VIR_MEM_WIDTH], &vec![total_num_vir_mem_accesses], vec![self.addr_comm_vir_mems_shifted.clone()])
        };
        self.addr_comm_ts_bits.append_to_transcript(b"poly_commitment", transcript);
        (
          VerifierWitnessSecInfo::new(vec![if compact_shift { 2 * VIR_MEM_WIDTH } else { VIR_MEM_WIDTH }], &vec![total_num_vir_mem_accesses], vec![self.addr_comm_vir_mems.clone()]),
          addr_vir_mems_shifted_verifier,
          VerifierWitnessSecInfo::new(vec![mem_addr_ts_bits_size], &vec![total_num_vir_mem_accesses], vec![self.addr_comm_ts_bits.clone()])
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy()
        )
      }
    };
    timer_commit.stop();

    // --
    // BLOCK_CORRECTNESS_EXTRACT
    // --
    {
      let timer_sat_proof = Timer::new("Block Correctness Extract Sat");
      let block_wit_secs = if compact_shift {
        vec![&block_vars_verifier, &block_w2_verifier, &perm_r_verifier, &block_w3_verifier]
      } else {
        vec![&block_vars_verifier, &block_w2_verifier, &perm_r_verifier, &block_w3_verifier, &block_w3_shifted_verifier]
      };
      let block_challenges = self.block_r1cs_sat_proof.verify(
        block_num_circuits,
        block_max_num_proofs,
        block_num_proofs,
        num_vars,
        block_wit_secs,
        block_num_cons,
        &vars_gens,
        &self.block_inst_evals_bound_rp,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Block Correctness Extract Eval");
      // Verify Evaluation on BLOCK
      let [rp, _, rx, ry] = block_challenges;
      
      if sparse_commit {
        for r in &self.block_inst_evals_list {
          r.append_to_transcript(b"ABCr_claim", transcript);
        }
        // Sample random combinations of A, B, C for inst_evals_bound_rp check
        let c0 = transcript.challenge_scalar(b"challenge_c0");
        let c1 = transcript.challenge_scalar(b"challenge_c1");
        let c2 = transcript.challenge_scalar(b"challenge_c2");

        let mut ABC_evals: Vec<Scalar> = (0..block_num_circuits_bound).map(|i| 
          c0 * self.block_inst_evals_list[3 * i] + c1 * self.block_inst_evals_list[3 * i + 1] + c2 * self.block_inst_evals_list[3 * i + 2]
        ).collect();

        for i in 0..block_comm_list.len() {
          self.block_r1cs_eval_proof_list[i].verify::<true>(
            compact_shift,
            &block_comm_list[i].comm,
            &rx,
            &ry,
            &block_comm_map[i].iter().map(|i| self.block_inst_evals_list[*i]).collect(),
            &block_gens.gens_r1cs_eval,
            transcript,
          )?;
        }
        // Permute block_inst_evals_list to the correct order for RP evaluation
        for i in (0..block_num_proofs_circuit.len()).rev() {
          if block_num_proofs_circuit[i] == 0 { ABC_evals.remove(i); }
        }
        // Verify that block_inst_evals_bound_rp is block_inst_evals_list bind rp
        assert_eq!(DensePolynomial::new(ABC_evals).evaluate(&rp), 
          c0 * self.block_inst_evals_bound_rp[0] + c1 * self.block_inst_evals_bound_rp[1] + c2 * self.block_inst_evals_bound_rp[2]
        );
      } else {
        let block_inst_evals_bound_rp = block_inst.inst.multi_evaluate_bound_rp::<false>(compact_shift, &rp, &rx, &ry, 1);
        assert_eq!(block_inst_evals_bound_rp.0, self.block_inst_evals_bound_rp[0]);
        assert_eq!(block_inst_evals_bound_rp.1, self.block_inst_evals_bound_rp[1]);
        assert_eq!(block_inst_evals_bound_rp.2, self.block_inst_evals_bound_rp[2]);
      }
      timer_eval_proof.stop();
    }

    // --
    // PAIRWISE_CHECK
    // --
    {
      let timer_sat_proof = Timer::new("Pairwise Check Sat");

      // Truncate the witness
      let (
        pairwise_verifier_w0, 
        pairwise_verifier_w1, 
        pairwise_verifier_w2, 
        pairwise_verifier_w4, 
        pairwise_num_proofs
      ) = {
        let mut pairwise_num_proofs = vec![consis_num_proofs];
        let dummy_w = VerifierWitnessSecInfo::pad();
        // perm_root_consis
        let mut w0_concat = vec![&exec_inputs_verifier];
        let mut w1_concat = vec![&perm_exec_w2_verifier];
        let mut w2_concat = vec![&perm_exec_w3_verifier];
        let mut w4_concat = vec![&perm_exec_w3_shifted_verifier];
        // phy_mem_cohere
        if total_num_phy_mem_accesses > 0 {
          pairwise_num_proofs.push(total_num_phy_mem_accesses);
          w0_concat.push(&addr_phy_mems_verifier);
          w1_concat.push(if compact_shift { &dummy_w } else { &addr_phy_mems_shifted_verifier });
          w2_concat.push(&dummy_w);
          w4_concat.push(&dummy_w);
        }
        // vir_mem_cohere
        if total_num_vir_mem_accesses > 0 {
          pairwise_num_proofs.push(total_num_vir_mem_accesses);
          w0_concat.push(&addr_ts_bits_verifier);
          w1_concat.push(&addr_vir_mems_verifier);
          w2_concat.push(if compact_shift { &dummy_w } else { &addr_vir_mems_shifted_verifier });
          w4_concat.push(&dummy_w);
        }
        // perm_root_mem
        if total_num_init_phy_mem_accesses > 0 {
          pairwise_num_proofs.push(total_num_init_phy_mem_accesses);
          w0_concat.push(&init_phy_mems_verifier);
          w1_concat.push(&init_phy_mem_w2_verifier);
          w2_concat.push(&init_phy_mem_w3_verifier);
          w4_concat.push(&init_phy_mem_w3_shifted_verifier);
        }
        if total_num_init_vir_mem_accesses > 0 {
          pairwise_num_proofs.push(total_num_init_vir_mem_accesses);
          w0_concat.push(&init_vir_mems_verifier);
          w1_concat.push(&init_vir_mem_w2_verifier);
          w2_concat.push(&init_vir_mem_w3_verifier);
          w4_concat.push(&init_vir_mem_w3_shifted_verifier);
        }
        if total_num_phy_mem_accesses > 0 {
          pairwise_num_proofs.push(total_num_phy_mem_accesses);
          w0_concat.push(&addr_phy_mems_verifier);
          w1_concat.push(&phy_mem_addr_w2_verifier);
          w2_concat.push(&phy_mem_addr_w3_verifier);
          w4_concat.push(&phy_mem_addr_w3_shifted_verifier);
        }
        if total_num_vir_mem_accesses > 0 {
          pairwise_num_proofs.push(total_num_vir_mem_accesses);
          w0_concat.push(&addr_vir_mems_verifier);
          w1_concat.push(&vir_mem_addr_w2_verifier);
          w2_concat.push(&vir_mem_addr_w3_verifier);
          w4_concat.push(&vir_mem_addr_w3_shifted_verifier);
        }
        (
          VerifierWitnessSecInfo::concat(w0_concat),
          VerifierWitnessSecInfo::concat(w1_concat),
          VerifierWitnessSecInfo::concat(w2_concat),
          VerifierWitnessSecInfo::concat(w4_concat),
          pairwise_num_proofs,
        )
      };
      let pairwise_witness_sec = if compact_shift {
        vec![&pairwise_verifier_w0, &pairwise_verifier_w1, &pairwise_verifier_w2, &perm_r_verifier]
      } else {
        vec![&pairwise_verifier_w0, &pairwise_verifier_w1, &pairwise_verifier_w2, &perm_r_verifier, &pairwise_verifier_w4]
      };
      let pairwise_max_num_proofs = pairwise_num_proofs.iter().max().unwrap().clone();
      let pairwise_num_circuits = pairwise_num_proofs.len();

      let pairwise_check_challenges = self.pairwise_check_r1cs_sat_proof.verify(
        pairwise_num_circuits,
        pairwise_max_num_proofs,
        &pairwise_num_proofs,
        max(num_ios, mem_addr_ts_bits_size),
        pairwise_witness_sec,
        pairwise_check_num_cons,
        &vars_gens,
        &self.pairwise_check_inst_evals_bound_rp,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Pairwise Check Eval");
      // Verify Evaluation on CONSIS_CHECK
      let [rp, _, rx, ry] = pairwise_check_challenges;
      let perm_root_repeat = [total_num_init_phy_mem_accesses, total_num_init_vir_mem_accesses, total_num_phy_mem_accesses, total_num_vir_mem_accesses].iter().fold(0, |s, i| s + if *i > 0 { 1 } else { 0 });
      let pairwise_check_inst_evals_bound_rp = pairwise_check_inst.inst.multi_evaluate_bound_rp::<false>(compact_shift, &rp, &rx, &ry, perm_root_repeat);
      assert_eq!(pairwise_check_inst_evals_bound_rp.0, self.pairwise_check_inst_evals_bound_rp[0]);
      assert_eq!(pairwise_check_inst_evals_bound_rp.1, self.pairwise_check_inst_evals_bound_rp[1]);
      assert_eq!(pairwise_check_inst_evals_bound_rp.2, self.pairwise_check_inst_evals_bound_rp[2]);
      // Correctness of the shift will be handled in SHIFT_PROOFS
      timer_eval_proof.stop();
    };

    // --
    // PERM_PRODUCT_PROOF
    // --
    {
      let timer_eval_opening = Timer::new("Perm Product");
      // Verify prod of exec, blocks, mem_block, & mem_addr
      // Compute prod for PERM_EXEC, PERM_BLOCK, MEM_BLOCK, MEM_ADDR
      let mut perm_block_prod = ONE;
      let mut perm_exec_prod = ONE;
      let mut phy_mem_block_prod = ONE;
      let mut phy_mem_addr_prod = ONE;
      let mut vir_mem_block_prod = ONE;
      let mut vir_mem_addr_prod = ONE;

      let two_b = vec![ONE, ZERO];
      let four_b = vec![ONE, ZERO, ZERO];
      let six_b = vec![ONE, ONE, ZERO];
      let (comm_list, num_vars_list, r_list) = {
        let mut p = 0;
        let w3_num_vars = |num_proofs: usize| (num_proofs * if compact_shift { 2 * W3_WIDTH } else { W3_WIDTH }).log_2();
        let mut comm_list = vec![&perm_exec_w3_verifier.comm_w[0]];
        let mut num_vars_list = vec![w3_num_vars(perm_exec_w3_verifier.num_proofs[0])];
        let mut r_list = vec![&two_b];
        perm_exec_prod *= self.perm_poly_eval_list[p];
        p += 1;
        if total_num_init_phy_mem_accesses > 0 {
          comm_list.push(&init_phy_mem_w3_verifier.comm_w[0]);
          num_vars_list.push(w3_num_vars(init_phy_mem_w3_verifier.num_proofs[0]));
          r_list.push(&two_b);
          phy_mem_block_prod *= self.perm_poly_eval_list[p];
          p += 1;
        }
        if total_num_init_vir_mem_accesses > 0 {
          comm_list.push(&init_vir_mem_w3_verifier.comm_w[0]);
          num_vars_list.push(w3_num_vars(init_vir_mem_w3_verifier.num_proofs[0]));
          r_list.push(&two_b);
          vir_mem_block_prod *= self.perm_poly_eval_list[p];
          p += 1;
        }
        if total_num_phy_mem_accesses > 0 {
          comm_list.push(&phy_mem_addr_w3_verifier.comm_w[0]);
          num_vars_list.push(w3_num_vars(phy_mem_addr_w3_verifier.num_proofs[0]));
          r_list.push(&two_b);
          phy_mem_addr_prod *= self.perm_poly_eval_list[p];
          p += 1;
        }
        if total_num_vir_mem_accesses > 0 {
          comm_list.push(&vir_mem_addr_w3_verifier.comm_w[0]);
          num_vars_list.push(w3_num_vars(vir_mem_addr_w3_verifier.num_proofs[0]));
          r_list.push(&two_b);
          vir_mem_addr_prod *= self.perm_poly_eval_list[p];
          p += 1;
        }
        comm_list.extend(&block_w3_verifier.comm_w);
        num_vars_list.extend(block_w3_verifier.num_proofs.iter().map(|np| w3_num_vars(*np)));
        r_list.extend(vec![&two_b; block_num_circuits]);
        for _ in 0..block_num_circuits {
          perm_block_prod *= self.perm_poly_eval_list[p];
          p += 1;
        }
        if max_block_num_phy_ops > 0 {
          comm_list.extend(&block_w3_verifier.comm_w);
          num_vars_list.extend(block_w3_verifier.num_proofs.iter().map(|np| w3_num_vars(*np)));
          r_list.extend(vec![&four_b; block_num_circuits]);
          for _ in 0..block_num_circuits {
            phy_mem_block_prod *= self.perm_poly_eval_list[p];
            p += 1;
          }
        }
        if max_block_num_vir_ops > 0 {
          comm_list.extend(&block_w3_verifier.comm_w);
          num_vars_list.extend(block_w3_verifier.num_proofs.iter().map(|np| w3_num_vars(*np)));
          r_list.extend(vec![&six_b; block_num_circuits]);
          for _ in 0..block_num_circuits {
            vir_mem_block_prod *= self.perm_poly_eval_list[p];
            p += 1;
          }
        }
        (comm_list, num_vars_list, r_list)
      };
      PolyEvalProof::verify_plain_batched_polys(
        &self.proof_eval_perm_poly_prod_list,
        &vars_gens.gens_pc,
        transcript,
        r_list,
        &self.perm_poly_eval_list,
        &comm_list,
        &num_vars_list
      )?;
      
      // Correctness of Permutation
      assert_eq!(perm_block_prod, perm_exec_prod);
      // Correctness of Memory
      assert_eq!(phy_mem_block_prod, phy_mem_addr_prod);
      assert_eq!(vir_mem_block_prod, vir_mem_addr_prod);
      timer_eval_opening.stop();
    };

    // --
    // SHIFT_PROOFS
    // --
    let timer_proof = Timer::new("Shift Proofs");
    if compact_shift {
      let W = W3_WIDTH;
      // perm_exec_w3
      let mut comms = vec![&perm_exec_w3_verifier.comm_w[0]];
      let mut N_list = vec![consis_num_proofs];
      // block_w3
      for (i, comm) in block_w3_verifier.comm_w.iter().enumerate() {
        comms.push(comm);
        N_list.push(block_num_proofs[i])
      }
      // init_phy_mem_w3, init_vir_mem_w3
      if total_num_init_phy_mem_accesses > 0 {
        comms.push(&init_phy_mem_w3_verifier.comm_w[0]);
        N_list.push(total_num_init_phy_mem_accesses);
      }
      if total_num_init_vir_mem_accesses > 0 {
        comms.push(&init_vir_mem_w3_verifier.comm_w[0]);
        N_list.push(total_num_init_vir_mem_accesses);
      }
      // phy_mem_addr, phy_mem_addr_w3
      if total_num_phy_mem_accesses > 0 {
        comms.extend([&addr_phy_mems_verifier.comm_w[0], &phy_mem_addr_w3_verifier.comm_w[0]]);
        N_list.extend([total_num_phy_mem_accesses; 2]);
      }
      // vir_mem_addr, vir_mem_addr_w3
      if total_num_vir_mem_accesses > 0 {
        comms.extend([&addr_vir_mems_verifier.comm_w[0], &vir_mem_addr_w3_verifier.comm_w[0]]);
        N_list.extend([total_num_vir_mem_accesses; 2]);
      }
      self.shift_proof.proof.verify_row_shift_batched(
        &comms,
        W,
        N_list,
        &self.shift_proof.openings,
        (&self.shift_proof.C_orig_evals, &self.shift_proof.C_shifted_evals),
        &vars_gens.gens_pc, 
        transcript,
      )?;
    } else {
      // perm_exec_w3
      let mut orig_comms = vec![&perm_exec_w3_verifier.comm_w[0]];
      let mut shifted_comms = vec![&perm_exec_w3_shifted_verifier.comm_w[0]];
      // block_w3
      for comm in &block_w3_verifier.comm_w {
        orig_comms.push(comm);
      }
      for comm in &block_w3_shifted_verifier.comm_w {
        shifted_comms.push(comm);
      }
      let mut poly_size_list = [vec![W3_WIDTH * consis_num_proofs], (0..block_num_circuits).map(|i| W3_WIDTH * block_num_proofs[i]).collect()].concat();
      let mut shift_size_list = [vec![W3_WIDTH], vec![W3_WIDTH; block_num_circuits]].concat();
      let mut header_len_list = [vec![6], vec![8; block_num_circuits]].concat();
      // init_phy_mem_w3, init_vir_mem_w3
      if total_num_init_phy_mem_accesses > 0 {
        orig_comms.push(&init_phy_mem_w3_verifier.comm_w[0]);
        shifted_comms.push(&init_phy_mem_w3_shifted_verifier.comm_w[0]);
        poly_size_list.push(W3_WIDTH * total_num_init_phy_mem_accesses);
        shift_size_list.push(W3_WIDTH);
        header_len_list.push(6);
      }
      if total_num_init_vir_mem_accesses > 0 {
        orig_comms.push(&init_vir_mem_w3_verifier.comm_w[0]);
        shifted_comms.push(&init_vir_mem_w3_shifted_verifier.comm_w[0]);
        poly_size_list.push(W3_WIDTH * total_num_init_vir_mem_accesses);
        shift_size_list.push(W3_WIDTH);
        header_len_list.push(6);
      }
      // addr_phy_mems, phy_mem_addr_w3
      if total_num_phy_mem_accesses > 0 {
        orig_comms.push(&addr_phy_mems_verifier.comm_w[0]);
        shifted_comms.push(&addr_phy_mems_shifted_verifier.comm_w[0]);
        poly_size_list.push(PHY_MEM_WIDTH * total_num_phy_mem_accesses);
        shift_size_list.push(PHY_MEM_WIDTH);
        header_len_list.push(4);
        orig_comms.push(&phy_mem_addr_w3_verifier.comm_w[0]);
        shifted_comms.push(&phy_mem_addr_w3_shifted_verifier.comm_w[0]);
        poly_size_list.push(W3_WIDTH * total_num_phy_mem_accesses);
        shift_size_list.push(W3_WIDTH);
        header_len_list.push(6);
      }
      // addr_vir_mems, vir_mem_addr_w3
      if total_num_vir_mem_accesses > 0 {
        orig_comms.push(&addr_vir_mems_verifier.comm_w[0]);
        shifted_comms.push(&addr_vir_mems_shifted_verifier.comm_w[0]);
        poly_size_list.push(VIR_MEM_WIDTH * total_num_vir_mem_accesses);
        shift_size_list.push(VIR_MEM_WIDTH);
        header_len_list.push(6);
        orig_comms.push(&vir_mem_addr_w3_verifier.comm_w[0]);
        shifted_comms.push(&vir_mem_addr_w3_shifted_verifier.comm_w[0]);
        poly_size_list.push(W3_WIDTH * total_num_vir_mem_accesses);
        shift_size_list.push(W3_WIDTH);
        header_len_list.push(6);
      }

      self.shift_proof.verify(
        orig_comms,
        shifted_comms,
        poly_size_list,
        shift_size_list,
        header_len_list,
        vars_gens,
        transcript
      )?;
    }
    timer_proof.stop();

    // --
    // IO_PROOFS
    // --
    let timer_proof = Timer::new("IO Proofs");
    self.io_proof.verify(
      &self.exec_comm_inputs[0],
      num_ios,
      num_inputs_unpadded,
      consis_num_proofs,
      input_block_num,
      output_block_num,
      input_liveness,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      vars_gens,
      transcript
    )?;
    timer_proof.stop();
    
    timer_verify.stop();

    println!("PROOF NONCOMMIT SIZE: {}", proof_noncommit_size);
    println!("PROOF COMMIT SIZE: {}", proof_commit_size);
    println!("COMMIT SIZE: {}", commit_size);
    println!("META SIZE: {}", meta_size);
    println!("Total Proof Size: {}", proof_commit_size + proof_noncommit_size + commit_size + meta_size);

    Ok(())
  }

}