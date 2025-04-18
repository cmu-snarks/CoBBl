use std::cmp::{max, min};
use std::collections::HashMap;
use std::iter::zip;

use crate::transcript::AppendToTranscript;

use super::dense_mlpoly::DensePolynomial;
use super::custom_dense_mlpoly::DensePolynomialPqx;
use super::errors::ProofVerifyError;
use super::math::Math;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::sparse_mlpoly::{
  MultiSparseMatPolynomialAsDense, SparseMatEntry, SparseMatPolyCommitment,
  SparseMatPolyCommitmentGens, SparseMatPolyEvalProof, SparseMatPolynomial,
};
use super::timer::Timer;
use flate2::{write::ZlibEncoder, Compression};
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct R1CSInstance {
  // num_circuits DOES NOT need to be a power of 2!
  num_circuits: usize,
  // num_cons and num_vars need to be power of 2
  max_num_cons: usize,
  num_cons: Vec<usize>,
  max_num_vars: usize,
  num_vars: Vec<usize>,
  // List of individual A, B, C for matrix multiplication
  A_list: Vec<SparseMatPolynomial>,
  B_list: Vec<SparseMatPolynomial>,
  C_list: Vec<SparseMatPolynomial>,
}

#[derive(Serialize)]
pub struct R1CSCommitmentGens {
  gens: SparseMatPolyCommitmentGens,
}

impl R1CSCommitmentGens {
  pub fn new(
    label: &'static [u8],
    num_circuits: usize,
    num_cons: usize,
    num_vars: usize,
    num_nz_entries: usize,
  ) -> R1CSCommitmentGens {
    let num_poly_vars_x = num_circuits.log_2() + num_cons.log_2();
    let num_poly_vars_y = num_vars.log_2();
    let gens =
      SparseMatPolyCommitmentGens::new(label, num_poly_vars_x, num_poly_vars_y, num_circuits * num_nz_entries, 3);
    R1CSCommitmentGens { gens }
  }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct R1CSCommitment {
  num_cons: usize,
  num_vars: usize,
  comm: SparseMatPolyCommitment,
}

impl AppendToTranscript for R1CSCommitment {
  fn append_to_transcript(&self, _label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_u64(b"num_cons", self.num_cons as u64);
    transcript.append_u64(b"num_vars", self.num_vars as u64);
    self.comm.append_to_transcript(b"comm", transcript);
  }
}

pub struct R1CSDecommitment {
  num_cons: usize,
  num_vars: usize,
  dense: MultiSparseMatPolynomialAsDense,
}

impl R1CSCommitment {
  pub fn get_num_cons(&self) -> usize {
    self.num_cons
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }
}

impl R1CSInstance {
  pub fn new(
    num_circuits: usize,
    max_num_cons: usize,
    num_cons: Vec<usize>,
    max_num_vars: usize,
    num_vars: Vec<usize>,
    A_list: &Vec<Vec<(usize, usize, Scalar)>>,
    B_list: &Vec<Vec<(usize, usize, Scalar)>>,
    C_list: &Vec<Vec<(usize, usize, Scalar)>>,
  ) -> R1CSInstance {
    Timer::print(&format!("number_of_circuits {num_circuits}"));
    Timer::print(&format!("number_of_constraints {max_num_cons}"));
    Timer::print(&format!("number_of_variables {max_num_vars}"));
    // Timer::print(&format!("number_non-zero_entries_A {}", A.len()));
    // Timer::print(&format!("number_non-zero_entries_B {}", B.len()));
    // Timer::print(&format!("number_non-zero_entries_C {}", C.len()));

    // check that num_cons is a power of 2
    assert_eq!(max_num_cons.next_power_of_two(), max_num_cons);
    for c in &num_cons {
      assert_eq!(c.next_power_of_two(), *c);
      assert!(*c <= max_num_cons);
    }

    // check that num_vars is a power of 2
    assert_eq!(max_num_vars.next_power_of_two(), max_num_vars);
    for v in &num_vars {
      assert_eq!(v.next_power_of_two(), *v);
      assert!(*v <= max_num_vars);
    }

    // check that length of A_list, B_list, C_list are the same
    assert_eq!(A_list.len(), B_list.len());
    assert_eq!(B_list.len(), C_list.len());

    // no errors, so create polynomials
    let mut poly_A_list = Vec::new();
    let mut poly_B_list = Vec::new();
    let mut poly_C_list = Vec::new();

    let mut mat_A = Vec::new();
    let mut mat_B = Vec::new();
    let mut mat_C = Vec::new();

    for inst in 0..A_list.len() {
      let num_poly_vars_x = num_cons[inst].log_2();
      let num_poly_vars_y = num_vars[inst].log_2();

      let A = &A_list[inst];
      let B = &B_list[inst];
      let C = &C_list[inst];
      let list_A = (0..A.len())
        .map(|i| SparseMatEntry::new(A[i].0, A[i].1, A[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let list_B = (0..B.len())
        .map(|i| SparseMatEntry::new(B[i].0, B[i].1, B[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let list_C = (0..C.len())
        .map(|i| SparseMatEntry::new(C[i].0, C[i].1, C[i].2))
        .collect::<Vec<SparseMatEntry>>();
      poly_A_list.push(SparseMatPolynomial::new(
        num_poly_vars_x,
        num_poly_vars_y,
        list_A,
      ));
      poly_B_list.push(SparseMatPolynomial::new(
        num_poly_vars_x,
        num_poly_vars_y,
        list_B,
      ));
      poly_C_list.push(SparseMatPolynomial::new(
        num_poly_vars_x,
        num_poly_vars_y,
        list_C,
      ));
      let mut list_A = (0..A.len())
        .map(|i| SparseMatEntry::new(inst * max_num_cons + A[i].0, A[i].1, A[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let mut list_B = (0..B.len())
        .map(|i| SparseMatEntry::new(inst * max_num_cons + B[i].0, B[i].1, B[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let mut list_C = (0..C.len())
        .map(|i| SparseMatEntry::new(inst * max_num_cons + C[i].0, C[i].1, C[i].2))
        .collect::<Vec<SparseMatEntry>>();
      mat_A.append(&mut list_A);
      mat_B.append(&mut list_B);
      mat_C.append(&mut list_C);
    }

    R1CSInstance {
      num_circuits,
      max_num_cons,
      num_cons: num_cons.clone(),
      max_num_vars,
      num_vars: num_vars.clone(),
      A_list: poly_A_list,
      B_list: poly_B_list,
      C_list: poly_C_list,
    }
  }

  // Permute A_list, B_list, C_list based on index
  // index[i] = j => the original jth entry should now be at the ith position
  pub fn permute(&mut self, num_circuits: usize, index: &Vec<usize>) {
    self.num_circuits = num_circuits;
    self.num_cons = (0..num_circuits).map(|i| self.num_cons[index[i]]).collect();
    self.A_list = (0..num_circuits).map(|i| self.A_list[index[i]].clone()).collect();
    self.B_list = (0..num_circuits).map(|i| self.B_list[index[i]].clone()).collect();
    self.C_list = (0..num_circuits).map(|i| self.C_list[index[i]].clone()).collect();
  }

  // Truncate A, B, C that are never executed
  pub fn truncate(&mut self, num_proofs: &Vec<usize>) {
    for i in (0..num_proofs.len()).rev() {
      if num_proofs[i] == 0 {
        self.num_circuits -= 1;
        self.num_cons.remove(i);
        self.A_list.remove(i);
        self.B_list.remove(i);
        self.C_list.remove(i);
      }
    }
  }

  pub fn get_num_circuits(&self) -> usize {
    self.num_circuits
  }

  pub fn get_num_vars(&self) -> usize {
    self.max_num_vars
  }

  pub fn get_num_cons(&self) -> usize {
    self.max_num_cons
  }

  pub fn get_inst_num_cons(&self) -> &Vec<usize> {
    &self.num_cons
  }

  pub fn get_digest(&self) -> Vec<u8> {
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &self).unwrap();
    encoder.finish().unwrap()
  }

  /*
  pub fn produce_synthetic_r1cs(
    num_circuits: usize,
    num_proofs_list: Vec<usize>,
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
  ) -> (R1CSInstance, Vec<Vec<Vec<Scalar>>>, Vec<Vec<Vec<Scalar>>>) {
    Timer::print(&format!("number_of_circuits {num_circuits}"));
    Timer::print(&format!("number_of_constraints {num_cons}"));
    Timer::print(&format!("number_of_variables {num_vars}"));
    Timer::print(&format!("number_of_inputs {num_inputs}"));

    let mut csprng: OsRng = OsRng;

    // assert everything is power of 2
    assert_eq!((num_circuits.log_2()).pow2(), num_circuits);
    for num_proofs in num_proofs_list {
      assert_eq!((num_proofs.log_2()).pow2(), num_proofs);
    }
    assert_eq!((num_cons.log_2()).pow2(), num_cons);
    assert_eq!((num_vars.log_2()).pow2(), num_vars);

    // find max_num_proofs and min_num_proofs
    let mut max_num_proofs = num_proofs_list[0];
    let mut min_num_proofs = num_proofs_list[0];
    for num_proofs in num_proofs_list {
      if num_proofs > max_num_proofs {
        max_num_proofs = num_proofs;
      }
      if num_proofs < min_num_proofs {
        min_num_proofs = num_proofs;
      }
    }

    // num_inputs + 1 <= num_vars
    assert!(num_inputs < num_vars);

    // z is organized as [vars,1,io]
    let size_z = num_vars + num_inputs + 1;

    // produce a random satisfying assignment for each circuit
    let mut Z_mat = Vec::new();
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();
    for i in 0..num_circuits {
      Z_mat.push(Vec::new());
      let mut Z: Vec<Scalar> = (0..size_z)
        .map(|_i| Scalar::random(&mut csprng))
        .collect::<Vec<Scalar>>();
      Z[num_vars] = Scalar::one();
      Z_mat[i].push(Z);

      // three sparse matrices for each circuit
      let mut A: Vec<SparseMatEntry> = Vec::new();
      let mut B: Vec<SparseMatEntry> = Vec::new();
      let mut C: Vec<SparseMatEntry> = Vec::new();
      let one = Scalar::one();
      for i in 0..num_cons {
        let A_idx = i % size_z;
        let B_idx = (i + 2) % size_z;
        A.push(SparseMatEntry::new(i, A_idx, one));
        B.push(SparseMatEntry::new(i, B_idx, one));
        let AB_val = Z[A_idx] * Z[B_idx];

        let C_idx = (i + 3) % size_z;
        let C_val = Z[C_idx];

        if C_val == Scalar::zero() {
          C.push(SparseMatEntry::new(i, num_vars, AB_val));
        } else {
          C.push(SparseMatEntry::new(
            i,
            C_idx,
            AB_val * C_val.invert().unwrap(),
          ));
        }
      }

      // from A, B, C produce more Z
      for _ in 1..num_proofs_list[i] {

      }

      A_list.push(A);
      B_list.push(B);
      C_list.push(C);

      
    }

    Timer::print(&format!("number_non-zero_entries_A {}", A.len()));
    Timer::print(&format!("number_non-zero_entries_B {}", B.len()));
    Timer::print(&format!("number_non-zero_entries_C {}", C.len()));

    let num_poly_vars_x = num_cons.log_2();
    let num_poly_vars_y = (2 * num_vars).log_2();
    let poly_A = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, A);
    let poly_B = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, B);
    let poly_C = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, C);

    let inst = R1CSInstance {
      num_cons,
      num_vars,
      num_inputs,
      A: poly_A,
      B: poly_B,
      C: poly_C,
    };

    assert!(inst.is_sat(&Z[..num_vars], &Z[num_vars + 1..]));

    (inst, Z[..num_vars].to_vec(), Z[num_vars + 1..].to_vec())
  }

  pub fn is_sat(&self, vars: &Vec<Vec<Vec<Scalar>>>, input: &Vec<Vec<Vec<Scalar>>>) -> bool {
    assert_eq!(vars.len(), self.num_circuits);
    assert_eq!(input.len(), self.num_circuits);

    for p in 0..self.num_circuits {
      assert_eq!(vars[p].len(), input[p].len());
      for q in 0..vars[p].len() {
        let vars = &vars[p][q];
        let input = &input[p][q];
        assert_eq!(vars.len(), self.num_vars);

        let z = {
          let mut z = vars.to_vec();
          z.extend(&vec![Scalar::one()]);
          z.extend(input);
          z
        };

        // verify if Az * Bz - Cz = [0...]
        let Az = self
          .A_list[p]
          .multiply_vec(self.num_cons, self.num_vars, &z);
        let Bz = self
          .B_list[p]
          .multiply_vec(self.num_cons, self.num_vars, &z);
        let Cz = self
          .C_list[p]
          .multiply_vec(self.num_cons, self.num_vars, &z);

        assert_eq!(Az.len(), self.num_cons);
        assert_eq!(Bz.len(), self.num_cons);
        assert_eq!(Cz.len(), self.num_cons);
        let res: usize = (0..self.num_cons)
          .map(|i| usize::from(Az[i] * Bz[i] != Cz[i]))
          .sum();

        if res != 0 { return false };
      }
    }
    return true;
  }
  */

  // Az(p, q, x) <- A(p, x) * z(p, q, x), where we require p for A and z are the same
  // Return Az, Bz, Cz as DensePolynomialPqx
  pub fn multiply_vec_block(
    &self,
    num_circuits: usize,
    num_proofs: Vec<usize>,
    max_num_proofs: usize,
    max_num_inputs: usize,
    max_num_cons: usize,
    num_cons: Vec<usize>,
    z_poly: &DensePolynomialPqx
  ) -> (DensePolynomialPqx, DensePolynomialPqx, DensePolynomialPqx) {
    assert!(self.num_circuits == 1 || self.num_circuits == num_circuits);
    assert_eq!(max_num_cons, self.max_num_cons);
    let mut Az = Vec::new();
    let mut Bz = Vec::new();
    let mut Cz = Vec::new();

    // Non-zero circuits
    for p in 0..num_circuits {
      let p_inst = if self.num_circuits == 1 { 0 } else { p };

      assert!(num_proofs[p] <= max_num_proofs);
      Az.push(vec![Vec::new(); num_proofs[p]]);
      Bz.push(vec![Vec::new(); num_proofs[p]]);
      Cz.push(vec![Vec::new(); num_proofs[p]]);

      for q in 0..num_proofs[p] {
        Az[p][q] = vec![self.A_list[p_inst].multiply_vec_disjoint_rounds(num_cons[p_inst].clone(), max_num_inputs, z_poly, p, q)];
        Bz[p][q] = vec![self.B_list[p_inst].multiply_vec_disjoint_rounds(num_cons[p_inst].clone(), max_num_inputs, z_poly, p, q)];
        Cz[p][q] = vec![self.C_list[p_inst].multiply_vec_disjoint_rounds(num_cons[p_inst].clone(), max_num_inputs, z_poly, p, q)];
      }
    }
    
    (
      DensePolynomialPqx::new(Az, vec![false]),
      DensePolynomialPqx::new(Bz, vec![false]),
      DensePolynomialPqx::new(Cz, vec![false])
    )
  }

  /*
  // Multiply one circuit by a list of inputs
  // Length of each input might be smaller than the length of the circuit,
  // in that case need to append the result by 0
  pub fn multiply_vec_single(
    &self,
    num_circuits: usize,
    num_proofs: &Vec<usize>,
    max_num_proofs_bound: usize,
    max_num_proofs: usize,
    num_rows: usize,
    num_cols: usize,
    z_list: &Vec<Vec<Scalar>>,
  ) -> (DensePolynomialPqx, DensePolynomialPqx, DensePolynomialPqx) {
    assert!(max_num_proofs <= max_num_proofs_bound);
    assert!(max_num_proofs_bound * num_rows <= self.num_cons);
    assert!(max_num_proofs_bound * num_cols <= self.num_vars);

    let mut Az = Vec::new();
    let mut Bz = Vec::new();
    let mut Cz = Vec::new();
    
    // Non-zero circuits
    for p in 0..num_circuits {
      let z = &z_list[p];
      assert!(num_proofs[p] <= max_num_proofs);
      // Each returns a num_proofs[p] * num_rows matrix
      Az.push(self.A_list[0].multiply_vec_pad(max_num_proofs_bound, num_proofs[p], num_rows, num_cols, z));
      Bz.push(self.B_list[0].multiply_vec_pad(max_num_proofs_bound, num_proofs[p], num_rows, num_cols, z));
      Cz.push(self.C_list[0].multiply_vec_pad(max_num_proofs_bound, num_proofs[p], num_rows, num_cols, z));
    }

    (
      DensePolynomialPqx::new_rev(&Az, num_proofs, max_num_proofs),
      DensePolynomialPqx::new_rev(&Bz, num_proofs, max_num_proofs),
      DensePolynomialPqx::new_rev(&Cz, num_proofs, max_num_proofs)
    )
  }
  */

  pub fn compute_eval_table_sparse(
    &self,
    num_circuits: usize,
    num_rows: usize,
    num_cols: usize,
    evals: &[Scalar],
  ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
    assert!(self.num_circuits == 1 || self.num_circuits == num_circuits);
    assert_eq!(num_rows, self.max_num_cons);
    assert_eq!(num_cols, self.max_num_vars);

    let mut evals_A_list = Vec::new();
    let mut evals_B_list = Vec::new();
    let mut evals_C_list = Vec::new();
    // If num_circuits is 1, copy it for num_circuits.next_power_of_two()
    if self.num_circuits == 1 {
      let evals_A = self.A_list[0].compute_eval_table_sparse(evals, num_rows, num_cols);
      let evals_B = self.B_list[0].compute_eval_table_sparse(evals, num_rows, num_cols);
      let evals_C = self.C_list[0].compute_eval_table_sparse(evals, num_rows, num_cols);
      evals_A_list = vec![evals_A; num_circuits.next_power_of_two()].concat();
      evals_B_list = vec![evals_B; num_circuits.next_power_of_two()].concat();
      evals_C_list = vec![evals_C; num_circuits.next_power_of_two()].concat();
    } else {
      // Non-zero circuits
      for p in 0..num_circuits {
        let evals_A = self.A_list[p].compute_eval_table_sparse(evals, num_rows, num_cols);
        let evals_B = self.B_list[p].compute_eval_table_sparse(evals, num_rows, num_cols);
        let evals_C = self.C_list[p].compute_eval_table_sparse(evals, num_rows, num_cols);
        evals_A_list.extend(evals_A);
        evals_B_list.extend(evals_B);
        evals_C_list.extend(evals_C);
      }
      // Zero circuits
      for _ in num_circuits..num_circuits.next_power_of_two() {
        evals_A_list.extend(vec![Scalar::zero(); num_cols]);
        evals_B_list.extend(vec![Scalar::zero(); num_cols]);
        evals_C_list.extend(vec![Scalar::zero(); num_cols]);
      }
    }

    (evals_A_list, evals_B_list, evals_C_list)
  }

  // Store the result in a vector divided into num_segs segments
  // output[p][q][w] stores entry w * max_num_cols ~ w * max_num_cols + num_cols of the original vector
  pub fn compute_eval_table_sparse_disjoint_rounds(
    &self,
    num_circuits: usize,
    num_rows: &Vec<usize>,
    num_segs: usize,
    max_num_cols: usize,
    num_cols: &Vec<Vec<usize>>,
    evals: &[Scalar],
    // Output in p, q, w, i format, where q section has length 1
  ) -> (Vec<Vec<Vec<Vec<Scalar>>>>, Vec<Vec<Vec<Vec<Scalar>>>>, Vec<Vec<Vec<Vec<Scalar>>>>) {
    assert!(self.num_circuits == 1 || self.num_circuits == num_circuits);
    assert_eq!(num_rows, &self.num_cons);
    assert_eq!(num_segs.next_power_of_two() * max_num_cols, self.max_num_vars);

    let mut evals_A_list = Vec::new();
    let mut evals_B_list = Vec::new();
    let mut evals_C_list = Vec::new();
    // Length of output follows self.num_circuits NOT num_circuits!!!
    for p in 0..self.num_circuits {
      let num_cols = *num_cols[p].iter().max().unwrap();
      let evals_A = self.A_list[p].compute_eval_table_sparse_disjoint_rounds(evals, num_rows[p], num_segs, max_num_cols, num_cols);
      let evals_B = self.B_list[p].compute_eval_table_sparse_disjoint_rounds(evals, num_rows[p], num_segs, max_num_cols, num_cols);
      let evals_C = self.C_list[p].compute_eval_table_sparse_disjoint_rounds(evals, num_rows[p], num_segs, max_num_cols, num_cols);
      evals_A_list.push(vec![evals_A]);
      evals_B_list.push(vec![evals_B]);
      evals_C_list.push(vec![evals_C]);
    }

    (evals_A_list, evals_B_list, evals_C_list)
  }


  /*
  // Only compute the first max_num_proofs / max_num_proofs_bound entries
  // num_cols is already num_vars * max_num_proofs / max_num_proofs_bound
  pub fn compute_eval_table_sparse_single(
    &self,
    num_circuits: usize,
    max_num_proofs: usize,
    max_num_proofs_bound: usize,
    num_rows: usize,
    num_cols: usize,
    evals: &[Scalar],
  ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
    assert!(self.num_circuits == 1 || self.num_circuits == num_circuits);
    assert_eq!(num_rows, self.num_cons);
    assert!(num_cols <= self.num_vars * max_num_proofs / max_num_proofs_bound);

    let mut evals_A_list = Vec::new();
    let mut evals_B_list = Vec::new();
    let mut evals_C_list = Vec::new();

    // If num_circuits is 1, copy it for num_circuits.next_power_of_two()
    if self.num_circuits == 1 {
      let evals_A = self.A_list[0].compute_eval_table_sparse_single(evals, max_num_proofs, max_num_proofs_bound, num_rows, num_cols);
      let evals_B = self.B_list[0].compute_eval_table_sparse_single(evals, max_num_proofs, max_num_proofs_bound, num_rows, num_cols);
      let evals_C = self.C_list[0].compute_eval_table_sparse_single(evals, max_num_proofs, max_num_proofs_bound, num_rows, num_cols);
      evals_A_list = vec![evals_A; num_circuits.next_power_of_two()].concat();
      evals_B_list = vec![evals_B; num_circuits.next_power_of_two()].concat();
      evals_C_list = vec![evals_C; num_circuits.next_power_of_two()].concat();
    } else {
      // Non-zero circuits
      for p in 0..num_circuits {
        let evals_A = self.A_list[p].compute_eval_table_sparse_single(evals, max_num_proofs, max_num_proofs_bound, num_rows, num_cols);
        let evals_B = self.B_list[p].compute_eval_table_sparse_single(evals, max_num_proofs, max_num_proofs_bound, num_rows, num_cols);
        let evals_C = self.C_list[p].compute_eval_table_sparse_single(evals, max_num_proofs, max_num_proofs_bound, num_rows, num_cols);
        evals_A_list.extend(evals_A);
        evals_B_list.extend(evals_B);
        evals_C_list.extend(evals_C);
      }
      // Zero circuits
      for _ in num_circuits..num_circuits.next_power_of_two() {
        evals_A_list.extend(vec![Scalar::zero(); num_cols]);
        evals_B_list.extend(vec![Scalar::zero(); num_cols]);
        evals_C_list.extend(vec![Scalar::zero(); num_cols]);
      }
    }

    (evals_A_list, evals_B_list, evals_C_list)
  }
  */

  // If IS_BLOCK, ry is truncated starting at the second or third entry depending on compact_shift
  pub fn multi_evaluate<const IS_BLOCK: bool>(&self, compact_shift: bool, rx: &[Scalar], ry: &[Scalar]) -> Vec<Scalar> {
    let wit_sec_offset = if compact_shift { 2 } else { 3 }; // Separate the first few entries in ry for combining witnesses
    let mut eval_list = Vec::new();
    // Evaluate each individual poly on [rx, ry]
    for i in 0..self.num_circuits {
      let num_cons = self.num_cons[i];
      let num_vars = self.num_vars[i];
      let rx_header = rx[..rx.len() - min(rx.len(), num_cons.log_2())].iter().fold(
        ONE, |c, i| c * (ONE - i.clone())
      );
      let rx_short = &rx[rx.len() - min(rx.len(), num_cons.log_2())..];
      let ry_skip_len = ry.len() - min(ry.len(), num_vars.log_2());
      let (ry_header, ry_short) = {
        if IS_BLOCK {
          let ry_header = ry[wit_sec_offset..wit_sec_offset + ry_skip_len].iter().fold(
            ONE, |c, i| c * (ONE - i.clone())
          );
          let ry_short = [ry[..wit_sec_offset].to_vec(), ry[wit_sec_offset + ry_skip_len..].to_vec()].concat();
          (ry_header, ry_short)
        } else {
          let ry_header = ry[0..ry_skip_len].iter().fold(
            ONE, |c, i| c * (ONE - i.clone())
          );
          let ry_short = ry[ry_skip_len..].to_vec();
          (ry_header, ry_short)
        }
      };

      let evals = SparseMatPolynomial::multi_evaluate(
        &[&self.A_list[i], &self.B_list[i], &self.C_list[i]],
        rx_short,
        &ry_short,
      );
      eval_list.extend(evals.into_iter().map(|i| rx_header * ry_header * i));
    }
    eval_list
  }

  pub fn multi_evaluate_bound_rp<const IS_BLOCK: bool>(
    &self,
    compact_shift: bool,
    rp: &[Scalar],
    rx: &[Scalar],
    ry: &[Scalar],
    last_inst_repeat: usize, // Used by pairwise, number of times perm_root_mem repeats
  ) -> (Scalar, Scalar, Scalar) {
    let wit_sec_offset = if compact_shift { 2 } else { 3 }; // Separate the first few entries in ry for combining witnesses
    let mut a_evals = Vec::new();
    let mut b_evals = Vec::new();
    let mut c_evals = Vec::new();
    // Evaluate each individual poly on [rx, ry]
    for i in 0..self.num_circuits {
      let num_cons = self.num_cons[i];
      let num_vars = self.num_vars[i];
      let rx_header = rx[..rx.len() - min(rx.len(), num_cons.log_2())].iter().fold(
        ONE, |c, i| c * (ONE - i.clone())
      );
      let rx_short = &rx[rx.len() - min(rx.len(), num_cons.log_2())..];
      let ry_skip_len = ry.len() - min(ry.len(), num_vars.log_2());
      let (ry_header, ry_short) = {
        if IS_BLOCK {
          let ry_header = ry[wit_sec_offset..wit_sec_offset + ry_skip_len].iter().fold(
            ONE, |c, i| c * (ONE - i.clone())
          );
          let ry_short = [ry[..wit_sec_offset].to_vec(), ry[wit_sec_offset + ry_skip_len..].to_vec()].concat();
          (ry_header, ry_short)
        } else {
          let ry_header = ry[0..ry_skip_len].iter().fold(
            ONE, |c, i| c * (ONE - i.clone())
          );
          let ry_short = ry[ry_skip_len..].to_vec();
          (ry_header, ry_short)
        }
      };

      let evals = SparseMatPolynomial::multi_evaluate(
        &[&self.A_list[i], &self.B_list[i], &self.C_list[i]],
        rx_short,
        &ry_short,
      );
      let evals: Vec<Scalar> = evals.into_iter().map(|i| rx_header * ry_header * i).collect();
      a_evals.push(evals[0]);
      b_evals.push(evals[1]);
      c_evals.push(evals[2]);
    }
    if last_inst_repeat > 1 {
      let evals_last = a_evals.len() - 1;
      a_evals.extend(vec![a_evals[evals_last]; last_inst_repeat - 1]);
      b_evals.extend(vec![b_evals[evals_last]; last_inst_repeat - 1]);
      c_evals.extend(vec![c_evals[evals_last]; last_inst_repeat - 1]);
    }
    // Bind A, B, C to rp
    let a_eval = DensePolynomial::new(a_evals).evaluate(rp);
    let b_eval = DensePolynomial::new(b_evals).evaluate(rp);
    let c_eval = DensePolynomial::new(c_evals).evaluate(rp);
    let eval_bound_rp = (a_eval, b_eval, c_eval);

    eval_bound_rp
  }

  // Used if there is only one circuit
  pub fn evaluate(&self, rx: &[Scalar], ry: &[Scalar]) -> (Scalar, Scalar, Scalar) {
    assert_eq!(self.num_circuits, 1);

    let evals = SparseMatPolynomial::multi_evaluate(&[&self.A_list[0], &self.B_list[0], &self.C_list[0]], rx, ry);
    (evals[0], evals[1], evals[2])
  }

  pub fn multi_commit(&self, gens: &R1CSCommitmentGens) -> (Vec<Vec<usize>>, Vec<R1CSCommitment>, Vec<R1CSDecommitment>) {
    let mut vars_size: HashMap<usize, usize> = HashMap::new();
    let mut label_map: Vec<Vec<usize>> = Vec::new();
    let mut sparse_polys_list: Vec<Vec<&SparseMatPolynomial>> = Vec::new();
    let mut max_num_cons_list: Vec<usize> = Vec::new();
    let mut max_num_vars_list: Vec<usize> = Vec::new();

    // Group the circuits based on number of variables, which are already orders of 2^4
    for i in 0..self.num_circuits {
      let var_len = self.num_vars[i];
      // A_list, B_list, C_list
      if let Some(index) = vars_size.get(&var_len) {
        label_map[*index].push(3 * i);
        sparse_polys_list[*index].push(&self.A_list[i]);
        label_map[*index].push(3 * i + 1);
        sparse_polys_list[*index].push(&self.B_list[i]);
        label_map[*index].push(3 * i + 2);
        sparse_polys_list[*index].push(&self.C_list[i]);
        max_num_cons_list[*index] = max(max_num_cons_list[*index], self.num_cons[i]);
        max_num_vars_list[*index] = max(max_num_vars_list[*index], self.num_vars[i]);
      } else {
        let next_label = vars_size.len();
        vars_size.insert(var_len, next_label);
        label_map.push(vec![3 * i, 3 * i + 1, 3 * i + 2]);
        sparse_polys_list.push(vec![&self.A_list[i], &self.B_list[i], &self.C_list[i]]);
        max_num_cons_list.push(self.num_cons[i]);
        max_num_vars_list.push(self.num_vars[i]);
      }
    }

    let mut r1cs_comm_list = Vec::new();
    let mut r1cs_decomm_list = Vec::new();
    for ((sparse_polys, max_num_cons), max_num_vars) in zip(zip(sparse_polys_list, max_num_cons_list), max_num_vars_list) {
      let (comm, dense) = SparseMatPolynomial::multi_commit(&sparse_polys, &gens.gens);
      let r1cs_comm = R1CSCommitment {
        num_cons: max_num_cons.next_power_of_two(),
        num_vars: max_num_vars,
        comm,
      };
      let r1cs_decomm = R1CSDecommitment {
        num_cons: max_num_cons.next_power_of_two(),
        num_vars: max_num_vars,
        dense
      };

      r1cs_comm_list.push(r1cs_comm);
      r1cs_decomm_list.push(r1cs_decomm);
    }

    (label_map, r1cs_comm_list, r1cs_decomm_list)
  }

  // Used if there is only one circuit
  pub fn commit(&self, gens: &R1CSCommitmentGens) -> (R1CSCommitment, R1CSDecommitment) {
    let mut sparse_polys = Vec::new();
    for i in 0..self.num_circuits {
      sparse_polys.push(&self.A_list[i]);
      sparse_polys.push(&self.B_list[i]);
      sparse_polys.push(&self.C_list[i]);
    }
    let (comm, dense) = SparseMatPolynomial::multi_commit(&sparse_polys, &gens.gens);
    let r1cs_comm = R1CSCommitment {
      num_cons: self.num_circuits * self.max_num_cons,
      num_vars: self.max_num_vars,
      comm,
    };

    let r1cs_decomm = R1CSDecommitment {
      num_cons: self.num_circuits * self.max_num_cons,
      num_vars: self.max_num_vars,
      dense
    };

    (r1cs_comm, r1cs_decomm)
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct R1CSEvalProof {
  proof: SparseMatPolyEvalProof,
}

const ONE: Scalar = Scalar::one();
impl R1CSEvalProof {
  // If is BLOCK, separate the first 2 or 3 entries of ry out (corresponding to the 5 segments of witnesses)
  pub fn prove<const IS_BLOCK: bool>(
    compact_shift: bool,
    decomm: &R1CSDecommitment,
    rx: &[Scalar], // point at which the polynomial is evaluated
    ry: &[Scalar],
    evals: &Vec<Scalar>,
    gens: &R1CSCommitmentGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> R1CSEvalProof {
    let timer = Timer::new("R1CSEvalProof::prove");
    let wit_sec_offset = if compact_shift { 2 } else { 3 }; // Separate the first few entries in ry for combining witnesses
    let rx_skip_len = rx.len() - min(rx.len(), decomm.num_cons.log_2());
    let rx_header = rx[..rx_skip_len].iter().fold(
      ONE, |c, i| c * (ONE - i.clone())
    );
    let rx_short = &rx[rx_skip_len..];
    let ry_skip_len = ry.len() - min(ry.len(), decomm.num_vars.log_2());
    let (ry_header, ry_short) = {
      if IS_BLOCK {
        let ry_header = ry[wit_sec_offset..wit_sec_offset + ry_skip_len].iter().fold(
          ONE, |c, i| c * (ONE - i.clone())
        );
        let ry_short = [ry[..wit_sec_offset].to_vec(), ry[wit_sec_offset + ry_skip_len..].to_vec()].concat();
        (ry_header, ry_short)
      } else {
        let ry_header = ry[0..ry_skip_len].iter().fold(
          ONE, |c, i| c * (ONE - i.clone())
        );
        let ry_short = ry[ry_skip_len..].to_vec();
        (ry_header, ry_short)
      }
    };
    // let ry_short = &ry[..min(ry.len(), decomm.num_vars.log_2())];
    let proof =
      SparseMatPolyEvalProof::prove(&decomm.dense, rx_header * ry_header, rx_short, &ry_short, evals, &gens.gens, transcript, random_tape);
    timer.stop();

    R1CSEvalProof { proof }
  }

  pub fn verify<const IS_BLOCK: bool>(
    &self,
    compact_shift: bool,
    comm: &R1CSCommitment,
    rx: &[Scalar], // point at which the R1CS matrix polynomials are evaluated
    ry: &[Scalar],
    evals: &Vec<Scalar>,
    gens: &R1CSCommitmentGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let wit_sec_offset = if compact_shift { 2 } else { 3 };
    let rx_header = rx[..rx.len() - min(rx.len(), comm.num_cons.log_2())].iter().fold(
      ONE, |c, i| c * (ONE - i.clone())
    );
    let rx_short = &rx[rx.len() - min(rx.len(), comm.num_cons.log_2())..];
    let ry_skip_len = ry.len() - min(ry.len(), comm.num_vars.log_2());
    let (ry_header, ry_short) = {
      if IS_BLOCK {
        let ry_header = ry[wit_sec_offset..wit_sec_offset + ry_skip_len].iter().fold(
          ONE, |c, i| c * (ONE - i.clone())
        );
        let ry_short = [ry[..wit_sec_offset].to_vec(), ry[wit_sec_offset + ry_skip_len..].to_vec()].concat();
        (ry_header, ry_short)
      } else {
        let ry_header = ry[0..ry_skip_len].iter().fold(
          ONE, |c, i| c * (ONE - i.clone())
        );
        let ry_short = ry[ry_skip_len..].to_vec();
        (ry_header, ry_short)
      }
    };
    self.proof.verify(&comm.comm, rx_header * ry_header, rx_short, &ry_short, evals, &gens.gens, transcript)
  }
}
