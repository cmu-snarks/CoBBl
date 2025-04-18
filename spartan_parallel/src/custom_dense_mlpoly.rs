#![allow(clippy::too_many_arguments)]
use crate::{dense_mlpoly::DensePolynomial, math::Math};
use super::scalar::Scalar;

const ZERO: Scalar = Scalar::zero();
const ONE: Scalar = Scalar::one();
const MODE_P: usize = 1;
const MODE_Q: usize = 2;
const MODE_W: usize = 3;
const MODE_X: usize = 4;

// Customized Dense ML Polynomials for Data-Parallelism
// These Dense ML Polys are aimed for space-efficiency by removing the 0s for invalid (p, q, w, x) quadruple

// Dense polynomial with variable order: p, q, w, x
// Used by Z_poly in r1csproof
#[derive(Debug, Clone, Hash)]
pub struct DensePolynomialPqx {
  // All metadata might not be a power of 2
  pub num_instances: usize,
  pub num_proofs: Vec<usize>, // P
  pub num_witness_secs: usize,
  pub num_inputs: Vec<Vec<usize>>, // P x W
  // Indicate whether the value within that witness sec is the same across all proofs (0 to num_proofs.next_power_two())
  // If so, then binding on Q for that witness_sec can be skipped
  // For now, still require the values to be stored in all `num_proofs` copies
  pub single_witness_sec: Vec<bool>,
  pub num_vars_p: usize, // log(P.next_power_of_two())
  pub num_vars_q: usize,
  pub num_vars_w: usize,
  pub num_vars_x: usize,
  pub Z: Vec<Vec<Vec<Vec<Scalar>>>>, // Evaluations of the polynomial in all the 2^num_vars Boolean inputs of order (p, q, w, x)
}

impl DensePolynomialPqx {
  // Assume z_mat is of form (p, q, x), construct DensePoly
  pub fn new(
    z_mat: Vec<Vec<Vec<Vec<Scalar>>>>,
    single_witness_sec: Vec<bool>,
  ) -> Self {
    let num_instances = z_mat.len();
    let num_proofs: Vec<usize> = (0..num_instances).map(|p| z_mat[p].len()).collect();
    let num_witness_secs = z_mat[0][0].len();
    assert_eq!(num_witness_secs, single_witness_sec.len());
    let num_inputs: Vec<Vec<usize>> = (0..num_instances).map(|p| 
      (0..num_witness_secs).map(|w| z_mat[p][0][w].len()).collect()
    ).collect();

    let num_vars_p = num_instances.next_power_of_two().log_2();
    let num_vars_q = num_proofs.iter().max().unwrap().next_power_of_two().log_2();
    let num_vars_w = num_witness_secs.next_power_of_two().log_2();
    let num_vars_x = num_inputs.iter().map(|i| i.iter().max().unwrap()).max().unwrap().next_power_of_two().log_2();
    DensePolynomialPqx {
      num_instances,
      num_proofs,
      num_witness_secs,
      num_inputs,
      single_witness_sec,
      num_vars_p,
      num_vars_q,
      num_vars_w,
      num_vars_x,
      Z: z_mat,
    }
  }

  pub fn len(&self) -> usize {
    return self.num_vars_p.pow2() * self.num_vars_q.pow2() * self.num_vars_w.pow2() * self.num_vars_x.pow2();
  }

  // Given (p, q, w, x) return Z[p][q][w][x], DO NOT CHECK FOR OUT OF BOUND
  pub fn index(&self, p: usize, q: usize, w: usize, x: usize) -> Scalar {
    if self.single_witness_sec[w] {
      return self.Z[0][0][w][x];
    } else {
      return self.Z[p][q][w][x];
    }
  }

  // Given (p, q, w, x) and a mode, return Z[p*][q*][w*][x*]
  // Mode = 1 ==> p* = 2p for low, 2p + 1 for high
  // Mode = 2 ==> q* = 2q for low, 2q + 1
  // Mode = 3 ==> w* = 2w for low, 2w + 1
  // Mode = 4 ==> x* = 2x for low, 2x + 1
  // Assume p*, q*, w*, x* are within bound
  pub fn index_low(&self, p: usize, q: usize, w: usize, x: usize, mode: usize) -> Scalar {
    match mode {
      MODE_P => { if self.num_instances == 1 { self.Z[0][q][w][x] } else if 2 * p >= self.num_instances { ZERO } else { self.Z[2 * p][q][w][x] } }
      MODE_Q => { if 2 * q >= self.num_proofs[p] { ZERO } else { self.Z[p][2 * q][w][x] } },
      MODE_W => { if 2 * w >= self.num_witness_secs { ZERO } else { self.Z[p][q][2 * w][x] } }
      MODE_X => { if 2 * x >= self.num_inputs[p][w] { ZERO } else { self.Z[p][q][w][2 * x] } },
      _ => unreachable!()
    }
  }
  pub fn index_high(&self, p: usize, q: usize, w: usize, x: usize, mode: usize) -> Scalar {
    match mode {
      MODE_P => { if self.num_instances == 1 { self.Z[0][q][w][x] } else if 2 * p + 1 >= self.num_instances { ZERO } else { self.Z[2 * p + 1][q][w][x] } }
      MODE_Q => { if 2 * q + 1 >= self.num_proofs[p] { ZERO } else { self.Z[p][2 * q + 1][w][x] } }
      MODE_W => { if 2 * w + 1 >= self.num_witness_secs { ZERO } else { self.Z[p][q][2 * w + 1][x] } }
      MODE_X => { if 2 * x + 1 >= self.num_inputs[p][w] { ZERO } else { self.Z[p][q][w][2 * x + 1] } }
      _ => unreachable!()
    }
  }

  // Bound a variable to r according to mode
  // Mode = 1 ==> Bound last variable of "p" section to r
  // Mode = 2 ==> Bound last variable of "q" section to r
  // Mode = 3 ==> Bound last variable of "w" section to r
  // Mode = 4 ==> Bound last variable of "x" section to r
  pub fn bound_poly(&mut self, r: &Scalar, mode: usize) {
    match mode {
        MODE_P => { self.bound_poly_p(r); }
        MODE_Q => { self.bound_poly_q(r); }
        MODE_W => { self.bound_poly_w(r); }
        MODE_X => { self.bound_poly_x(r); }
        _ => { panic!("DensePolynomialPqx bound failed: unrecognized mode {}!", mode); }
    }
  }

  // Bound the last variable of "p" section to r
  // We are only allowed to bound "p" if we have bounded the entire q and x section
  pub fn bound_poly_p(&mut self, r: &Scalar) {
    assert!(self.num_vars_p >= 1);
    assert_eq!(self.num_vars_q, 0);
    assert_eq!(self.num_vars_x, 0);
    let new_num_instances = self.num_instances.div_ceil(2);
    for p in 0..new_num_instances {
      for w in 0..self.num_witness_secs {
        let Z_low = self.index_low(p, 0, w, 0, MODE_P);
        let Z_high = self.index_high(p, 0, w, 0, MODE_P);
        self.Z[p][0][w][0] = Z_low + r * (Z_high - Z_low);
      }
    }
    self.num_instances = new_num_instances;
    self.num_vars_p -= 1;
  }

  // Bound the last variable of "q" section to r
  pub fn bound_poly_q(&mut self, r: &Scalar) {
    assert!(self.num_vars_q >= 1);
    for p in 0..self.num_instances {
      let new_num_proofs = self.num_proofs[p].div_ceil(2);
      for w in 0..self.num_witness_secs {
        if !self.single_witness_sec[w] {
          for q in 0..new_num_proofs {
            for x in 0..self.num_inputs[p][w] {
              let Z_low = self.index_low(p, q, w, x, MODE_Q);
              let Z_high = self.index_high(p, q, w, x, MODE_Q);
              self.Z[p][q][w][x] = Z_low + r * (Z_high - Z_low);
            }
          } 
        } else if self.num_proofs[p] == 1 {
          // If singleton witness, only bind once num_proofs[p] reaches 1
          for x in 0..self.num_inputs[p][w] {
            self.Z[p][0][w][x] *= ONE - r;
          }
        }
      }
      self.num_proofs[p] = new_num_proofs;
    }
    self.num_vars_q -= 1;
  }

  // Bound the last variable of "w" section to r
  // We are only allowed to bound "w" if we have bounded the entire x section
  pub fn bound_poly_w(&mut self, r: &Scalar) {
    assert!(self.num_vars_w >= 1);
    assert_eq!(self.num_vars_x, 0);
    // If any witness_sec is single, must bound q first
    assert!(self.num_vars_q == 0 || !self.single_witness_sec.contains(&true));
    let new_num_witness_secs = self.num_witness_secs.div_ceil(2);
    for p in 0..self.num_instances {
      for q in 0..self.num_proofs[p] {
        for w in 0..new_num_witness_secs {
          let Z_low = self.index_low(p, q, w, 0, MODE_W);
          let Z_high = self.index_high(p, q, w, 0, MODE_W);
          self.Z[p][q][w][0] = Z_low + r * (Z_high - Z_low);
        }
      }
    }
    self.num_witness_secs = new_num_witness_secs;
    self.num_vars_w -= 1;
}

  // Bound the last variable of "x" section to r
  pub fn bound_poly_x(&mut self, r: &Scalar) {
    // assert!(self.num_vars_x >= 1);
    for p in 0..self.num_instances {
      for w in 0..self.num_witness_secs {
        let new_num_inputs = self.num_inputs[p][w].div_ceil(2);
        for q in 0..self.num_proofs[p] {
          for x in 0..new_num_inputs {
            let Z_low = self.index_low(p, q, w, x, MODE_X);
            let Z_high = self.index_high(p, q, w, x, MODE_X);
            self.Z[p][q][w][x] = Z_low + r * (Z_high - Z_low);
          }
        }
        self.num_inputs[p][w] = new_num_inputs;
      }
    }
    if self.num_vars_x >= 1 {
      self.num_vars_x -= 1;
    }
  }

  // Bound the entire "p" section to r_p in reverse
  // Must occur after r_q's are bounded
  pub fn bound_poly_vars_rp(&mut self, r_p: &[Scalar]) {
    for r in r_p {
      self.bound_poly_p(r);
    }
  }

  // Bound the entire "q" section to r_q in reverse
  pub fn bound_poly_vars_rq(&mut self, r_q: &[Scalar]) {
    for r in r_q {
      self.bound_poly_q(r);
    }
  }

  // Bound the entire "w" section to r_w in reverse
  pub fn bound_poly_vars_rw(&mut self, r_w: &[Scalar]) {
    for r in r_w {
      self.bound_poly_w(r);
    }
  }

  // Bound the entire "x_rev" section to r_x
  pub fn bound_poly_vars_rx(&mut self, r_x: &[Scalar]) {
    for r in r_x {
      self.bound_poly_x(r);
    }
  }

  pub fn evaluate(&self,
    rp_rev: &Vec<Scalar>,
    rq_rev: &Vec<Scalar>,
    rw_rev: &Vec<Scalar>,
    rx_rev: &Vec<Scalar>,
  ) -> Scalar {
    let mut cl = self.clone();
    cl.bound_poly_vars_rx(rx_rev);
    cl.bound_poly_vars_rw(rw_rev);
    cl.bound_poly_vars_rq(rq_rev);
    cl.bound_poly_vars_rp(rp_rev);
    return cl.index(0, 0, 0, 0);
  }

  // Convert to a (p, q_rev, x_rev) regular dense poly of form (p, q, x)
  pub fn to_dense_poly(&self) -> DensePolynomial {
    let p_space = self.num_vars_p.pow2();
    let q_space = self.num_vars_q.pow2();
    let w_space = self.num_vars_w.pow2();
    let x_space = self.num_vars_x.pow2();

    let mut Z_poly = vec![ZERO; p_space * q_space * w_space * x_space];
    for p in 0..self.num_instances {
      for q in 0..self.num_proofs[p] {
        for w in 0..self.num_witness_secs {
          for x in 0..self.num_inputs[p][w] {
              Z_poly[
                  p * q_space * w_space * x_space
                + q * w_space * x_space
                + w * x_space
                + x
              ] = self.Z[p][q][w][x];
          }
        }
      }
    }
    DensePolynomial::new(Z_poly)
  }
}