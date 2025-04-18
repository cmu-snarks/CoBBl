//! Reads in constraints and inputs from zok_tests/constraints and zok_tests/inputs
//! Used as a temporary interface to / from CirC
#![allow(clippy::assertions_on_result_states)]
use std::fs::File;
use std::{io::Read, env};

use libspartan::{instance::Instance, SNARKGens, VarsAssignment, SNARK, InputsAssignment, MemsAssignment};
use merlin::Transcript;
use std::time::*;
use serde::{Serialize, Deserialize};

const TOTAL_NUM_VARS_BOUND: usize = 10000000;

// Everything provided by the frontend
#[derive(Serialize, Deserialize)]
struct CompileTimeKnowledge {
  block_num_circuits: usize,
  num_vars: usize,
  num_inputs_unpadded: usize,
  num_vars_per_block: Vec<usize>,
  block_num_phy_ops: Vec<usize>,
  block_num_vir_ops: Vec<usize>,
  max_ts_width: usize,
  max_addr_width: usize,

  args: Vec<Vec<(Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>)>>,

  input_liveness: Vec<bool>,
  func_input_width: usize,
  input_offset: usize,
  input_block_num: usize,
  output_offset: usize,
  output_block_num: usize
}

impl CompileTimeKnowledge {
  fn deserialize_from_file(benchmark_name: String) -> CompileTimeKnowledge {
    let file_name = format!("../zok_tests/constraints/{}_bin.ctk", benchmark_name);
    let mut f = File::open(file_name).unwrap();
    let mut content: Vec<u8> = Vec::new();
    f.read_to_end(&mut content).unwrap();
    bincode::deserialize(&content).unwrap()
  }
}

// Everything provided by the prover
#[derive(Serialize, Deserialize)]
struct RunTimeKnowledge {
  block_max_num_proofs: usize,
  block_num_proofs: Vec<usize>,
  consis_num_proofs: usize,
  total_num_init_phy_mem_accesses: usize,
  total_num_init_vir_mem_accesses: usize,
  total_num_phy_mem_accesses: usize,
  total_num_vir_mem_accesses: usize,

  block_vars_matrix: Vec<Vec<VarsAssignment>>,
  exec_inputs: Vec<InputsAssignment>,
  init_phy_mems_list: Vec<MemsAssignment>,
  init_vir_mems_list: Vec<MemsAssignment>,
  addr_phy_mems_list: Vec<MemsAssignment>,
  addr_vir_mems_list: Vec<MemsAssignment>,
  addr_ts_bits_list: Vec<MemsAssignment>,

  input: Vec<[u8; 32]>,
  input_stack: Vec<[u8; 32]>,
  input_mem: Vec<[u8; 32]>,
  output: [u8; 32],
  output_exec_num: usize
}

impl RunTimeKnowledge {
  fn deserialize_from_file(benchmark_name: String) -> RunTimeKnowledge {
    let file_name = format!("../zok_tests/inputs/{}_bin.rtk", benchmark_name);
    let mut f = File::open(file_name).unwrap();
    let mut content: Vec<u8> = Vec::new();
    f.read_to_end(&mut content).unwrap();
    bincode::deserialize(&content).unwrap()
  }
}

fn main() {
  let args = env::args().collect::<Vec<String>>();
  let benchmark_name = &args[1];
  let sparse_commit: bool = !args.contains(&format!("--sparse_commit=false"));
  let compact_shift: bool = !args.contains(&format!("--compact_shift=false"));
  // let ctk = CompileTimeKnowledge::read_from_file(benchmark_name.to_string()).unwrap();
  let ctk = CompileTimeKnowledge::deserialize_from_file(benchmark_name.to_string());
  // let rtk = RunTimeKnowledge::read_from_file(benchmark_name.to_string()).unwrap();
  let rtk = RunTimeKnowledge::deserialize_from_file(benchmark_name.to_string());

  // --
  // INSTANCE PREPROCESSING
  // --
  println!("Preprocessing instances...");
  let preprocess_start = Instant::now();
  let block_num_circuits_bound = ctk.block_num_circuits;
  let num_vars = ctk.num_vars;
  // num_inputs_unpadded is the actual size of the input
  let num_inputs_unpadded = ctk.num_inputs_unpadded;
  // num_ios is the width used by all input related computations
  let num_ios = (num_inputs_unpadded * 2).next_power_of_two();
  let block_num_phy_ops = ctk.block_num_phy_ops;
  let block_num_vir_ops = ctk.block_num_vir_ops;
  let max_block_num_phy_ops = *block_num_phy_ops.iter().max().unwrap();
  let max_block_num_vir_ops = *block_num_vir_ops.iter().max().unwrap();

  let mem_addr_ts_bits_size = if ctk.max_addr_width > 0 {
    (5 + ctk.max_ts_width + ctk.max_addr_width).next_power_of_two()
  } else {
    (2 + ctk.max_ts_width).next_power_of_two()
  };

  assert_eq!(num_vars, num_vars.next_power_of_two());
  assert!(ctk.args.len() == block_num_circuits_bound);
  assert!(block_num_phy_ops.len() == block_num_circuits_bound);
  // If output_block_num < block_num_circuits, the prover can cheat by executing the program multiple times
  assert!(ctk.output_block_num >= block_num_circuits_bound);

  println!("Generating Circuits...");
  // --
  // BLOCK INSTANCES
  let (block_num_vars, block_num_cons, block_num_non_zero_entries, block_inst) =
    Instance::gen_block_inst::<true, false>(
      compact_shift,
      block_num_circuits_bound,
      num_vars,
      &ctk.args,
      num_inputs_unpadded,
      &block_num_phy_ops,
      &block_num_vir_ops,
      &ctk.num_vars_per_block,
      &rtk.block_num_proofs,
    );
  // block_inst is used by commitment. Every block has different number of variables
  let (_, _, _, block_inst_for_commit) =
    Instance::gen_block_inst::<true, true>(
      compact_shift,
      block_num_circuits_bound,
      num_vars,
      &ctk.args,
      num_inputs_unpadded,
      &block_num_phy_ops,
      &block_num_vir_ops,
      &ctk.num_vars_per_block,
      &rtk.block_num_proofs,
    );
  println!("Finished Block");

  // Pairwise INSTANCES
  // CONSIS_CHECK & PHY_MEM_COHERE
  let (_, pairwise_check_num_vars, pairwise_check_num_cons, pairwise_check_num_non_zero_entries, pairwise_check_inst_prover) = Instance::gen_pairwise_check_inst::<true, true>(
    compact_shift,
    num_inputs_unpadded, 
    num_ios,
    ctk.max_ts_width,
    ctk.max_addr_width,
    mem_addr_ts_bits_size,
    rtk.consis_num_proofs,
    rtk.total_num_phy_mem_accesses,
    rtk.total_num_vir_mem_accesses,
  );
  let (pairwise_check_num_instances, _, _, _, pairwise_check_inst_verifier) = Instance::gen_pairwise_check_inst::<true, false>(
    compact_shift,
    num_inputs_unpadded, 
    num_ios,
    ctk.max_ts_width,
    ctk.max_addr_width,
    mem_addr_ts_bits_size,
    rtk.consis_num_proofs,
    rtk.total_num_phy_mem_accesses,
    rtk.total_num_vir_mem_accesses,
  );
  println!("Finished Pairwise");

  // --
  // COMMITMENT PREPROCESSING
  // --
  println!("Producing Public Parameters...");
  // produce public parameters
  let block_gens = SNARKGens::new(block_num_cons, block_num_vars, block_num_circuits_bound, block_num_non_zero_entries);
  let pairwise_check_gens = SNARKGens::new(pairwise_check_num_cons, pairwise_check_num_vars, pairwise_check_num_instances, pairwise_check_num_non_zero_entries);
  // Only use one version of gens_r1cs_sat
  let vars_gens = SNARKGens::new(block_num_cons, TOTAL_NUM_VARS_BOUND, block_num_circuits_bound.next_power_of_two(), block_num_non_zero_entries).gens_r1cs_sat;
  
  // create a commitment to the R1CS instance
  println!("Comitting Circuits...");
  // block_comm_map records the sparse_polys committed in each commitment
  // Note that A, B, C are committed separately, so sparse_poly[3*i+2] corresponds to poly C of instance i
  let (block_comm_map, block_comm_list, block_decomm_list) = SNARK::multi_encode(&block_inst_for_commit, &block_gens);
  println!("Finished Block");
  let (pairwise_check_comm, _pairwise_check_decomm) = SNARK::encode(&pairwise_check_inst_verifier, &pairwise_check_gens);
  println!("Finished Pairwise");

  // --
  // WITNESS PREPROCESSING
  // --
  let block_num_proofs = rtk.block_num_proofs;
  let block_vars_matrix = rtk.block_vars_matrix;

  assert!(block_num_proofs.len() <= block_num_circuits_bound);
  assert!(block_vars_matrix.len() <= block_num_circuits_bound);
  let preprocess_time = preprocess_start.elapsed();
  println!("Preprocess time: {}ms", preprocess_time.as_millis());

  println!("Running the proof...");
  // produce a proof of satisfiability
  let mut prover_transcript = Transcript::new(b"snark_example");
  let proof = SNARK::prove(
    sparse_commit,
    compact_shift,
    ctk.input_block_num,
    ctk.output_block_num,
    &ctk.input_liveness,
    ctk.func_input_width,
    ctk.input_offset,
    ctk.output_offset,
    &rtk.input,
    &rtk.output,
    rtk.output_exec_num,
    
    num_vars,
    num_ios,
    max_block_num_phy_ops,
    &block_num_phy_ops,
    max_block_num_vir_ops,
    &block_num_vir_ops,
    mem_addr_ts_bits_size,
    num_inputs_unpadded,
    &ctk.num_vars_per_block,

    block_num_circuits_bound,
    rtk.block_max_num_proofs,
    &block_num_proofs,
    &mut block_inst.clone(),
    &block_comm_map,
    &block_comm_list,
    &block_decomm_list,
    &block_gens,
    
    rtk.consis_num_proofs,
    rtk.total_num_init_phy_mem_accesses,
    rtk.total_num_init_vir_mem_accesses,
    rtk.total_num_phy_mem_accesses,
    rtk.total_num_vir_mem_accesses,
    &mut pairwise_check_inst_prover.clone(),
    &pairwise_check_comm,

    block_vars_matrix,
    rtk.exec_inputs,
    rtk.init_phy_mems_list,
    rtk.init_vir_mems_list,
    rtk.addr_phy_mems_list,
    rtk.addr_vir_mems_list,
    rtk.addr_ts_bits_list,

    &vars_gens,
    &mut prover_transcript,
  );

  println!("Verifying the proof...");
  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof.verify(
    sparse_commit,
    compact_shift,
    ctk.input_block_num,
    ctk.output_block_num,
    &ctk.input_liveness,
    ctk.func_input_width,
    ctk.input_offset,
    ctk.output_offset,
    &rtk.input,
    &rtk.input_stack,
    &rtk.input_mem,
    &rtk.output,
    rtk.output_exec_num,

    num_vars,
    num_ios,
    max_block_num_phy_ops,
    &block_num_phy_ops,
    max_block_num_vir_ops,
    &block_num_vir_ops,
    mem_addr_ts_bits_size,
    num_inputs_unpadded,
    &ctk.num_vars_per_block,
    
    block_num_circuits_bound, 
    rtk.block_max_num_proofs, 
    &block_num_proofs, 
    block_num_cons,
    &mut block_inst.clone(),
    &block_comm_map,
    &block_comm_list,
    &block_gens,

    rtk.consis_num_proofs, 
    rtk.total_num_init_phy_mem_accesses,
    rtk.total_num_init_vir_mem_accesses,
    rtk.total_num_phy_mem_accesses,
    rtk.total_num_vir_mem_accesses,
    pairwise_check_num_cons,
    &mut pairwise_check_inst_verifier.clone(),
    &pairwise_check_comm,

    &vars_gens,
    &mut verifier_transcript
  ).is_ok());
  println!("proof verification successful!");
}
