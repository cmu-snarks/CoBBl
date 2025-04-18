// Interpret and generate circuit using CirC's own circuit evaluator
const TOTAL_NUM_VARS_BOUND: usize = 10000000000;

use core::cmp::min;
use std::convert::TryInto;
use std::collections::BTreeMap;
use circ::target::r1cs::wit_comp::StagedWitCompEvaluatorBatched;
use rug::{Integer, integer::Order};
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::opt::{opt, Opt};
use circ::front::zsharp::OPT_RO_ARRAYS;
/*
use circ::target::r1cs::bellman::parse_instance;
*/
use circ::target::r1cs::{VarType, Lc};
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
use circ::target::r1cs::ProverData;

use std::fs::File;
use std::io::{BufReader, BufRead, Write};

use circ::cfg::{
    cfg,
    clap::{self, Parser, ValueEnum},
    CircOpt,
};
use circ_fields::FieldT;
use std::path::PathBuf;

use std::time::*;
use serde::{Serialize, Deserialize};
use libspartan::{instance::Instance, SNARKGens, Assignment, VarsAssignment, SNARK, InputsAssignment, MemsAssignment, scalar::Scalar};
use merlin::Transcript;

// How many reserved variables (EXCLUDING V) are in front of the actual input / output?
// %BN, %RET, %TS, %AS, %SP, %BP
const NUM_RESERVED_VARS: usize = 6;
// Which index in the output (INCLUDING V) denotes %RET?
const OUTPUT_OFFSET: usize = 2;
// What is the maximum width (# of bits) of %TS?
const MAX_TS_WIDTH: usize = 20;
// What is the maximum width (# of bits) of %ADDR? Used by opt < 3
const MAX_ADDR_WIDTH: usize = 20;

const ZERO_VEC: [u8; 32] = [0; 32];
const ONE_VEC: [u8; 32] = {
    let mut vec = [0; 32];
    vec[0] = 1;
    vec
};

#[derive(Debug, Parser)]
#[command(name = "zxc", about = "CirC: the circuit compiler")]
struct Options {
    /// Input file
    #[arg(name = "PATH")]
    path: PathBuf,

    /*
    #[arg(long, default_value = "P", parse(from_os_str))]
    prover_key: PathBuf,

    #[arg(long, default_value = "V", parse(from_os_str))]
    verifier_key: PathBuf,

    #[arg(long, default_value = "pi", parse(from_os_str))]
    proof: PathBuf,

    #[arg(long, default_value = "x", parse(from_os_str))]
    instance: PathBuf,
    */
    #[arg(short = 'L')]
    /// skip linearity reduction entirely
    skip_linred: bool,

    #[command(flatten)]
    /// CirC options
    circ: CircOpt,

    #[arg(long, default_value = "count")]
    action: ProofAction,

    #[arg(short = 'q')]
    /// quiet mode: don't print R1CS at the end
    quiet: bool,

    #[arg(long = "opt_level", default_value_t = 3)]
    /// level of optimizations
    opt_level: usize,

    #[arg(long = "verbose_opt")]
    /// print results of every optimization pass
    verbose_opt: bool,

    #[arg(long = "inline_spartan")]
    /// automatically execute Spartan
    inline_spartan: bool,

    #[arg(long = "print_proof")]
    /// automatically execute Spartan
    print_proof: bool,
}

#[derive(PartialEq, Eq, Debug, Clone, ValueEnum)]
enum ProofAction {
    Count,
    Setup,
    Prove,
    Verify,
}

#[derive(PartialEq, Debug, Clone, ValueEnum)]
enum ProofOption {
    Count,
    Prove,
}

struct SparseMatEntry {
    args_a: Vec<(usize, [u8; 32])>,
    args_b: Vec<(usize, [u8; 32])>,
    args_c: Vec<(usize, [u8; 32])>
}

// When adding the validity check, what does the sparse format look like?
fn get_sparse_cons_with_v_check(
    c: &(Lc, Lc, Lc), 
    v_cnst: usize,
    io_relabel: impl FnOnce(usize) -> usize + std::marker::Copy,
    witness_relabel: impl FnOnce(usize) -> usize + std::marker::Copy,
) -> SparseMatEntry {
    // Extract all entries from A, B, C
    let (args_a, args_b, args_c) = {
        let mut args_a = Vec::new();
        let mut args_b = Vec::new();
        let mut args_c = Vec::new();
        if !c.0.constant_is_zero() {
            args_a.push((v_cnst, c.0.constant.i()));
        }
        for (var, coeff) in c.0.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_a.push((io_relabel(var.number()), coeff.i())),
                VarType::FinalWit => args_a.push((witness_relabel(var.number()), coeff.i())),
                _ => panic!("Unsupported variable type!")
            }
        }
        if !c.1.constant_is_zero() {
            args_b.push((v_cnst, c.1.constant.i()));
        }
        for (var, coeff) in c.1.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_b.push((io_relabel(var.number()), coeff.i())),
                VarType::FinalWit => args_b.push((witness_relabel(var.number()), coeff.i())),
                _ => panic!("Unsupported variable type!")
            }
        }
        if !c.2.constant_is_zero() {
            args_c.push((v_cnst, c.2.constant.i()));
        }
        for (var, coeff) in c.2.monomials.iter() {
            match var.ty() {
                VarType::Inst => {
                    args_c.push((io_relabel(var.number()), coeff.i()))
                },
                VarType::FinalWit => args_c.push((witness_relabel(var.number()), coeff.i())),
                _ => panic!("Unsupported variable type!")
            }
        }
        (args_a, args_b, args_c)
    };
    let args_a = args_a.into_iter().map(|(x, y)| (x, integer_to_bytes(y))).collect();
    let args_b = args_b.into_iter().map(|(x, y)| (x, integer_to_bytes(y))).collect();
    let args_c = args_c.into_iter().map(|(x, y)| (x, integer_to_bytes(y))).collect();
    return SparseMatEntry { args_a, args_b, args_c };
}

// Convert an integer into a little-endian byte array
fn integer_to_bytes(raw: Integer) -> [u8; 32] {
    let mut bits = raw.to_digits::<u8>(Order::LsfLe);
    assert!(bits.len() <= 32);
    bits.extend(vec![0; 32 - bits.len()]);
    bits.try_into().unwrap()
}

// Convert a little-endian byte array to integer
fn bytes_to_integer(bytes: &[u8; 32]) -> Integer {
    let mut i = Integer::ZERO;
    let mut factor = Integer::from(1);
    for b in bytes {
        i += Integer::from(*b as usize) * factor.clone();
        factor *= 256;
    }
    i
}

fn _write_bytes(mut f: &File, bytes: &[u8; 32]) -> std::io::Result<()> {
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

// --
// Structures to match Spartan
// --
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
    fn serialize_to_file(&self, benchmark_name: String) -> std::io::Result<()> {
        let file_name = format!("../zok_tests/constraints/{}_bin.ctk", benchmark_name);
        let mut f = File::create(file_name)?;
        let content = bincode::serialize(&self).unwrap();
        f.write(&content)?;
        Ok(())
    }

    fn write_to_file(&self, benchmark_name: String) -> std::io::Result<()> {
        let file_name = format!("../zok_tests/constraints/{}.ctk", benchmark_name);
        let mut f = File::create(file_name)?;
        writeln!(&mut f, "Num Blocks: {}", self.block_num_circuits)?;
        writeln!(&mut f, "Max Num Vars: {}", self.num_vars)?;
        writeln!(&mut f, "Num Inputs: {}", self.num_inputs_unpadded)?;
        write!(&mut f, "{:>11}: ", "Block")?;
        for i in 0..self.block_num_circuits {
            write!(&mut f, "{:>6}", i)?;
        }
        writeln!(&mut f, "")?;
        write!(&mut f, "{:>11}: ", "Num Vars")?;
        for i in &self.num_vars_per_block {
            write!(&mut f, "{:>6}", i)?;
        }
        writeln!(&mut f, "")?;
        write!(&mut f, "{:>11}: ", "Num Phy Ops")?;
        for i in &self.block_num_phy_ops {
            write!(&mut f, "{:>6}", i)?;
        }
        writeln!(&mut f, "")?;
        write!(&mut f, "{:>11}: ", "Num Vir Ops")?;
        for i in &self.block_num_vir_ops {
            write!(&mut f, "{:>6}", i)?;
        }
        writeln!(&mut f, "")?;
        writeln!(&mut f, "Max TS Width: {}", self.max_ts_width)?;

        // Instances
        let mut counter = 0;
        for inst in &self.args {
            writeln!(&mut f, "--\nINST {}, {} x {}", counter, inst.len(), self.num_vars_per_block[counter])?;
            for cons in inst {
                write!(&mut f, "  A ")?;
                let mut pad = false;
                for (var, val) in &cons.0 {
                    if !pad {
                        write!(&mut f, "{} ", var)?;
                    } else {
                        write!(&mut f, "    {} ", var)?;
                    }
                    writeln!(&mut f, "{}", bytes_to_integer(&val))?;
                    pad = true;
                }
                if !pad { writeln!(&mut f, "")?; }
                write!(&mut f, "  B ")?;
                let mut pad = false;
                for (var, val) in &cons.1 {
                    if !pad {
                        write!(&mut f, "{} ", var)?;
                    } else {
                        write!(&mut f, "    {} ", var)?;
                    }
                    writeln!(&mut f, "{}", bytes_to_integer(&val))?;
                    pad = true;
                }
                if !pad { writeln!(&mut f, "")?; }
                write!(&mut f, "  C ")?;
                let mut pad = false;
                for (var, val) in &cons.2 {
                    if !pad {
                        write!(&mut f, "{} ", var)?;
                    } else {
                        write!(&mut f, "    {} ", var)?;
                    }
                    writeln!(&mut f, "{}", bytes_to_integer(&val))?;
                    pad = true;
                }
                if !pad { writeln!(&mut f, "")?; }
                writeln!(&mut f, "")?;
            }
            counter += 1;
        }
        writeln!(&mut f, "INST_END")?;
        writeln!(&mut f, "")?;

        write!(&mut f, "Input Liveness: ")?;
        for b in &self.input_liveness {
            write!(&mut f, "{} ", if *b { 1 } else { 0 })?;
        }
        writeln!(&mut f, "")?;
        writeln!(&mut f, "Prog Input Width: {}", self.func_input_width)?;
        writeln!(&mut f, "Input Offset: {}", self.input_offset)?;
        writeln!(&mut f, "Input Block Num: {}", self.input_block_num)?;
        writeln!(&mut f, "Output Offset: {}", self.output_offset)?;
        writeln!(&mut f, "Output Block Num: {}", self.output_block_num)?;
        Ok(())
    }
}

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
    // Initial memory state, in (addr, val, ls = STORE, ts = 0) pair, sorted by appearance in program input (the same as address order)
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
    fn serialize_to_file(&self, benchmark_name: String) -> std::io::Result<()> {
        let file_name = format!("../zok_tests/inputs/{}_bin.rtk", benchmark_name);
        let mut f = File::create(file_name)?;
        let content = bincode::serialize(&self).unwrap();
        f.write(&content)?;
        Ok(())
    }

    fn write_to_file(&self, benchmark_name: String) -> std::io::Result<()> {
        let file_name = format!("../zok_tests/inputs/{}.rtk", benchmark_name);
        let mut f = File::create(file_name)?;
        writeln!(&mut f, "Block Max Num Proofs: {}", self.block_max_num_proofs)?;
        write!(&mut f, "{:>11}: ", "Block")?;
        for i in 0..self.block_num_proofs.len() {
            write!(&mut f, "{:>6}", i)?;
        }
        writeln!(&mut f, "")?;
        writeln!(&mut f, "{:>11}: ", "Num Proofs")?;
        for i in &self.block_num_proofs {
            write!(&mut f, "{:>6}", i)?;
        }
        writeln!(&mut f, "")?;
        writeln!(&mut f, "Total Num Proofs: {}", self.consis_num_proofs)?;
        writeln!(&mut f, "Total Num Init Phy Mem Acc: {}", self.total_num_init_phy_mem_accesses)?;
        writeln!(&mut f, "Total Num Init Vir Mem Acc: {}", self.total_num_init_vir_mem_accesses)?;
        writeln!(&mut f, "Total Num Phy Mem Acc: {}", self.total_num_phy_mem_accesses)?;
        writeln!(&mut f, "Total Num Vir Mem Acc: {}", self.total_num_vir_mem_accesses)?;

        writeln!(&mut f, "BLOCK_VARS")?;
        let mut block_counter = 0;
        for block in &self.block_vars_matrix {
            writeln!(&mut f, "BLOCK {}", block_counter)?;
            let mut exec_counter = 0;
            for exec in block {
                writeln!(&mut f, "EXEC {}", exec_counter)?;
                for assg in &exec.assignment {
                    write!(&mut f, "{} ", bytes_to_integer(&assg.to_bytes()))?;
                }
                writeln!(&mut f, "")?;
                exec_counter += 1;
            }
            block_counter += 1;
        }
        writeln!(&mut f, "EXEC_INPUTS")?;
        let mut exec_counter = 0;
        for exec in &self.exec_inputs {
            writeln!(&mut f, "EXEC {}", exec_counter)?;
            for assg in &exec.assignment {
                write!(&mut f, "{} ", bytes_to_integer(&assg.to_bytes()))?;
            }
            writeln!(&mut f, "")?;
            exec_counter += 1;
        }
        writeln!(&mut f, "INIT_PHY_MEMS")?;
        let mut addr_counter = 0;
        for addr in &self.init_phy_mems_list {
            writeln!(&mut f, "ACCESS {}", addr_counter)?;
            for assg in &addr.assignment {
                write!(&mut f, "{} ", bytes_to_integer(&assg.to_bytes()))?;
            }
            writeln!(&mut f, "")?;
            addr_counter += 1;
        }
        writeln!(&mut f, "INIT_VIR_MEMS")?;
        let mut addr_counter = 0;
        for addr in &self.init_vir_mems_list {
            writeln!(&mut f, "ACCESS {}", addr_counter)?;
            for assg in &addr.assignment {
                write!(&mut f, "{} ", bytes_to_integer(&assg.to_bytes()))?;
            }
            writeln!(&mut f, "")?;
            addr_counter += 1;
        }
        writeln!(&mut f, "ADDR_PHY_MEMS")?;
        let mut addr_counter = 0;
        for addr in &self.addr_phy_mems_list {
            writeln!(&mut f, "ACCESS {}", addr_counter)?;
            for assg in &addr.assignment {
                write!(&mut f, "{} ", bytes_to_integer(&assg.to_bytes()))?;
            }
            writeln!(&mut f, "")?;
            addr_counter += 1;
        }
        writeln!(&mut f, "ADDR_VIR_MEMS")?;
        let mut addr_counter = 0;
        for addr in &self.addr_vir_mems_list {
            writeln!(&mut f, "ACCESS {}", addr_counter)?;
            for assg in &addr.assignment {
                write!(&mut f, "{} ", bytes_to_integer(&assg.to_bytes()))?;
            }
            writeln!(&mut f, "")?;
            addr_counter += 1;
        }
        writeln!(&mut f, "ADDR_VM_BITS")?;
        let mut addr_counter = 0;
        for addr in &self.addr_ts_bits_list {
            writeln!(&mut f, "ACCESS {}", addr_counter)?;
            for assg in &addr.assignment {
                write!(&mut f, "{} ", bytes_to_integer(&assg.to_bytes()))?;
            }
            writeln!(&mut f, "")?;
            addr_counter += 1;
        }
        write!(&mut f, "Inputs: ")?;
        for assg in &self.input {
            write!(&mut f, "{} ", bytes_to_integer(&assg))?;
        }
        writeln!(&mut f, "")?;
        write!(&mut f, "Input Mems: ")?;
        for assg in &self.input_mem {
            write!(&mut f, "{} ", bytes_to_integer(&assg))?;
        }
        writeln!(&mut f, "")?;
        write!(&mut f, "Outputs: ")?;
        for assg in &[self.output] {
            write!(&mut f, "{} ", bytes_to_integer(&assg))?;
        }
        writeln!(&mut f, "")?;
        writeln!(&mut f, "Output Exec Num: {}", self.output_exec_num)?;
        Ok(())
    }
}

// --
// Generate constraints and others
// --
fn get_compile_time_knowledge<const VERBOSE: bool>(
    path: PathBuf,
    options: &Options,
) -> (CompileTimeKnowledge, Vec<(Vec<usize>, Vec<usize>)>, Vec<usize>, Vec<ProverData>) {
    println!("Generating Compiler Time Data...");

    let (
        cs, 
        func_input_width, 
        num_inputs_unpadded, 
        live_io_list, 
        block_num_wit_reads,
        block_num_mem_accesses, 
        input_liveness,
    ) = {
        let inputs = zsharp::Inputs {
            file: path,
            mode: Mode::Proof,
            opt_level: options.opt_level,
            verbose_opt: options.verbose_opt
        };
        ZSharpFE::gen(inputs)
    };

    println!("Optimizing IR... ");
    let cs = opt(
        cs,
        vec![
            Opt::ScalarizeVars,
            Opt::Flatten,
            Opt::Sha,
            Opt::ConstantFold(Box::new([])),
            Opt::Flatten,
            Opt::Inline,
            // Tuples must be eliminated before oblivious array elim
            Opt::Tuple,
            Opt::ConstantFold(Box::new([])),
            Opt::Obliv,
            // The obliv elim pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::LinearScan,
            // The linear scan pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::Flatten,
            Opt::ConstantFold(Box::new([])),
            Opt::Inline,
            Opt::SkolemizeChallenges
        ],
    );
    println!("done.");
    
    if VERBOSE {
        for (name, c) in &cs.comps {
            println!("\n--\nName: {}", name);
            println!("VariableMetadata:");
            for v in &c.metadata.ordered_input_names() {
                let m = &c.metadata.lookup(v);
                println!("{}: vis: {}, round: {}, random: {}, committed: {}", 
                    v, if m.vis == None {"PUBLIC"} else {if m.vis == Some(0) {"PROVER"} else {"VERIFIER"}}, m.round.to_string(), m.random.to_string(), m.committed.to_string());
            }
            println!("Output:");
            for t in &c.outputs {
                println!("  {}", t);
            }
        }
    }

    if VERBOSE { println!("Converting to r1cs:"); }
    let mut block_num = 0;
    let mut block_name = format!("Block_{}", block_num);
    // Obtain a list of (r1cs, io_map) for all blocks
    // As we generate R1Cs for each block:
    // 1. Add checks on validity: V * V = V
    // 2. Compute the maximum number of witnesses within any constraint to obtain final io width
    let mut r1cs_list = Vec::new();
    let io_width = 2 * num_inputs_unpadded;
    // Number of io + mem_op_vars + wit_read_vars of each block
    // Actual intermediate computations of each block starts at the offset
    let wit_offset_per_block: Vec<usize> = (0..cs.comps.len()).map(|b|
        io_width + 2 * block_num_mem_accesses[b].0 + 4 * block_num_mem_accesses[b].1 + block_num_wit_reads[b]
    ).collect();
    let mut max_num_vars = io_width;
    let mut max_num_cons = 1;
    // Obtain a list of prover data by block
    let mut prover_data_list = Vec::new();
    // Obtain the actual number of vars per block, round to the next power of 2
    let mut num_vars_per_block = Vec::new();
    while let Some(c) = cs.comps.get(&block_name) {
        let r1cs = to_r1cs(c, cfg());
        // Add prover data
        let (prover_data, _) = r1cs.clone().finalize(c);
        prover_data_list.push(prover_data);

        let r1cs = {
            let old_size = r1cs.constraints().len();
            let r1cs = reduce_linearities(r1cs, cfg());
            let new_size = r1cs.constraints().len();
            if VERBOSE {
                println!("{} linear reduction: {} -> {}", block_name, old_size, new_size);
            }
            r1cs
        };

        let num_vars = 
            r1cs.num_vars()
            + io_width // input + output
            - live_io_list[block_num].0.len() - live_io_list[block_num].1.len(); // remove all inputs / outputs
        num_vars_per_block.push(num_vars.next_power_of_two());
        // Include V * V = V
        let num_cons = r1cs.constraints().len() + 1;
        if num_vars > max_num_vars { max_num_vars = num_vars };
        if num_cons > max_num_cons { max_num_cons = num_cons };
        r1cs_list.push(r1cs);
        block_num += 1;
        block_name = format!("Block_{}", block_num);
    }

    let max_num_vars = max_num_vars.next_power_of_two();
    let max_num_cons = max_num_cons.next_power_of_two();

    // Convert R1CS into Spartan sparse format
    // The final version will be of form: (v, _, i, o, ma, mv, w), where
    //   v is the valid bit
    //   _ is a dummy
    //   i are the inputs
    //   o are the outputs
    //  ma are addresses of all memory accesses
    //  mv are values of all memory accesses
    //   w are witnesses
    // According to the final io width, re-label all inputs and witnesses to the form (witness, input, output)
    let io_relabel = |b: usize, i: usize| -> usize {
        if i < live_io_list[b].0.len() {
            // inputs, label starts at 1, index starts at 2
            live_io_list[b].0[i] + 1
        } else if i < live_io_list[b].0.len() + live_io_list[b].1.len() {
            // outputs, label starts at 1, index starts at num_inputs_unpadded + 1
            live_io_list[b].1[i - live_io_list[b].0.len()] + num_inputs_unpadded
        } else {
            // Everything else starts at io_width
            io_width + i - live_io_list[b].0.len() - live_io_list[b].1.len()
        }
    };
    // Add all IOs and WV in front
    let witness_relabel = |b: usize, i: usize| -> usize {
        wit_offset_per_block[b] + i
    };
    // 0th entry is constant
    let v_cnst = 0;
    let mut sparse_mat_entry: Vec<Vec<SparseMatEntry>> = Vec::new();
    for b in 0..r1cs_list.len() {
        let r1cs = &r1cs_list[b];
        sparse_mat_entry.push(Vec::new());
        // First constraint is V * V = V
        let (args_a, args_b, args_c) =
            (vec![(v_cnst, ONE_VEC)], vec![(v_cnst, ONE_VEC)], vec![(v_cnst, ONE_VEC)]);
        sparse_mat_entry[b].push(SparseMatEntry { args_a, args_b, args_c });
        // Iterate
        for c in r1cs.constraints() {
            sparse_mat_entry[b].push(get_sparse_cons_with_v_check(c, v_cnst, |i| io_relabel(b, i), |i| witness_relabel(b, i)));
        }
    }

    // Print out the sparse matrix
    if VERBOSE {
        println!("NUM_VARS: {}", max_num_vars);
        println!("NUM_CONS: {}", max_num_cons);
        for b in 0..sparse_mat_entry.len() {
            println!("\nBLOCK {}", b);
            for i in 0..min(10, sparse_mat_entry[b].len()) {
                println!("  ROW {}", i);
                let e = &sparse_mat_entry[b][i];
                println!("    A: {:?}\n    B: {:?}\n    C: {:?}", e.args_a, e.args_b, e.args_c);
            }
            if sparse_mat_entry[b].len() > 10 {
                println!("...");
            }
        }
    }

    // Collect all necessary info
    let block_num_circuits = r1cs_list.len();
    let num_vars = max_num_vars;
    let args: Vec<Vec<(Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>)>> = 
        sparse_mat_entry.iter().map(|v| v.iter().map(|i| (
            i.args_a.clone(), 
            i.args_b.clone(), 
            i.args_c.clone()
        )).collect()).collect();
    let input_block_num = 0;
    let output_block_num = block_num_circuits;

    (CompileTimeKnowledge {
        block_num_circuits,
        num_vars,
        num_inputs_unpadded,
        num_vars_per_block,
        block_num_phy_ops: block_num_mem_accesses.iter().map(|i| i.0).collect(),
        block_num_vir_ops: block_num_mem_accesses.iter().map(|i| i.1).collect(),
        max_ts_width: MAX_TS_WIDTH,
        max_addr_width: if options.opt_level < 3 { MAX_ADDR_WIDTH } else { 0 },
        args,
        
        input_liveness,
        func_input_width,
        input_offset: NUM_RESERVED_VARS,
        input_block_num,
        output_offset: OUTPUT_OFFSET,
        output_block_num
      },
      live_io_list,
      block_num_wit_reads,
      prover_data_list,
    )
}

// --
// Generate witnesses and others
// --
fn get_run_time_knowledge<const VERBOSE: bool>(
    options: &Options,
    entry_witnesses: Vec<Integer>,
    entry_regs_concat: Vec<Integer>,
    entry_stacks_concat: Vec<Integer>,
    entry_arrays_concat: Vec<Integer>,
    ctk: &CompileTimeKnowledge,
    live_io_list: Vec<(Vec<usize>, Vec<usize>)>,
    block_num_wit_reads: Vec<usize>,
    prover_data_list: Vec<ProverData>,
    total_num_init_phy_mem_accesses: usize,
    total_num_init_vir_mem_accesses: usize,
) -> RunTimeKnowledge {
    // Set up default field for initialization
    let default_field = if !options.circ.field.custom_modulus.is_empty() {
        let error =
            |r: &str| panic!("The field modulus '{}' is {}", &options.circ.field.custom_modulus, r);
        let i = Integer::from_str_radix(&options.circ.field.custom_modulus, 10)
            .unwrap_or_else(|_| error("not an integer"));
        if i.is_probably_prime(30) == rug::integer::IsPrime::No {
            error("not a prime");
        }
        FieldT::from(i)
    } else {
        match options.circ.field.builtin {
            circ_opt::BuiltinField::Bls12381 => FieldT::FBls12381,
            circ_opt::BuiltinField::Bn254 => FieldT::FBn254,
            circ_opt::BuiltinField::Curve25519 => FieldT::FCurve25519,
            circ_opt::BuiltinField::Goldilocks => FieldT::FGoldilocks,
            circ_opt::BuiltinField::GoldilocksExt2 => FieldT::FGoldilocksExt2,
        }
    };

    let num_blocks = ctk.block_num_circuits;
    let num_input_unpadded = ctk.num_inputs_unpadded;
    let io_width = 2 * num_input_unpadded;

    let wit_start = Instant::now();
    // Block-specific info
    let mut func_outputs = Integer::ZERO;
    let mut evaluator = StagedWitCompEvaluatorBatched::new(
        prover_data_list.iter().map(|d| &d.precompute).collect(), 
        ctk.output_block_num,
        num_input_unpadded,
        default_field,
    );
    // Convert entry_regs to HashMap<usize, Value> form
    // input indices are 6(%SP) ++ 5(%AS) ++ [2 + input_offset..](others)
    // Filter out all dead inputs
    let (input_map, initial_phy_mem, initial_vir_mem, init_phy_ops_list, init_vir_ops_list) = 
        ZSharpFE::generate_input(&entry_regs_concat, &entry_stacks_concat, &entry_arrays_concat, &ctk.input_liveness, ctk.input_offset);
    evaluator.eval_setup(0, input_map, initial_phy_mem, initial_vir_mem, entry_witnesses);

    // Start from entry block, compute value of witnesses
    // Note: block_vars_matrix  are sorted by block_num_proofs, tie-breaked by block id
    // Thus, block_vars_matrix[0] might NOT store the executions of block 0!
    let mut block_vars_matrix = vec![Vec::new(); num_blocks];
    let mut exec_inputs = Vec::new();
    let mut phy_ops_list = init_phy_ops_list.clone();
    let mut vir_ops_list: Vec<[Integer; 4]> = init_vir_ops_list.iter().map(|i| [i[0].clone(), i[1].clone(), Integer::ZERO, Integer::ZERO]).collect();
    // Number of times each block is executed
    let mut block_num_proofs = vec![0; num_blocks];
    let mut nb = evaluator.get_cur_block();
    while nb != ctk.output_block_num {
        block_num_proofs[nb] += 1;

        let (_io, phy_ops, vir_ops, eval, _wit) = evaluator.eval_block(&live_io_list[nb], block_num_wit_reads[nb], ctk.block_num_phy_ops[nb], ctk.block_num_vir_ops[nb]);
        // vars = valid | _ | eval
        let mut vars: Vec<Integer> = [vec![Integer::from(1), Integer::ZERO], eval.into_iter().map(|v| v.as_integer().unwrap()).collect()].concat();
        vars.extend(vec![Integer::ZERO; ctk.num_vars_per_block[nb] - vars.len()]);
        if VERBOSE {
            let print_width = min(num_input_unpadded - 1, 32);
            print!("--\n{:3} ", block_num_proofs.iter().sum::<usize>());
            for i in 0..2 + print_width {
                print!("{:3} ", i);
            }
            println!();
            print!("{:3} ", "I");
            for i in 0..2 + print_width {
                print!("{:3} ", vars[i]);
            }
            if num_input_unpadded - 1 > print_width {
                println!("...");
            } else {
                println!();
            }
            print!("{:3} {:3} {:3} ", "O", " ", " ");
            for i in num_input_unpadded + 1..num_input_unpadded + 1 + print_width {
                print!("{:3} ", vars[i]);
            }
            if num_input_unpadded - 1 > print_width {
                println!("...");
            } else {
                println!();
            }
            print!("{:3} ", "W");
            let print_width = min(vars.len() - io_width, 32);
            for i in 0..print_width {
                print!("{:3} ", vars[io_width + i]);
            }
            if vars.len() > print_width {
                println!("...");
            } else {
                println!();
            }
        }

        let inputs = [vars[..io_width].to_vec(), vec![Integer::ZERO; io_width.next_power_of_two() - io_width]].concat();
        let inputs_assignment = Assignment::new(&inputs.iter().map(|i| integer_to_bytes(i.clone())).collect::<Vec<[u8; 32]>>()).unwrap();
        let vars_assignment = Assignment::new(&vars.iter().map(|i| integer_to_bytes(i.clone())).collect::<Vec<[u8; 32]>>()).unwrap();

        exec_inputs.push(inputs_assignment.clone());
        block_vars_matrix[nb].push(vars_assignment);
        phy_ops_list.extend(phy_ops.into_iter().map(|i| [i[0].as_integer().unwrap(), i[1].as_integer().unwrap()]));
        vir_ops_list.extend(vir_ops.into_iter().map(|i| [i[0].as_integer().unwrap(), i[1].as_integer().unwrap(), i[2].as_integer().unwrap(), i[3].as_integer().unwrap()]));
        nb = evaluator.get_cur_block();
        if nb == ctk.output_block_num {
            func_outputs = vars[num_input_unpadded + OUTPUT_OFFSET].clone();
        }
    }
    // Truncate all blocks with zero execution
    for i in (0..num_blocks).rev() {
        if block_num_proofs[i] == 0 { block_vars_matrix.remove(i); }
    }
    
    // The most time any block is executed
    let block_max_num_proofs = *block_num_proofs.iter().max().unwrap();
    // Total number of blocks executed
    let consis_num_proofs = block_num_proofs.iter().sum();
    let output_exec_num = consis_num_proofs - 1;
    let wit_time = wit_start.elapsed();
    println!("Witness gen time: {}ms", wit_time.as_millis());

    let mem_start = Instant::now();
    // Initial Physical & Virtual Memory: valid, _, addr, data (ts and ls are both 0 and are not recorded)
    let init_phy_mems_list = init_phy_ops_list.into_iter().map(|m| {
        let mem: Vec<Integer> = vec![Integer::from(1), Integer::ZERO, m[0].clone(), m[1].clone()];
        Assignment::new(&mem.iter().map(|i| integer_to_bytes(i.clone())).collect::<Vec<[u8; 32]>>()).unwrap()
    }).collect();
    let init_vir_mems_list = init_vir_ops_list.into_iter().map(|m| {
        let mem: Vec<Integer> = vec![Integer::from(1), Integer::ZERO, m[0].clone(), m[1].clone()];
        Assignment::new(&mem.iter().map(|i| integer_to_bytes(i.clone())).collect::<Vec<[u8; 32]>>()).unwrap()
    }).collect();

    // Sort phy_ops and vir_ops
    phy_ops_list.sort_by(|a, b| a[0].cmp(&b[0]));
    vir_ops_list.sort_by(|a, b| a[0].cmp(&b[0])); // tie-breaking timestamp preserved if sorting is stable

    // Physical Memory: valid, D, addr, data
    let mut addr_phy_mems_list = Vec::new();
    let mut phy_mem_last = vec![Integer::from(1); 4];
    for i in 0..phy_ops_list.len() {
        let m = &phy_ops_list[i];
        let mut mem: Vec<Integer> = vec![Integer::ZERO; 4];
        mem[0] = Integer::from(1);
        mem[2] = m[0].clone();
        mem[3] = m[1].clone();
        // backend requires the 1st entry to be v[k + 1] * (1 - addr[k + 1] + addr[k])
        if i != 0 {
            phy_mem_last[1] = mem[0].clone() * (Integer::from(1) - mem[2].clone() + phy_mem_last[2].clone());
            addr_phy_mems_list.push(Assignment::new(&phy_mem_last.iter().map(|i| integer_to_bytes(i.clone())).collect::<Vec<[u8; 32]>>()).unwrap());
        }
        if i == phy_ops_list.len() - 1 {
            addr_phy_mems_list.push(Assignment::new(&mem.iter().map(|i| integer_to_bytes(i.clone())).collect::<Vec<[u8; 32]>>()).unwrap());
        } else {
            phy_mem_last = mem;
        }
    }

    // Virtual Memory: valid, D1, addr, data, ls, ts, _, _
    let mut addr_vir_mems_list = Vec::new();
    let mut vir_mem_last: Vec<Integer> = Vec::new();
    // TS Bits: D2, EQ, B0, B1, B2 ...
    let mut addr_ts_bits_list = Vec::new();
    for i in 0..vir_ops_list.len() {
        let m = &vir_ops_list[i];
        
        let mut mem: Vec<Integer> = vec![Integer::ZERO; 8];
        mem[0] = Integer::from(1);
        mem[2] = m[0].clone();
        mem[3] = m[1].clone();
        mem[4] = m[2].clone();
        mem[5] = m[3].clone();

        let mut ts_bits: Vec<[u8; 32]> = if options.opt_level < OPT_RO_ARRAYS {
            vec![ZERO_VEC; (MAX_TS_WIDTH + MAX_ADDR_WIDTH + 5).next_power_of_two()]
        } else {
            vec![ZERO_VEC; (MAX_TS_WIDTH + 2).next_power_of_two()]
        };
        // D1, D2, D3, D4
        if i != 0 {
            if options.opt_level < OPT_RO_ARRAYS {
                let addr_offset = MAX_TS_WIDTH + 2;
                // bit split v[k + 1] * (addr[k + 1] - addr[k])
                let mut d4 = mem[0].clone() * (mem[2].clone() - vir_mem_last[2].clone());
                if d4 != 0 {
                    // D4
                    ts_bits[addr_offset] = integer_to_bytes(d4.clone());
                    // INV = D4^{-1}
                    ts_bits[addr_offset + 1] = Scalar::from_bytes(&integer_to_bytes(d4.clone())).unwrap().invert().unwrap().to_bytes();
                    // EQ = 1
                    ts_bits[addr_offset + 2] = ONE_VEC;
                    // Use bits to assemble D4 - 1
                    d4 -= 1;
                    let raw_d4_bits = d4.to_digits::<bool>(Order::LsfLe);
                    for (i, b) in raw_d4_bits.into_iter().enumerate() {
                        ts_bits[addr_offset + 3 + i] = if b { ONE_VEC } else { ZERO_VEC };
                    }
                } else {
                    // D1[k] = 1
                    vir_mem_last[1] = Integer::from(1);
                }
            } else {
                // D1[k] = v[k + 1] * (1 - addr[k + 1] + addr[k])
                vir_mem_last[1] = mem[0].clone() * (Integer::from(1) - mem[2].clone() + vir_mem_last[2].clone());
            }
            // D2[k] = D1[k] * (ls[k + 1] - STORE), where STORE = 0
            ts_bits[0] = integer_to_bytes(vir_mem_last[1].clone() * mem[4].clone());
            // Bits of D1[k] * (ts[k + 1] - ts[k]) in ts_bits[2..]
            let mut d4 = vir_mem_last[1].clone() * (mem[5].clone() - vir_mem_last[5].clone());
            if d4 != 0 {
                // EQ = 1
                ts_bits[1] = ONE_VEC;
                // Use bits to assemble D4 - 1
                d4 -= 1;
                let raw_d4_bits = d4.to_digits::<bool>(Order::LsfLe);
                for (i, b) in raw_d4_bits.into_iter().enumerate() {
                    ts_bits[2 + i] = if b { ONE_VEC } else { ZERO_VEC };
                }
            }

            addr_vir_mems_list.push(Assignment::new(&vir_mem_last.iter().map(|i| integer_to_bytes(i.clone())).collect::<Vec<[u8; 32]>>()).unwrap());
            addr_ts_bits_list.push(Assignment::new(&ts_bits).unwrap());
        }
        if i == vir_ops_list.len() - 1 {
            addr_vir_mems_list.push(Assignment::new(&mem.iter().map(|i| integer_to_bytes(i.clone())).collect::<Vec<[u8; 32]>>()).unwrap());
            let empty_ts_bits: Vec<[u8; 32]> = if options.opt_level < OPT_RO_ARRAYS {
                vec![ZERO_VEC; (MAX_TS_WIDTH + MAX_ADDR_WIDTH + 5).next_power_of_two()]
            } else {
                vec![ZERO_VEC; (MAX_TS_WIDTH + 2).next_power_of_two()]
            };
            addr_ts_bits_list.push(Assignment::new(&empty_ts_bits).unwrap());
        } else {
            vir_mem_last = mem;
        }
    }
    
    let total_num_phy_mem_accesses = phy_ops_list.len();
    let total_num_vir_mem_accesses = vir_ops_list.len();
    let mem_time = mem_start.elapsed();
    println!("Mem gen time: {}ms", mem_time.as_millis());

    {
        println!("\n--\nNUM BLOCK EXECS: {}", block_num_proofs.iter().sum::<usize>());
        print!("{:3} ", " ");
        for i in 0..if entry_regs_concat.len() == 0 {1} else {0} {
            print!("{:3} ", i);
        }
        println!();
        print!("{:3} ", "I");
        for i in 0..entry_regs_concat.len() {
            print!("{:3} ", entry_regs_concat[i]);
        }
        println!();
        print!("{:3} ", "S");
        for i in 0..min(entry_stacks_concat.len(), 32) {
            print!("{:3} ", entry_stacks_concat[i]);
        }
        println!();
        print!("{:3} ", "M");
        for i in 0..min(entry_arrays_concat.len(), 32) {
            print!("{:3} ", entry_arrays_concat[i]);
        }
        println!();
        print!("{:3} ", "O");
        println!("{:3} ", func_outputs);
    }

    let func_inputs = entry_regs_concat.iter().map(|i| integer_to_bytes(i.clone())).collect();
    let input_stack = entry_stacks_concat.iter().map(|i| integer_to_bytes(i.clone())).collect();
    let input_mem = entry_arrays_concat.iter().map(|i| integer_to_bytes(i.clone())).collect();
    let func_outputs = integer_to_bytes(func_outputs);

    RunTimeKnowledge {
        block_max_num_proofs,
        block_num_proofs,
        consis_num_proofs,
        total_num_init_phy_mem_accesses,
        total_num_init_vir_mem_accesses,
        total_num_phy_mem_accesses,
        total_num_vir_mem_accesses,
      
        block_vars_matrix,
        exec_inputs,
        init_phy_mems_list,
        init_vir_mems_list,
        addr_phy_mems_list,
        addr_vir_mems_list,
        addr_ts_bits_list,
      
        input: func_inputs,
        input_stack,
        input_mem,
        output: func_outputs,
        output_exec_num
    }
}

fn run_spartan_proof(ctk: CompileTimeKnowledge, rtk: RunTimeKnowledge) {
  let sparse_commit: bool = true;
  let compact_shift: bool = true;

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
  let (pairwise_check_num_circuits, _, _, _, pairwise_check_inst_verifier) = Instance::gen_pairwise_check_inst::<true, false>(
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
  let pairwise_check_gens = SNARKGens::new(pairwise_check_num_cons, pairwise_check_num_vars, pairwise_check_num_circuits, pairwise_check_num_non_zero_entries);
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

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::parse();
    circ::cfg::set(&options.circ);
    println!("{options:?}");

    // --
    // Generate Constraints
    // --
    let compiler_start = Instant::now();
    let benchmark_name = options.path.as_os_str().to_str().unwrap();
    let path = PathBuf::from(format!("../zok_tests/benchmarks/{}.zok", benchmark_name));
    let (ctk, live_io_list, block_num_wit_reads, prover_data_list) = 
        get_compile_time_knowledge::<false>(path, &options);
    let compiler_time = compiler_start.elapsed();

    if options.print_proof {
        ctk.write_to_file(benchmark_name.to_string()).unwrap();
    }
    if !options.inline_spartan {
        // --
        // Write CTK to file
        // --
        ctk.serialize_to_file(benchmark_name.to_string()).unwrap();
    }

    // --
    // Obtain Inputs
    // --
    let witness_start = Instant::now();
    // Keep track of %SP and %AS and record initial memory state
    let mut stack_alloc_counter = 0;
    let mut mem_alloc_counter = 0;
    // Inputs as register, stack, or array
    // Note that stacks and arrays cans be passed as pointers (registers)
    let mut entry_regs: BTreeMap<String, Integer> = BTreeMap::new();
    let mut entry_stacks: BTreeMap<String, Vec<Integer>> = BTreeMap::new(); // for read-only
    let mut entry_arrays: BTreeMap<String, Vec<Integer>> = BTreeMap::new(); // for others
    // Initial memory setup
    let mut entry_regs_concat: Vec<Integer> = Vec::new();
    let mut entry_stacks_concat: Vec<Integer> = Vec::new();
    let mut entry_arrays_concat: Vec<Integer> = Vec::new();
    let no_ro_accesses = options.opt_level < OPT_RO_ARRAYS;

    let input_file_name = format!("../zok_tests/benchmarks/{}.input", benchmark_name);
    let f = File::open(input_file_name);
    if let Ok(f) = f {
        let mut reader = BufReader::new(f);
        let mut buffer = String::new();
        reader.read_line(&mut buffer).unwrap();
        while buffer.trim() != "END".to_string() {
        let split: Vec<String> = buffer.split(' ').map(|i| i.to_string().trim().to_string()).collect();
        let var_name = split[0].split(":").next().unwrap().trim();
        // split is either of form [VAR, VAL] or [VAR, "[", ENTRY_0, ENTRY_1, ..., "]"] 
        if let Ok(val) = Integer::from_str_radix(&split[1], 10) {
            entry_regs.insert(var_name.to_string(), val.clone());
            entry_regs_concat.push(val);
        } else if split[1] == "[ro" && !no_ro_accesses {
            assert_eq!(split[split.len() - 1], "]");
            entry_regs.insert(var_name.to_string(), Integer::from(stack_alloc_counter));
            entry_regs_concat.push(Integer::from(stack_alloc_counter));
            // Parse the entries
            let stack_entries: Vec<Integer> = split[2..split.len() - 1].iter().map(|entry| Integer::from_str_radix(&entry, 10).unwrap()).collect();
            entry_stacks.insert(var_name.to_string(), stack_entries.clone());
            entry_stacks_concat.extend(stack_entries);
            stack_alloc_counter += split.len() - 3; // var, "[", and "]"
        } else {
            assert!(split[1] == "[" || split[1] == "[ro");
            assert_eq!(split[split.len() - 1], "]");
            entry_regs.insert(var_name.to_string(), Integer::from(mem_alloc_counter));
            entry_regs_concat.push(Integer::from(mem_alloc_counter));
            // Parse the entries
            let array_entries: Vec<Integer> = split[2..split.len() - 1].iter().map(|entry| Integer::from_str_radix(&entry, 10).unwrap()).collect();
            entry_arrays.insert(var_name.to_string(), array_entries.clone());
            entry_arrays_concat.extend(array_entries);
            mem_alloc_counter += split.len() - 3; // var, "[", and "]"
        }
        buffer.clear();
        reader.read_line(&mut buffer).unwrap();
    }
    }
    // Insert [%SP, %AS] to the front of entry_reg
    entry_regs.insert("%AS".to_string(), Integer::from(mem_alloc_counter));
    entry_regs_concat.insert(0, Integer::from(mem_alloc_counter));
    entry_regs.insert("%SP".to_string(), Integer::from(stack_alloc_counter));
    entry_regs_concat.insert(0, Integer::from(stack_alloc_counter));

    // Obtain Witnesses,
    let mut entry_witnesses: Vec<Integer> = Vec::new();
    let witness_file_name = format!("../zok_tests/benchmarks/{}.witness", benchmark_name);
    let f = File::open(witness_file_name);
    if let Ok(f) = f {
        let mut reader = BufReader::new(f);
        let mut buffer = String::new();
        reader.read_line(&mut buffer).unwrap();
        while buffer.trim() != "END".to_string() {
            let split: Vec<String> = buffer.split(' ').map(|i| i.to_string().trim().to_string()).collect();
            entry_witnesses.extend(split.iter().map(|entry| Integer::from_str_radix(&entry, 10).unwrap()));
            buffer.clear();
            reader.read_line(&mut buffer).unwrap();
        }
    }

    // --
    // Generate Witnesses
    // --
    let rtk = get_run_time_knowledge::<false>(
        &options, 
        entry_witnesses,
        entry_regs_concat,
        entry_stacks_concat,
        entry_arrays_concat,
        &ctk,
        live_io_list, 
        block_num_wit_reads,
        prover_data_list,
        stack_alloc_counter,
        mem_alloc_counter
    );
    let witness_time = witness_start.elapsed();

    if options.print_proof {
        rtk.write_to_file(benchmark_name.to_string()).unwrap();
    }
    if !options.inline_spartan {
        // --
        // Write RTK to file
        // --
        rtk.serialize_to_file(benchmark_name.to_string()).unwrap();
    } else {
        run_spartan_proof(ctk, rtk);
    }

    println!("Compiler time: {}ms", compiler_time.as_millis());
    println!("\n--\nWitness time: {}ms", witness_time.as_millis());
}