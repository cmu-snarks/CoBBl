use core::cmp::min;
use std::collections::BTreeMap;
use rug::Integer;
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::Mode;
use circ::front::zsharp::OPT_RO_ARRAYS;

use std::fs::File;
use std::io::{BufReader, BufRead};

use circ::cfg::{
    clap::{self, Parser},
    CircOpt,
};
use std::path::PathBuf;
use std::time::*;
use std::iter::zip;
use std::cmp::max;

// Which index in the output (INCLUDING V) denotes %RET?
const OUTPUT_OFFSET: usize = 2;

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

    #[arg(short = 'q')]
    /// quiet mode: don't print R1CS at the end
    quiet: bool,

    #[arg(long = "opt_level", default_value_t = 3)]
    /// level of optimizations
    opt_level: usize,

    #[arg(long = "verbose_opt")]
    /// print results of every optimization pass
    verbose_opt: bool,
}

// --
// Generate witnesses and others
// --
fn interpret<const VERBOSE: bool>(
    path: PathBuf,
    options: &Options,
    mut entry_regs: BTreeMap<String, Integer>,
    entry_stacks: BTreeMap<String, Vec<Integer>>,
    entry_arrays: BTreeMap<String, Vec<Integer>>,
    entry_witnesses: Vec<Integer>,
    entry_regs_concat: Vec<Integer>,
    entry_stacks_concat: Vec<Integer>,
    entry_arrays_concat: Vec<Integer>,
    _total_num_init_phy_mem_accesses: usize,
    _total_num_init_vir_mem_accesses: usize,
) {
    let interpret_start = Instant::now();
    let (
        _, 
        block_id_list, 
        bl_outputs_list, 
        bl_mems_list, 
        _bl_io_map_list,
        _init_phy_mem_list,
        _init_vir_mem_list,
        _phy_mem_list, 
        _vir_mem_list,
    ) = {
        let inputs = zsharp::Inputs {
            file: path,
            mode: Mode::Proof,
            opt_level: options.opt_level,
            verbose_opt: options.verbose_opt
        };

        ZSharpFE::interpret(inputs, &mut entry_regs, &entry_stacks, &entry_arrays, &entry_witnesses)
    };
    let interpret_time = interpret_start.elapsed();
    println!("Interpret time: {}ms", interpret_time.as_millis());

    let func_outputs = bl_outputs_list[block_id_list.len()][OUTPUT_OFFSET].clone().unwrap().as_integer().unwrap();

    if VERBOSE {
        for (b, (os, ms)) in zip(bl_outputs_list, bl_mems_list).enumerate() {
            print!("--\n{:3} ", b);
            for i in 0..os.len() {
                print!("{:3} ", i);
            }
            println!();
            print!("{:3} ", "R");
            for o in &os {
                if let Some(o) = o { print!("{:3} ", o.as_integer().unwrap()); } else { print!("{:>3} ", "_"); }
            }
            println!("");
            print!("{:3} ", "M");
            for m in &ms[0..min(os.len(), ms.len())] {
                if let Some(m) = m { print!("{:3} ", m.as_integer().unwrap()); } else { print!("{:>3} ", "_"); }
            }
            println!("");
        }
    }

    println!("\n--\nNUM BLOCK EXECS: {}", block_id_list.len());
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

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::parse();
    circ::cfg::set(&options.circ);
    println!("{options:?}");

    let benchmark_name = options.path.as_os_str().to_str().unwrap();
    let path = PathBuf::from(format!("../zok_tests/benchmarks/{}.zok", benchmark_name));
    // --
    // Obtain Inputs
    // --
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
    interpret::<false>(
        path.clone(), 
        &options, 
        entry_regs, 
        entry_stacks, 
        entry_arrays, 
        entry_witnesses,
        entry_regs_concat,
        entry_stacks_concat,
        entry_arrays_concat,
        stack_alloc_counter,
        mem_alloc_counter
    );
}