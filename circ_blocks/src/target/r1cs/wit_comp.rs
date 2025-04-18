//! A multi-stage R1CS witness evaluator.

use crate::ir::term::*;
use circ_fields::FieldT;
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use itertools::Itertools;
use rug::Integer;
use serde::{Deserialize, Serialize};

use log::trace;

const R_BN: usize = 1;

/// A witness computation that proceeds in stages.
///
/// In each stage:
/// * it takes a partial assignment
/// * it returns a vector of field values
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct StagedWitComp {
    vars: HashSet<String>,
    stages: Vec<Stage>,
    steps: Vec<(Op, usize)>,
    step_args: Vec<usize>,
    output_steps: Vec<usize>,
    // we don't serialize the cache; it's just used during construction, and terms are expensive to
    // serialize.
    #[serde(skip)]
    term_to_step: TermMap<usize>,
}

/// Specifies a stage.
#[derive(Debug, Serialize, Deserialize)]
pub struct Stage {
    inputs: HashMap<String, Sort>,
    num_outputs: usize,
}

/// Builder interface
impl StagedWitComp {
    /// Add a new stage.
    #[allow(clippy::uninlined_format_args)]
    pub fn add_stage(&mut self, inputs: HashMap<String, Sort>, output_values: Vec<Term>) {
        let stage = Stage {
            inputs,
            num_outputs: output_values.len(),
        };
        for input in stage.inputs.keys() {
            debug_assert!(!self.vars.contains(input), "Duplicate input {}", input);
        }
        self.vars.extend(stage.inputs.keys().cloned());
        self.stages.push(stage);
        let already_have: TermSet = self.term_to_step.keys().cloned().collect();
        for t in PostOrderIter::from_roots_and_skips(output_values.clone(), already_have) {
            self.add_step(t);
        }
        for t in output_values {
            self.output_steps.push(*self.term_to_step.get(&t).unwrap());
        }
    }

    fn add_step(&mut self, term: Term) {
        debug_assert!(!self.term_to_step.contains_key(&term));
        let step_idx = self.steps.len();
        if let Op::Var(name, _) = term.op() {
            debug_assert!(self.vars.contains(name));
        }
        for child in term.cs() {
            let child_step = self.term_to_step.get(child).unwrap();
            self.step_args.push(*child_step);
        }
        let term_op = {
            if let Op::Var(name, sort) = term.op() {
                let reg_name = name.split("%").nth(1).unwrap().split("_").next().unwrap();
                match &reg_name[..1] {
                    "i" | "o" => {
                        let reg_index = (&reg_name[1..]).parse::<usize>().unwrap();
                        Op::Reg(reg_index, sort.clone())
                    }
                    "p" => {
                        panic!("Stack access do not invoke inputs!")
                    }
                    "v" => {
                        panic!("Heap access do not invoke inputs!")
                    }
                    "w" => {
                        let wit_index = (&reg_name[2..]).parse::<usize>().unwrap();
                        Op::Witness(wit_index, sort.clone())
                    }
                    _ => unreachable!()
                }
            } else {
                term.op().clone()
            }
        };
        self.steps.push((term_op, self.step_args.len()));
        self.term_to_step.insert(term, step_idx);
    }

    /// How many stages are there?
    pub fn stage_sizes(&self) -> impl Iterator<Item = usize> + '_ {
        self.stages.iter().map(|s| s.num_outputs)
    }

    /// How many inputs are there for this stage?
    pub fn num_stage_inputs(&self, n: usize) -> usize {
        self.stages[n].inputs.len()
    }
}

/// Evaluator interface
impl StagedWitComp {
    fn step_args(&self, step_idx: usize) -> impl Iterator<Item = usize> + '_ {
        assert!(step_idx < self.steps.len());
        let args_end = self.steps[step_idx].1;
        let args_start = if step_idx == 0 {
            0
        } else {
            self.steps[step_idx - 1].1
        };
        (args_start..args_end).map(move |step_arg_idx| self.step_args[step_arg_idx])
    }
}

/// Evaluates a staged witness computation.
#[derive(Debug)]
pub struct StagedWitCompEvaluator<'a> {
    comp: &'a StagedWitComp,
    variable_values: HashMap<String, Value>,
    step_values: Vec<Value>,
    stages_evaluated: usize,
    outputs_evaluated: usize,
}

impl<'a> StagedWitCompEvaluator<'a> {
    /// Create an empty witness computation.
    pub fn new(comp: &'a StagedWitComp) -> Self {
        Self {
            comp,
            variable_values: Default::default(),
            step_values: Default::default(),
            stages_evaluated: Default::default(),
            outputs_evaluated: 0,
        }
    }
    /// Have all stages been evaluated?
    pub fn is_done(&self) -> bool {
        self.stages_evaluated == self.comp.stages.len()
    }
    fn eval_step(&mut self) {
        let next_step_idx = self.step_values.len();
        assert!(next_step_idx < self.comp.steps.len());
        let op = &self.comp.steps[next_step_idx].0;
        let args: Vec<&Value> = self
            .comp
            .step_args(next_step_idx)
            .map(|i| &self.step_values[i])
            .collect();
        let value = eval_op(op, &args, &self.variable_values);
        trace!(
            "Eval step {}: {} on {:?} -> {}",
            next_step_idx,
            op,
            args,
            value
        );
        self.step_values.push(value);
    }
    /// Evaluate one stage.
    pub fn eval_stage(&mut self, inputs: HashMap<String, Value>) -> Vec<&Value> {
        trace!(
            "Beginning stage {}/{}",
            self.stages_evaluated,
            self.comp.stages.len()
        );
        debug_assert!(self.stages_evaluated < self.comp.stages.len());
        let stage = &self.comp.stages[self.stages_evaluated];
        let num_outputs = stage.num_outputs;
        for (k, v) in &inputs {
            trace!("Input {}: {}", k, v,);
        }
        self.variable_values.extend(inputs);
        if num_outputs > 0 {
            let max_step = (0..num_outputs)
                .map(|i| {
                    let new_output_i = i + self.outputs_evaluated;
                    self.comp.output_steps[new_output_i]
                })
                .max()
                .unwrap();
            while self.step_values.len() <= max_step {
                self.eval_step();
            }
        }
        self.outputs_evaluated += num_outputs;
        self.stages_evaluated += 1;
        let mut out = Vec::new();
        for output_step in
            &self.comp.output_steps[self.outputs_evaluated - num_outputs..self.outputs_evaluated]
        {
            out.push(&self.step_values[*output_step]);
        }
        out
    }
    /// Return the variable values
    pub fn get_variable_values(&self) -> HashMap<String, Value> {
        self.variable_values.clone()
    }
}

/// Evaluates a staged witness computation.
#[derive(Debug)]
pub struct StagedWitCompEvaluatorBatched<'a> {
    comps: Vec<&'a StagedWitComp>,
    exit_label: usize, // terminates if cur_label == exit_label
    cur_label: usize,
    entry_witnesses: Vec<Integer>, // list of non-det witnesses used by Witness Op, type unknown
    witness_offset: usize, // index of the next witness to be assigned
    trans_regs: Vec<Value>, // block transition state
    phy_mem: Vec<Value>, // stack state
    phy_mem_patches: HashMap<usize, Value>, // patches to stack during each evaluated stage, do not update directly in case of future roll-back
    vir_mem: Vec<Value>, // heap state
    vir_mem_patches: HashMap<usize, Value>, // patches to heap during each evaluated stage
    step_values: Vec<Value>, // all intermediate witnesses
    stages_evaluated: usize,
    outputs_evaluated: usize,
}

impl<'a> StagedWitCompEvaluatorBatched<'a> {
    /// Create an empty witness computation.
    pub fn new(comps: Vec<&'a StagedWitComp>, exit_label: usize, reg_width: usize, default_field: FieldT) -> Self {
        let f_zero = Value::Field(default_field.new_v(0));
        Self {
            comps,
            exit_label,
            cur_label: 0,
            entry_witnesses: Default::default(),
            witness_offset: 0,
            trans_regs: vec![f_zero; reg_width], // trans_regs always store field values
            phy_mem: Default::default(),
            phy_mem_patches: Default::default(),
            vir_mem: Default::default(),
            vir_mem_patches: Default::default(),
            step_values: Default::default(),
            stages_evaluated: Default::default(),
            outputs_evaluated: 0,
        }
    }
    /// Have all stages been evaluated?
    pub fn is_done(&self) -> bool {
        self.cur_label == self.exit_label
    }

    /// Obtain the label for the next block
    pub fn get_cur_block(&self) -> usize {
        self.cur_label
    }
    /// Setup the evaluation
    pub fn eval_setup(&mut self, entry_label: usize, inputs: HashMap<usize, Value>, initial_phy_mem: Vec<Value>, initial_vir_mem: Vec<Value>, witnesses: Vec<Integer>) {
        self.cur_label = entry_label;
        for (i, v) in inputs {
            self.trans_regs[i] = v;
        }
        self.phy_mem = initial_phy_mem;
        self.vir_mem = initial_vir_mem;
        self.entry_witnesses = witnesses;
    }
    fn eval_step(&mut self) {
        let next_step_idx = self.step_values.len();
        assert!(next_step_idx < self.comps[self.cur_label].steps.len());
        let op = &self.comps[self.cur_label].steps[next_step_idx].0;
        let args: Vec<&Value> = self
            .comps[self.cur_label]
            .step_args(next_step_idx)
            .map(|i| &self.step_values[i])
            .collect();
        let value = eval_op_block(
            op, 
            &args, 
            &self.entry_witnesses,
            self.witness_offset,
            &self.trans_regs,
            &self.phy_mem,
            &self.phy_mem_patches,
            &self.vir_mem,
            &self.vir_mem_patches,
        );
        trace!(
            "Eval step {}: {} on {:?} -> {}",
            next_step_idx,
            op,
            args,
            value
        );
        // Update memory
        match op {
            Op::StackPush(..) => {
                let stack_cond = args[0].as_bool();
                if stack_cond {
                    let stack_index = args[1].as_usize().unwrap();
                    self.phy_mem_patches.insert(stack_index, value.clone());
                }
            }
            Op::HeapStore(..) => {
                let heap_cond = args[0].as_bool();
                if heap_cond {
                    let heap_index = args[1].as_usize().unwrap();
                    self.vir_mem_patches.insert(heap_index, value.clone());
                }
            }
            _ => {}
        }
        self.step_values.push(value);
    }
    // Evaluate a stage
    // Returns WIT
    fn eval_stage(&mut self) -> Vec<Value> {
        trace!(
            "Beginning stage {}/{} of block {}",
            self.stages_evaluated,
            self.comps[self.cur_label].stages.len(),
            self.cur_label
        );
        debug_assert!(self.stages_evaluated < self.comps[self.cur_label].stages.len());
        let stage = &self.comps[self.cur_label].stages[self.stages_evaluated];
        let num_outputs = stage.num_outputs;
        // All inputs are expressed using trans_regs
        if num_outputs > 0 {
            let max_step = (0..num_outputs)
                .map(|i| {
                    let new_output_i = i + self.outputs_evaluated;
                    self.comps[self.cur_label].output_steps[new_output_i]
                })
                .max()
                .unwrap();
            while self.step_values.len() <= max_step {
                self.eval_step();
            }
        }
        self.outputs_evaluated += num_outputs;
        self.stages_evaluated += 1;
        let mut out = Vec::new();
        for output_step in
            &self.comps[self.cur_label].output_steps[self.outputs_evaluated - num_outputs..self.outputs_evaluated]
        {
            out.push(self.step_values[*output_step].clone());
        }
        out
    }
    /// Evaluate an entire block
    /// Returns IO, PHY_OPS, VIR_OPS, INTER_COMP
    pub fn eval_block(&mut self, live_io: &(Vec<usize>, Vec<usize>), num_wit_reads: usize, num_phy_ops: usize, num_vir_ops: usize) -> 
        (Vec<Value>, Vec<Vec<Value>>, Vec<Vec<Value>>, Vec<Value>, Vec<Value>) 
    {
        debug_assert!(self.cur_label != self.exit_label);
        let mut wit = Vec::new();
        let mut phy_mem_patches = Default::default();
        let mut vir_mem_patches = Default::default();
        for i in 0..self.comps[self.cur_label].stages.len() {
            self.stages_evaluated = i;
            // Clear all patches on phy_mem and vir_mem
            self.phy_mem_patches = Default::default();
            self.vir_mem_patches = Default::default();
            wit.extend(self.eval_stage());
            if i == 0 {
                phy_mem_patches = self.phy_mem_patches.clone();
                vir_mem_patches = self.vir_mem_patches.clone();
            }
        }
        // Update phy_mem and vir_mem based on patches
        for (stack_index, value) in phy_mem_patches {
            // Append stack with entries until matches stack_index
            if stack_index >= self.phy_mem.len() {
                self.phy_mem.extend(vec![Default::default(); stack_index - self.phy_mem.len() + 1]);
            }
            self.phy_mem[stack_index] = value.clone();
        }
        for (heap_index, value) in vir_mem_patches {
            // Append heap with entries until matches heap_index
            if heap_index >= self.vir_mem.len() {
                self.vir_mem.extend(vec![Default::default(); heap_index - self.vir_mem.len() + 1]);
            }
            self.vir_mem[heap_index] = value.clone();
        }

        // Construct io = old_trans_regs[1..] | new_trans_regs[1..]
        let mut io = self.trans_regs[1..].to_vec();
        // Update trans_regs
        wit.drain(..live_io.0.len());
        for (i, r) in wit.drain(..live_io.1.len()).enumerate() {
            self.trans_regs[live_io.1[i]] = r;
        }
        io.extend(self.trans_regs[1..].to_vec());
        // Eval = io | wit
        let mut eval = io.clone();
        eval.extend(wit.clone());
        // Divide wit into io, phy_ops, vir_ops
        let phy_ops = wit.drain(..2 * num_phy_ops).chunks(2).into_iter().map(|c| c.collect()).collect();
        let vir_ops = wit.drain(..4 * num_vir_ops).chunks(4).into_iter().map(|c| c.collect()).collect();
        
        // Switch to the next block
        self.cur_label = self.trans_regs[R_BN].as_integer().unwrap().to_usize().unwrap();
        self.witness_offset += num_wit_reads;
        self.outputs_evaluated = 0;
        self.stages_evaluated = 0;
        self.step_values = Default::default();
        (io, phy_ops, vir_ops, eval, wit)
    }
}

#[cfg(test)]
mod test {

    use rug::Integer;

    use super::*;
    use circ_fields::FieldT;

    fn mk_inputs(v: Vec<(String, Sort)>) -> HashMap<String, Sort> {
        v.into_iter().collect()
    }

    #[test]
    fn one_const() {
        let mut comp = StagedWitComp::default();
        let field = FieldT::from(Integer::from(7));
        comp.add_stage(mk_inputs(vec![]), vec![pf_lit(field.new_v(0))]);

        let mut evaluator = StagedWitCompEvaluator::new(&comp);

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[0];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        assert!(evaluator.is_done());
    }

    #[test]
    fn many_const() {
        let mut comp = StagedWitComp::default();
        let field = FieldT::from(Integer::from(7));
        comp.add_stage(mk_inputs(vec![]), vec![pf_lit(field.new_v(0))]);
        comp.add_stage(
            mk_inputs(vec![]),
            vec![pf_lit(field.new_v(1)), pf_lit(field.new_v(4))],
        );
        comp.add_stage(mk_inputs(vec![]), vec![pf_lit(field.new_v(6))]);
        comp.add_stage(mk_inputs(vec![]), vec![pf_lit(field.new_v(0))]);

        let mut evaluator = StagedWitCompEvaluator::new(&comp);

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[0];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[1, 4];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[6];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[0];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        assert!(evaluator.is_done());
    }

    #[test]
    fn vars_one_stage() {
        let mut comp = StagedWitComp::default();
        let field = FieldT::from(Integer::from(7));
        comp.add_stage(mk_inputs(vec![("a".into(), Sort::Bool), ("b".into(), Sort::Field(field.clone()))]),
        vec![
            leaf_term(Op::Var("b".into(), Sort::Field(field.clone()))),
            term![Op::Ite; leaf_term(Op::Var("a".into(), Sort::Bool)), pf_lit(field.new_v(1)), pf_lit(field.new_v(0))],
        ]);

        let mut evaluator = StagedWitCompEvaluator::new(&comp);

        let output = evaluator.eval_stage(
            vec![
                ("a".into(), Value::Bool(true)),
                ("b".into(), Value::Field(field.new_v(5))),
            ]
            .into_iter()
            .collect(),
        );
        let ex_output: &[usize] = &[5, 1];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        assert!(evaluator.is_done());
    }

    #[test]
    fn vars_many_stages() {
        let mut comp = StagedWitComp::default();
        let field = FieldT::from(Integer::from(7));
        comp.add_stage(mk_inputs(vec![("a".into(), Sort::Bool), ("b".into(), Sort::Field(field.clone()))]),
        vec![
            leaf_term(Op::Var("b".into(), Sort::Field(field.clone()))),
            term![Op::Ite; leaf_term(Op::Var("a".into(), Sort::Bool)), pf_lit(field.new_v(1)), pf_lit(field.new_v(0))],
        ]);
        comp.add_stage(mk_inputs(vec![("c".into(), Sort::Field(field.clone()))]),
        vec![
            term![PF_ADD;
               leaf_term(Op::Var("b".into(), Sort::Field(field.clone()))),
               leaf_term(Op::Var("c".into(), Sort::Field(field.clone())))],
            term![Op::Ite; leaf_term(Op::Var("a".into(), Sort::Bool)), pf_lit(field.new_v(1)), pf_lit(field.new_v(0))],
            term![Op::Ite; leaf_term(Op::Var("a".into(), Sort::Bool)), pf_lit(field.new_v(0)), pf_lit(field.new_v(1))],
        ]);

        let mut evaluator = StagedWitCompEvaluator::new(&comp);

        let output = evaluator.eval_stage(
            vec![
                ("a".into(), Value::Bool(true)),
                ("b".into(), Value::Field(field.new_v(5))),
            ]
            .into_iter()
            .collect(),
        );
        let ex_output: &[usize] = &[5, 1];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        let output = evaluator.eval_stage(
            vec![("c".into(), Value::Field(field.new_v(3)))]
                .into_iter()
                .collect(),
        );
        let ex_output: &[usize] = &[1, 1, 0];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        assert!(evaluator.is_done());
    }
}
