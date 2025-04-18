# CoBBl: SNARK over Basic Blocks

CoBBl is a full-stack SNARK system that divides a computation into blocks and verify their correctness in parallel. CoBBl is divided into two components:

#### CirC Blocks
A front-end SNARK compiler based on CirC that divides a program into blocks and generates all constraints related to verification.

#### Spartan Parallel
A modified Spartan proof system that supports data-parallelism and additional properties.

## Running the program
* First set up all compilers: `bash setup.sh`
* Next run the proof system on all benchmarks: `python3 tester.py`
* Finally generate the result: `python3 plotter.py > output`

## Output Format
A sample output can be viewed in `./output`
Generated graphs can be viewed in `./graphs/`

Time comparison is consisted of a 9 x 4 table, corresponding to 4 metrics on 9 benchmarks.
Size comparison is consisted of a 9 x 5 table.

#### Benchmarks
* `CirC`: modified CirC compiler + unmodified Spartan
* `CoBBl For`: CoBBl proof on the exact same code as CirC (no while loops)
* `Jolt`: unmodified Jolt
* `CoBBl While`: CoBBl with while loops with number of iterations = upper bound
* `CoBBl Opt0`: CoBBl with no optimization
* `CoBBl Opt`: CoBBl with block merge analysis
* `CoBBl Opt`: CoBBl with register spilling but performed within the heap (as opposed to the stack)
* `CoBBl 75`: Program with while loops with number of iterations = 0.75 x upper bound
* `CoBBl 50`: Program with while loops with number of iterations = 0.50 x upper bound

#### Time Metrics
* `Compiler`: time to convert the code into constraints
* `Preprocess`: time of one-time setup, mostly instance commitment, not applicable to Jolt
* `Prover`: prover setup time from witnesses to proof generation, excluding actual program execution
* `Verifier`: verification time, includes every computation performed by the verifier

#### Size Metrics
* `Block`: number of blocks, only applicable to CoBBl
* `Commit`: total number of non-zero entries of the circuit(s)
* `Var`: total number of witnesses supplied by the prover
* `Exec`: total number of constraints executed throughout the proof
* `Proof`: size of the SNARK proof