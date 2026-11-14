//! The benchmarks of step L1.36, one file for each file of correctness tests they came from,
//! run by `tools/run_tests.sh --bench` and left out of its default run (TEST-bench-split). Each
//! check they make besides the ratio has a small instance among the correctness tests of the
//! file of the same name.

mod deep_calls;
mod drops;
mod function_binders;
mod kernel_inputs;
mod kinds;
mod legalize;
mod minmax;
mod release_order;
mod scaling;
mod shared_closures;
mod shared_values;
mod string_scaling;
mod table;
