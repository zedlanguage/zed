//! The benchmarks of step L1.18, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-split). Each file holds those of the correctness file of its name,
//! which builds their inputs and checks each at a small size, as it does every check they make
//! besides the ratio.

mod literals;
mod prim_names;
mod scaling;
mod sqrt_fma;
mod tuple_min_max;
mod word_args;
