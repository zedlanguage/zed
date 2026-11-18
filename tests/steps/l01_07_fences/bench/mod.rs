//! The benchmarks of the fences, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-rest). Each check they make besides the ratio is made at small sizes by
//! a correctness test of the module whose name each file bears.

mod keys;
mod mathlib;
#[cfg(feature = "spec")]
mod readme;
mod scaling;
