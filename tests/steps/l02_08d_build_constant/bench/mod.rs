//! The benchmarks of the build constant, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-rest). Each check they make besides the ratio is made at small
//! sizes by a correctness test of the module whose name each file bears.

mod scaling;
#[cfg(target_os = "linux")]
mod staged;
#[cfg(target_os = "linux")]
mod test_staged;
