//! The benchmarks of the polynomial decision, run by `tools/run_tests.sh --bench` and left out
//! of its default run (TEST-bench-move-rest). Each check they make besides the ratio, or besides
//! the time in `calibration.rs`, is made at small sizes by a correctness test of the module
//! whose name each file bears.

mod calibration;
mod choice;
mod factored;
mod scaling;
