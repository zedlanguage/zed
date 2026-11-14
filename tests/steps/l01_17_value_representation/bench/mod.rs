//! The benchmarks of step L1.17, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-split). Each file holds those of the correctness file of its name,
//! which builds their inputs and checks each at a small size, as it does every check they make
//! besides the ratio.

mod asks;
mod fields;
mod in_place;
mod memory_check;
mod powers;
mod products;
mod string_copies;
mod subquadratic;
