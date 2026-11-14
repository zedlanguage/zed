//! The full test battery: tests that need tools outside the Rust toolchain, such as emulators,
//! containers, databases and other languages' compilers. Each folder lists its tools in a file
//! `needs`. `tools/run_tests.sh --full` runs these after the local suite, and stops first if a
//! tool is missing, so no test here is ever skipped. Plain `cargo test` does not build them.

mod l01_21_test_runner;
mod m0_04_corpus_references;
mod m0_09_kernel_evaluator;
mod s00_01_tools;
