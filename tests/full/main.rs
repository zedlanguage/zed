//! The full test battery: tests that need tools outside the Rust toolchain, such as emulators,
//! containers, databases and other languages' compilers. Each folder lists its tools in a file
//! `needs`. `tools/run_tests.sh --full` runs these after the local suite, and stops first if a
//! tool is missing, so no test here is ever skipped. Plain `cargo test` does not build them.

mod s00_01_tools;
