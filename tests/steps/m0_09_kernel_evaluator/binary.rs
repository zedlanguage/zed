//! The zedc executable, run as a user runs it, on a value deeper than the minimum of 20,000
//! nested calls (DESIGN.md step M0.11). `crates/zed-native/Cargo.toml` names this test program,
//! since only a test of that package can name the executable. Its one test is a benchmark, in
//! `bench/zedc_deep.rs`, so that `tools/run_tests.sh` leaves it out of its default run and
//! `--bench` runs it; the evaluator's comparison of deep values runs at small depths in
//! `deep_values.rs`, and zedc runs programs at ordinary sizes in step L1.36a.

#[path = "bench/zedc_deep.rs"]
mod bench;
