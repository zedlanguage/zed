//! The benchmarks of operations on deep values, a test program of its own for the reason
//! deep_values.rs gives. Its tests are all benchmarks, in `bench/deep_scaling.rs`, so that
//! `tools/run_tests.sh` leaves them out of its default run and `--bench` runs them.

#[path = "bench/deep_scaling.rs"]
mod bench;
