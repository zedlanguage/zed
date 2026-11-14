//! The benchmarks of `main … with handles(…)` (plan row SPEC-sigint-override), run by
//! `tools/run_tests.sh --bench` and left out of its default run (TEST-bench-split). Each check
//! they make besides the ratio has a small instance among the correctness tests in
//! `signals.rs`.

use zed_tests::scaling::{check, inputs};
use zedc::rejection::Row;

use super::signals::{REPEATS_REPAIR, built, reads, repeats};

#[test]
fn a_handles_with_n_repeated_arguments_is_rejected_in_linear_time() {
    const N: usize = 140_000;
    let srcs = inputs(N, repeats);
    check("rejecting handles with n repeated arguments", N, |n| {
        let error = built(&srcs[&n]);
        assert!(error.message.ends_with(REPEATS_REPAIR), "{}", error.message);
    });
}

#[test]
fn n_reads_of_signals_without_handles_are_rejected_in_linear_time() {
    const N: usize = 36_000;
    let srcs = inputs(N, reads);
    check("rejecting n reads of m.signals without handles", N, |n| {
        assert_eq!(built(&srcs[&n]).row, Some(Row::SignalsReadWithoutHandles));
    });
}
