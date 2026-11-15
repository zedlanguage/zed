//! Parsing, building and checking a chain of infix calls is linear in its length.

use zed_tests::scaling;

use crate::scaling::{chain, pass, rejected_chain};

#[test]
fn a_chain_of_infix_calls_scales() {
    scaling::check("a chain of n infix calls", 2_000, |n| {
        assert!(!zedc::query::Db::new().front(&chain(n)).is_err());
    });
}

#[test]
fn a_rejected_chain_of_infix_calls_scales() {
    scaling::check("a chain of n infix calls ending in `* 2`", 2_000, |n| {
        assert!(zedc::query::Db::new().front(&rejected_chain(n)).is_err());
    });
}

/// The builder holds its work on the heap: a chain far deeper than a recursive walk of a test
/// thread's 2 MiB stack holds is accepted, and rejected at its end.
#[test]
fn a_deep_chain_runs_on_a_test_thread() {
    pass(4_000);
}
