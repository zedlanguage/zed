//! The benchmarks of `hooks`, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates, author P178: a test that needs an unusual size, here a depth past
//! what the default test stack holds by recursion, is a benchmark). Each runs a check of
//! `tests` at a million levels, which shows that `term` and `rename` do not recurse once per
//! level; what each checks besides is checked at a small depth by the test of `tests` named on it.

use super::tests::{
    a_chain_of_closures_of_depth_becomes_a_term,
    binders_of_a_pattern_of_depth_are_renamed_in_preorder,
};

/// How deep the benchmarks go, on the default test stack; each old function overflowed it.
const DEPTH: usize = 1_000_000;

/// At a small depth: `tests::a_chain_of_closures_becomes_a_term`.
#[test]
fn a_chain_of_closures_becomes_a_term() {
    a_chain_of_closures_of_depth_becomes_a_term(DEPTH);
}

/// At a small depth: `tests::binders_of_a_nested_pattern_are_renamed_in_preorder`.
#[test]
fn binders_of_a_deep_pattern_are_renamed_in_preorder() {
    binders_of_a_pattern_of_depth_are_renamed_in_preorder(DEPTH);
}
