//! The benchmarks of provenance, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-rest). Each check they make besides the ratio is made at small sizes in
//! `scaling.rs`.

use zed_tests::scaling::{check, inputs};

use crate::scaling::{countdown, finds_the_term_of_every_fact, records_the_recursion, sum_of_ones};

#[test]
fn recording_a_deep_recursion_scales() {
    // Each fact copied the call sites it was inside: the facts of a recursion of depth `n`
    // held `n²/2` of them.
    let terms = inputs(1000, countdown);
    check("the provenance of a recursion, by depth", 1000, |n| {
        records_the_recursion(&terms[&n], n);
    });
}

#[test]
fn the_term_of_every_fact_scales() {
    // The term at a node is found by walking the term in preorder to its position, so
    // reading the term of each of the `O(n)` facts of an `n`-node term one at a time took
    // `O(n²)` steps (ratio 61). `fact_terms()` finds each distinct position once, from its
    // parent.
    let terms = inputs(1000, sum_of_ones);
    check("the term at each fact, by term size", 1000, |n| {
        finds_the_term_of_every_fact(&terms[&n], n);
    });
}
