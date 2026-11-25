//! The benchmarks of provenance, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-rest). Each check they make besides the ratio is made at small sizes in
//! `scaling.rs`.

use zed_tests::scaling::{check, inputs};

use crate::scaling::{
    countdown, finds_the_origins_of_each_member, finds_the_term_of_every_fact, product_of_atoms,
    records_the_recursion, sum_of_ones,
};

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

#[test]
fn the_origins_of_a_failure_with_many_members_scale() {
    // The product of `n` distinct loose atoms: its `#errs` has `n` members, each first
    // appearing at its literal. Each member's search tested every input fact by walking its
    // value, an `#errs` of up to `n` members: `O(n² log n)` steps. Deferred by
    // TESTS-scaling-limit-10_5 (11.1 times the bytes at 64 and 512 on cdf07ac4f); back with
    // row PROV-scaling-10_5.
    let terms = inputs(64, product_of_atoms);
    check("the origins of an n-member failure, by n", 64, |n| {
        finds_the_origins_of_each_member(&terms[&n], n);
    });
}
