//! Building a syntax tree is of order n log n in the length of the text, and its depth is
//! bounded by memory alone (DESIGN.md Part G). Each text is lexed and parsed before timing, so
//! the checks time the building alone. The benchmarks of this step, run by
//! `tools/run_tests.sh --bench`; `scaling.rs` builds each of their trees at small sizes.

use std::collections::HashMap;

use zed_tests::scaling::{check, inputs};
use zed_tests::trees::parsed;

use super::scaling::{CHAIN, Case, HOLES, NEGATIONS, Parsed, builds};

/// The texts of `case` at `n` and `8n`, lexed and parsed before any run is timed.
fn trees(case: &Case, n: usize) -> HashMap<usize, Parsed> {
    inputs(n, |m| parsed((case.text)(m), "Expr"))
}

#[test]
fn a_long_chain_scales() {
    let built = trees(&CHAIN, 200);
    check("building a chain of 4n links", 200, |n| {
        builds(&CHAIN, &built[&n], n)
    });
}

#[test]
fn deep_nesting_scales() {
    let built = trees(&NEGATIONS, 500);
    check("building calls and negations nested n deep", 500, |n| {
        builds(&NEGATIONS, &built[&n], n)
    });
}

#[test]
fn nested_string_holes_scale() {
    let built = trees(&HOLES, 100);
    check("building string holes nested n deep", 100, |n| {
        builds(&HOLES, &built[&n], n)
    });
}
