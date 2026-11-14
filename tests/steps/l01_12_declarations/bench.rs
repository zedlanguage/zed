//! Building units and writing their text are of order n log n in the length of the text, and
//! the depth of nested functions and `else if` chains is bounded by memory alone (DESIGN.md
//! Part G). Each text is lexed and parsed before timing, so the checks time the building, or
//! the writing, alone. The benchmarks of this step, run by `tools/run_tests.sh --bench`;
//! `scaling.rs` makes each of their checks at small sizes.

use std::collections::HashMap;

use zed_tests::scaling::{check, inputs};
use zed_tests::trees::parsed;

use super::scaling::{
    Case, ELSE_IF_CHAIN, MANY_FUNCTIONS, NESTED_FUNCTIONS, Parsed, builds, texts, texts_hold,
};

/// The units of `case` at `n` and `8n`, lexed and parsed before any run is timed.
fn trees(case: &Case, n: usize) -> HashMap<usize, Parsed> {
    inputs(n, |m| parsed((case.text)(m), "Unit"))
}

#[test]
fn many_functions_and_a_long_test_table_scale() {
    let built = trees(&MANY_FUNCTIONS, 200);
    check("building n functions and a table of n rows", 200, |n| {
        builds(&MANY_FUNCTIONS, &built[&n], n)
    });
}

#[test]
fn nested_functions_scale() {
    let built = trees(&NESTED_FUNCTIONS, 200);
    check("building functions nested n deep", 200, |n| {
        builds(&NESTED_FUNCTIONS, &built[&n], n)
    });
}

#[test]
fn the_text_of_nested_functions_and_of_a_long_sum_scales() {
    let built = inputs(125, texts);
    check(
        "writing functions nested n deep and a sum of 4n terms",
        125,
        |n| {
            let (def, sum) = &built[&n];
            texts_hold(def, sum, n);
        },
    );
}

#[test]
fn a_long_else_if_chain_scales() {
    let built = trees(&ELSE_IF_CHAIN, 200);
    check("building an else if chain of n links", 200, |n| {
        builds(&ELSE_IF_CHAIN, &built[&n], n)
    });
}
