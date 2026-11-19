//! Building units and writing their text are of order n log n in the length of the text, and
//! the depth of nested functions and `else if` chains is bounded by memory alone (DESIGN.md
//! Part G). Each text is lexed and parsed before timing, so the checks time the building, or
//! the writing, alone. The benchmarks of this step, run by `tools/run_tests.sh --bench`;
//! `scaling.rs` makes each of their checks at small sizes.

use std::collections::HashMap;

use zed_tests::scaling::{check, inputs};
use zed_tests::trees::parsed;
use zedc::ast::unit;
use zedc::rejection::Row;

use super::scaling::{
    Case, ELSE_IF_CHAIN, MANY_FUNCTIONS, NESTED_FUNCTIONS, Parsed,
    bindings_before_a_generation_push, builds, loops_with_generation_pushes, nested, statements,
    texts, texts_hold,
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

/// Placing a generation push walks the tree once per unit, however many pushes it holds
/// (COMPLEXITY.md, PUSH-target-rules).
#[test]
fn placing_generation_pushes_is_linear() {
    let many = inputs(500, |n| {
        parsed(bindings_before_a_generation_push(n), "Unit")
    });
    check("n bindings before `x' <- 1;` outside a loop", 500, |n| {
        let (text, tokens, tree) = &many[&n];
        let e = unit(text, tokens, tree).unwrap_err();
        assert_eq!(e.row, Some(Row::GenerationPushOutsideLoop));
    });
    let loops = inputs(500, |n| parsed(loops_with_generation_pushes(n), "Unit"));
    check("n loops, each with a generation push", 500, |n| {
        let (text, tokens, tree) = &loops[&n];
        assert_eq!(unit(text, tokens, tree).unwrap().len(), n);
    });
}

/// The text of functions nested 100,000 deep, deeper than a recursion fits on the call stack
/// (author P178: an unusual size is a benchmark); the same at small depths is checked by
/// `scaling::the_text_of_functions_nested_a_few_deep`.
#[test]
fn the_text_of_functions_nested_deeper_than_the_call_stack() {
    let n = 100_000;
    let text = statements(nested(n))[0].to_string();
    assert!(text.starts_with(&"(def f (x) (block ".repeat(1000)));
    assert!(text.ends_with(&format!("(block (return x))){}", "))".repeat(n - 1))));
}
