use zed_tests::scaling;

use super::super::is_chains::{balanced, chain, names_chain, right_chain, test_or_comparison};

/// Checks the units `text(m)` at `n` and `8n`, read and resolved before the timing, for work
/// of order n log n at most: each fact of the chain is narrowed once and moved at most log2 n
/// times.
fn scales(what: &str, text: impl Fn(usize) -> String + Sync) {
    let n = 4000;
    let built = scaling::inputs(n, |m| zed_tests::deep::resolved(&text(m)));
    scaling::check_order(what, n, 1, |m| {
        let (stmts, res) = &built[&m];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{what}: {:?}", info.errors);
    });
}

/// Besides its ratio: no type error. Small instance, of each shape:
/// `is_chains::chains_and_trees_of_is_tests_are_accepted`.
#[test]
fn a_chain_of_is_tests_nested_to_the_left_scales() {
    scales("a chain of n `x is int` joined by `&&`", |k| {
        chain(k, "&&", |_| "x is int".into())
    });
}

/// Besides its ratio: no type error. Small instance, of each shape:
/// `is_chains::chains_and_trees_of_is_tests_are_accepted`.
#[test]
fn a_chain_of_is_tests_nested_to_the_right_scales() {
    scales("a chain of n `x is int`, each `&&` with the rest", |k| {
        right_chain(k, |_| "x is int".into())
    });
}

/// Besides its ratio: no type error. Small instance, of each shape:
/// `is_chains::chains_and_trees_of_is_tests_are_accepted`.
#[test]
fn a_chain_of_is_tests_and_comparisons_scales() {
    scales("a chain of n `is` tests and comparisons", |k| {
        chain(k, "&&", test_or_comparison)
    });
}

/// Besides its ratio: no type error. Small instance, of each shape:
/// `is_chains::chains_and_trees_of_is_tests_are_accepted`.
#[test]
fn a_chain_of_is_tests_and_comparisons_nested_to_the_right_scales() {
    scales(
        "a chain of n `is` tests and comparisons nested right",
        |k| right_chain(k, test_or_comparison),
    );
}

/// Besides its ratio: no type error. Small instance, of each shape:
/// `is_chains::chains_and_trees_of_is_tests_are_accepted`.
#[test]
fn a_chain_of_is_tests_of_many_names_scales() {
    scales("a chain of `is` tests of n names", names_chain);
}

/// Besides its ratio: no type error. Small instance, of each shape:
/// `is_chains::chains_and_trees_of_is_tests_are_accepted`.
#[test]
fn a_chain_of_is_tests_joined_by_or_scales() {
    scales("a chain of n `x is int` joined by `||`", |k| {
        chain(k, "||", |_| "x is int".into())
    });
}

/// Besides its ratio: no type error. Small instance, of each shape:
/// `is_chains::chains_and_trees_of_is_tests_are_accepted`.
#[test]
fn a_balanced_tree_of_is_tests_scales() {
    // Each join moves the shorter list of facts onto the longer, so a fact moves once per
    // level of the tree: n log n.
    scales("a balanced tree of n `x is int` joined by `&&`", balanced);
}
