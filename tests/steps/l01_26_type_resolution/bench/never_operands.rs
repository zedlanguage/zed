use zed_tests::scaling;

use super::super::never_operands::{below, chain_beside_never, max_of, never_beside_shared_tuples};
use super::super::scaling::resolved;

/// A chain of `n` additions beside one operand of type `Never`, each other operand a union of
/// `int` and `f64`, ending in `true`: each operator is checked once.
#[test]
fn a_chain_beside_never_scales() {
    let units = resolved(4000, chain_beside_never);
    scaling::check_order("a chain of n operators beside Never", 4000, 1, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
    });
}

/// A comparison of `Never` with a value of nested tuples that share their rows: each row is
/// visited once.
#[test]
fn a_comparison_of_never_with_shared_tuples_scales() {
    // The type of `t{d}` has `2^d` paths to `t0` and `d + 1` rows.
    let units = resolved(3200, |d| never_beside_shared_tuples(d, below));
    scaling::check_order("Never beside a tuple of n shared rows", 3200, 1, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// `max` of `Never` and a value of nested tuples that share their rows: each position of each
/// row is checked once.
#[test]
fn max_of_never_and_shared_tuples_scales() {
    let units = resolved(3200, |d| never_beside_shared_tuples(d, max_of));
    scaling::check_order("max of Never and a tuple of n shared rows", 3200, 1, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
