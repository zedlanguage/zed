//! The explanations of `emptied.rs` at `n` and `8n`.

use zed_tests::scaling;

use crate::emptied::*;

#[test]
fn explaining_a_union_of_n_empty_tuples_scales() {
    let n = 14_000;
    let inputs = scaling::inputs(n, wide);
    scaling::check("explaining a union of n empty tuples", n, |k| {
        a_union_of_empty_tuples_explained(&inputs[&k], k);
    });
}

#[test]
fn explaining_n_nested_empty_tuples_scales() {
    let n = 13_000;
    let inputs = scaling::inputs(n, deep);
    scaling::check("explaining n nested empty tuples", n, |k| {
        nested_empty_tuples_explained(&inputs[&k], k);
    });
}
