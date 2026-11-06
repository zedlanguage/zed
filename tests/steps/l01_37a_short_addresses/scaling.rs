//! Scaling at the rule of low complexity (DESIGN.md Part G) of what step L1.37a adds: the
//! ordering by shape of the nodes of one key in the lowering (`canon::Shape`), and the
//! numbering of a unit's definitions that keys the query database (`Db::cone`). Inputs are
//! built before the runs are measured.

use std::collections::HashMap;

use zed_kernel::term::build::{lam, var};
use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling::check_order;
use zedc::zir::lower::lower;

/// `(m) -> m + 0 + 1 + … + (n - 1)`, a lambda whose body holds `n` nodes.
fn long_lambda(n: usize) -> Term {
    let mut body = var("m");
    for i in 0..n {
        body = Term::Prim(Prim::Add, vec![body, Term::Lit(Value::Int(i as i64))]);
    }
    lam(&["m"], body)
}

#[test]
fn confirming_a_key_reads_each_node_once() {
    // Two equal lambdas built apart: the second's key is found, and confirming it compares
    // the two bodies node by node.
    let (n, sizes) = (500, [500, 4000]);
    let inputs: HashMap<usize, Term> = sizes
        .into_iter()
        .map(|k| {
            let t = Term::Prim(Prim::Tuple, vec![long_lambda(k), long_lambda(k)]);
            (k, t)
        })
        .collect();
    check_order(
        "lowering two equal lambdas built apart, by body size",
        n,
        1,
        |k| {
            let g = lower(&inputs[&k]).expect("two lambdas lower");
            assert_eq!(
                zed_tests::step_helpers::l01_33_lowering::count(&g, "lambda"),
                1
            );
        },
    );
}

#[test]
fn many_equal_nodes_are_found_by_their_keys() {
    let (n, sizes) = (500, [500, 4000]);
    let inputs: HashMap<usize, Term> = sizes
        .into_iter()
        .map(|k| {
            let sum = |i: usize| {
                Term::Prim(
                    Prim::Add,
                    vec![Term::Lit(Value::Int(i as i64)), Term::Lit(Value::Int(1))],
                )
            };
            let parts = (0..k).map(sum).chain((0..k).map(sum)).collect();
            (k, Term::Prim(Prim::Tuple, parts))
        })
        .collect();
    check_order("lowering n sums, each built twice apart, by n", n, 1, |k| {
        let g = lower(&inputs[&k]).expect("sums lower");
        assert_eq!(
            zed_tests::step_helpers::l01_33_lowering::count(&g, "prim"),
            k + 1
        );
    });
}

#[test]
fn numbering_the_definitions_of_a_unit_scales() {
    // `n` definitions, each with one table row: each row's key numbers the definitions its
    // cone reaches, and each definition is numbered once for the database.
    let (n, sizes) = (40, [40, 320]);
    let inputs: HashMap<usize, String> = sizes
        .into_iter()
        .map(|k| {
            let text: String = (0..k)
                .map(|i| format!("g{i}(positional x) = x + {i}\ntest {{ 1 -> {} }}\n", i + 1))
                .collect();
            (k, text)
        })
        .collect();
    check_order("checking the tables of n definitions, by n", n, 1, |k| {
        let out = zedc::testing::test(&inputs[&k]);
        assert_eq!(out.len(), k, "{:?}", out.first());
        assert!(out.iter().all(|o| o.failure.is_none()));
    });
}
