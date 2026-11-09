//! Scaling at the rule of low complexity (DESIGN.md Part G) of what step L1.37a adds: the
//! ordering by shape of the nodes of one key in the lowering (`canon::Shape`), and the
//! numbering of a unit's definitions that keys the query database (`Db::cone`), and the
//! thread's tables of live rows, morphism types and set nodes, whose buckets hold the nodes
//! that tie in digest (step TABLE-short-scan). Inputs are built before the runs are measured.

use std::collections::HashMap;

use zed_kernel::term::build::{lam, var};
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling::{check_order, inputs};
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

#[test]
fn rows_and_morphism_types_that_tie_in_digest_are_found_and_dropped_in_log_time() {
    // `n` tuple types `(aᵢ)` and morphism types `(aᵢ ⊆ dom ⊆ aᵢ) -> aᵢ` over distinct atoms,
    // each made twice, the second found in the tables, then all dropped. With
    // `short-addresses` the digests keep 8 bits. The atoms are chosen so that their digests
    // all tie, so every tuple type, every morphism type and every set node over them ties too:
    // one bucket of each table holds all n of them, and a lookup or a drop that read its whole
    // bucket would make the run quadratic. In the full build the filter keeps one name in 256
    // and each bucket holds one node.
    //
    // Atoms taken in order spread over many buckets instead, each of a fixed fraction b of n,
    // so a lookup costs about 2 ln(bn) steps of about 2,000 instructions each (815 since
    // BUCKET-cmp-cost): n log n, but with log(bn) in place of log n the ratio between n and 8n
    // exceeds the limit at every size that runs in 60 s. That input took 13.1 times the work
    // from 2,000 to 16,000 against the limit 11.2, with 5.5, 9.8 and 13.8 comparisons per lookup
    // at 2,000, 16,000 and 128,000 (SCALE-fix-37a-digest). With one bucket it took 10.3 times,
    // and 10.1 times with half the work since BUCKET-cmp-cost cut the cost of a step; a lookup
    // that compares one node in 64 of its bucket besides its path takes 43 times.
    let n = 2000;
    let tie = super::collide::digest(&Type::atom("a0")) & 0xff;
    let atoms = inputs(n, |k| {
        (0..)
            .map(|i| Type::atom(&format!("a{i}")))
            .filter(|a| super::collide::digest(a) & 0xff == tie)
            .take(k)
            .collect::<Vec<_>>()
    });
    check_order(
        "making n rows and n morphism types twice, then dropping them, by n",
        n,
        1,
        |k| {
            let make = || -> Vec<Type> {
                atoms[&k]
                    .iter()
                    .flat_map(|a| {
                        [
                            Type::tuple(vec![a.clone()]),
                            Type::morphism(a.clone(), a.clone(), a.clone()),
                        ]
                    })
                    .collect()
            };
            let (first, second) = (make(), make());
            assert_eq!(first, second);
        },
    );
}
