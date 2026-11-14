//! Scaling at the rule of low complexity (DESIGN.md Part G) of what step L1.37a adds: the
//! ordering by shape of the nodes of one key in the lowering (`canon::Shape`), and the
//! numbering of a unit's definitions that keys the query database (`Db::cone`), and the
//! thread's tables of live rows, morphism types and set nodes, whose buckets hold the nodes
//! that tie in digest (step TABLE-short-scan). The inputs and checks of the benchmarks in
//! `bench.rs`, each run here at a small size.

use zed_kernel::term::build::{lam, var};
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term, Value};
use zed_tests::step_helpers::l01_33_lowering::count;
use zedc::zir::lower::lower;

/// `(m) -> m + 0 + 1 + … + (n - 1)`, a lambda whose body holds `n` nodes.
fn long_lambda(n: usize) -> Term {
    let mut body = var("m");
    for i in 0..n {
        body = Term::Prim(Prim::Add, vec![body, Term::Lit(Value::Int(i as i64))]);
    }
    lam(&["m"], body)
}

/// Two equal lambdas of [`long_lambda`] at `n`, built apart, in a tuple.
pub(super) fn equal_lambdas(n: usize) -> Term {
    Term::Prim(Prim::Tuple, vec![long_lambda(n), long_lambda(n)])
}

/// Lowers [`equal_lambdas`]: the second's key is found, and confirming it compares the two
/// bodies node by node, so the graph holds one lambda.
pub(super) fn lowers_to_one_lambda(t: &Term) {
    let g = lower(t).expect("two lambdas lower");
    assert_eq!(count(&g, "lambda"), 1);
}

#[test]
fn two_equal_lambdas_built_apart_are_one_node() {
    lowers_to_one_lambda(&equal_lambdas(5));
}

/// `n` sums `i + 1`, each built twice apart, in a tuple.
pub(super) fn sums_twice(n: usize) -> Term {
    let sum = |i: usize| {
        Term::Prim(
            Prim::Add,
            vec![Term::Lit(Value::Int(i as i64)), Term::Lit(Value::Int(1))],
        )
    };
    Term::Prim(
        Prim::Tuple,
        (0..n).map(sum).chain((0..n).map(sum)).collect(),
    )
}

/// Lowers [`sums_twice`] at `n`: each sum is one node, and the tuple one more.
pub(super) fn each_sum_is_one_node(t: &Term, n: usize) {
    let g = lower(t).expect("sums lower");
    assert_eq!(count(&g, "prim"), n + 1);
}

#[test]
fn sums_built_twice_apart_are_one_node_each() {
    each_sum_is_one_node(&sums_twice(3), 3);
}

/// `n` definitions, each with one table row.
pub(super) fn tables(n: usize) -> String {
    (0..n)
        .map(|i| format!("g{i}(positional x) = x + {i}\ntest {{ 1 -> {} }}\n", i + 1))
        .collect()
}

/// Checks the tables of [`tables`] at `n`: each row's key numbers the definitions its cone
/// reaches, and each definition is numbered once for the database; each of the `n` rows
/// passes.
pub(super) fn every_table_passes(text: &str, n: usize) {
    let out = zedc::testing::test(text);
    assert_eq!(out.len(), n, "{:?}", out.first());
    assert!(out.iter().all(|o| o.failure.is_none()));
}

#[test]
fn the_tables_of_several_definitions_pass() {
    every_table_passes(&tables(3), 3);
}

/// The first `n` atoms `a<i>` whose digests keep the same low 8 bits as that of `a0`.
pub(super) fn tied_atoms(n: usize) -> Vec<Type> {
    let tie = super::collide::digest(&Type::atom("a0")) & 0xff;
    (0..)
        .map(|i| Type::atom(&format!("a{i}")))
        .filter(|a| super::collide::digest(a) & 0xff == tie)
        .take(n)
        .collect()
}

/// Makes the tuple type `(a)` and the morphism type `(a ⊆ a ⊆ a) -> a` of each of `atoms`
/// twice, the second found in the tables, then drops them all: the two are equal.
pub(super) fn made_twice_and_dropped(atoms: &[Type]) {
    let make = || -> Vec<Type> {
        atoms
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
}

#[test]
fn rows_and_morphism_types_that_tie_in_digest_are_found_and_dropped() {
    let atoms = tied_atoms(3);
    assert_eq!(atoms.len(), 3);
    made_twice_and_dropped(&atoms);
}
