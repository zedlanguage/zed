//! The emptiness search decides a type of any depth on a small stack: `is_empty`, `verdict`,
//! the difference of two deep types and `subtype` of two unequal ones keep their calls on the
//! heap (COMPLEXITY.md K39). Its own binary, so that the deep searches do not lengthen the piece
//! of step L1.23; its benchmarks are in `deep_search/bench.rs`.

use zed_kernel::Value;
use zed_kernel::types::{Type, Verdict};
use zed_tests::scaling;

fn lit(i: i64) -> Type {
    Type::lit(&Value::Int(i)).expect("an integer literal")
}

/// A type nested `n` deep in tuples, `(.., 1)`.
fn tuples(n: usize, bottom: Type) -> Type {
    (0..n).fold(bottom, |t, _| Type::tuple(vec![t, lit(1)]))
}

/// A type nested `n` deep in atom payloads, `a(..)`.
fn atoms(n: usize, bottom: Type) -> Type {
    (0..n).fold(bottom, |t, _| Type::atom_with("a", &Type::tuple(vec![t])))
}

/// A type nested `n` deep in the values of morphisms, `{int: ..}`.
fn morphisms(n: usize, bottom: Type) -> Type {
    (0..n).fold(bottom, |t, _| Type::exact(Type::int(), t))
}

/// The search overflowed a 2 MiB stack some thousands of levels down when it recursed; here it
/// goes 10,000, past that depth and no deeper, so that each test stays short (author P169: the
/// smallest depth that overflows a default stack). It went 100,000 until TEST-bench-move-l0123.
const DEEP: usize = 10_000;

/// `t` nested `DEEP` deep around `0` is inhabited, by `is_empty` and by `verdict`.
fn decides_deep(shape: fn(usize, Type) -> Type) {
    zed_tests::deep::on_small_stack(move || {
        let t = shape(DEEP, lit(0));
        assert!(!t.is_empty());
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}

#[test]
fn a_tuple_type_far_deeper_than_the_stack_is_decided() {
    decides_deep(tuples);
}

#[test]
fn an_atom_type_far_deeper_than_the_stack_is_decided() {
    decides_deep(atoms);
}

#[test]
fn a_morphism_type_far_deeper_than_the_stack_is_decided() {
    decides_deep(morphisms);
}

/// Two types nested `DEEP` deep that differ only at the bottom: the one around `0` is not under
/// the one around `1`, which the search decides on their difference, and, in a test of its own,
/// is under the one around `int`, which the simulation of rows shows. Tuples split the box on
/// their way down and morphisms meet and subtract their fields at each level; atoms do neither,
/// and theirs are compared in a test of their own and in the benchmarks. A morphism comparison
/// 100,000 levels deep took 9.1 s in the optimized test build at load 22 (EMPTY-morphism-next,
/// 2026-11-07).
fn compares_deep(shape: fn(usize, Type) -> Type, bottom: Type, under: bool) {
    zed_tests::deep::on_small_stack(move || {
        let t = shape(DEEP, lit(0));
        assert_eq!(t.subtype(&shape(DEEP, bottom)), under);
    });
}

#[test]
fn a_deep_tuple_type_is_not_under_one_that_differs_at_the_bottom() {
    compares_deep(tuples, lit(1), false);
}

#[test]
fn a_deep_tuple_type_is_under_one_wider_at_the_bottom() {
    compares_deep(tuples, Type::int(), true);
}

#[test]
fn a_deep_morphism_type_is_not_under_one_that_differs_at_the_bottom() {
    compares_deep(morphisms, lit(1), false);
}

#[test]
fn a_deep_morphism_type_is_under_one_wider_at_the_bottom() {
    compares_deep(morphisms, Type::int(), true);
}

/// Atoms, nested `DEEP` deep, compared both ways: a small instance of the comparison of
/// `bench::deciding_and_comparing_deep_atom_types_scale_with_depth`.
#[test]
fn a_deep_atom_type_is_compared_by_its_bottom() {
    compares_deep(atoms, lit(1), false);
    compares_deep(atoms, Type::int(), true);
}

/// Deciding, the verdict and the subtype of types nested `n` and `8n` deep in
/// `shape`.
fn scales(what: &str, shape: fn(usize, Type) -> Type) {
    let n = 500;
    zed_tests::deep::on_small_stack(|| {
        let built = |k: usize| (shape(k, lit(0)), shape(k, lit(1)), shape(k, Type::int()));
        let (small, large) = (built(n), built(8 * n));
        let at = |k: usize| if k == n { &small } else { &large };
        // Each run is on a thread of its own, so it finds no answer kept by another.
        scaling::check(&format!("deciding {what}"), n, |k| {
            assert!(!at(k).0.is_empty());
        });
        scaling::check(&format!("the verdict on {what}"), n, |k| {
            assert_eq!(at(k).0.verdict(), Verdict::Inhabited);
        });
        scaling::check(&format!("comparing {what}"), n, |k| {
            let (t, u, int) = at(k);
            assert!(!t.subtype(u) && t.subtype(int));
        });
    });
}

#[path = "deep_search/bench.rs"]
mod bench;
