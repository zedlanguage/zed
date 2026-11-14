//! The emptiness search decides a type of any depth on a small stack: `is_empty`, `verdict`,
//! the difference of two deep types and `subtype` of two unequal ones keep their calls on the
//! heap (COMPLEXITY.md K39). Its own binary, so that the deep searches do not lengthen the piece
//! of step L1.23; its benchmarks are in `deep_search/bench.rs`.

use zed_kernel::Value;
use zed_kernel::types::{Type, Verdict};

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

/// The depth of the types of the regular tests: each search goes down and back up through
/// many levels of each shape, on the default test thread. The same checks at 10,000 levels,
/// past the depth at which a search by recursion overflowed a 2 MiB stack, are in `bench`
/// (TEST-bench-move-l0123, author P178: a test that needs an unusual depth is a benchmark).
const DEPTH: usize = 20;

/// `t` nested `DEPTH` deep around `0` is inhabited, by `is_empty` and by `verdict`.
fn decides(shape: fn(usize, Type) -> Type) {
    let t = shape(DEPTH, lit(0));
    assert!(!t.is_empty());
    assert_eq!(t.verdict(), Verdict::Inhabited);
}

#[test]
fn a_nested_tuple_type_is_decided() {
    decides(tuples);
}

#[test]
fn a_nested_atom_type_is_decided() {
    decides(atoms);
}

#[test]
fn a_nested_morphism_type_is_decided() {
    decides(morphisms);
}

/// Two types nested `DEPTH` deep that differ only at the bottom: the one around `0` is not
/// under the one around `1`, which the search decides on their difference, and is under the one
/// around `int`, which the simulation of rows shows.
fn compares(shape: fn(usize, Type) -> Type, bottom: Type, under: bool) {
    let t = shape(DEPTH, lit(0));
    assert_eq!(t.subtype(&shape(DEPTH, bottom)), under);
}

#[test]
fn a_nested_tuple_type_is_not_under_one_that_differs_at_the_bottom() {
    compares(tuples, lit(1), false);
}

#[test]
fn a_nested_tuple_type_is_under_one_wider_at_the_bottom() {
    compares(tuples, Type::int(), true);
}

#[test]
fn a_nested_morphism_type_is_not_under_one_that_differs_at_the_bottom() {
    compares(morphisms, lit(1), false);
}

#[test]
fn a_nested_morphism_type_is_under_one_wider_at_the_bottom() {
    compares(morphisms, Type::int(), true);
}

/// Atoms, nested `DEPTH` deep, compared both ways: a small instance of the comparison of
/// `bench::comparing_deep_atom_types_scales_with_depth`.
#[test]
fn a_nested_atom_type_is_compared_by_its_bottom() {
    compares(atoms, lit(1), false);
    compares(atoms, Type::int(), true);
}

#[path = "deep_search/bench.rs"]
mod bench;
