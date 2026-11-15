//! The benchmarks of the emptiness search, run by `tools/run_tests.sh --bench` and left out of
//! its default run (TEST-bench-move-crates). Each check they make besides the ratio has a small
//! instance among the correctness tests in `tests.rs`, named at each benchmark.

use super::tests::rings;
use super::*;

/// Checks the families `range` of [`rings`] at 64 and 512 types.
fn rings_scale(range: std::ops::Range<usize>) {
    let families = crate::scaling::inputs(2048, rings);
    for i in range {
        let (what, _, _) = rings(1).swap_remove(i);
        crate::scaling::check(what, 2048, |k| {
            let (_, ts, classes) = &families[&k][i];
            assert_eq!(&overlaps(ts.iter()), classes);
        });
    }
}

/// k types that each reach one ring of k types with a name each cost order k log k, though each
/// reaches all k: the ring placed for a type is read only where another type reaches it (the
/// second tradeoff at `overlaps`). The first three families of [`rings`]. Small instances:
/// `the_rings_of_names_have_the_classes_their_shapes_give`.
#[test]
fn types_that_each_reach_a_ring_of_names_scale() {
    rings_scale(0..3);
}

/// k types that each reach one ring of k names whose members hold types of lower groups cost
/// order k log k: the lower types of a node of the ring are placed only when the node is read
/// (the second tradeoff at `overlaps`). The last three families of [`rings`]. Small instances:
/// `the_rings_of_names_have_the_classes_their_shapes_give`.
#[test]
fn types_that_each_reach_a_ring_holding_lower_types_scale() {
    rings_scale(3..6);
}

/// The atom of a union of n tuple differences, `#a(∪ i<n: (i, int | bool) \ (i, bool))`, and the
/// atom of the union of the n tuples taken away, `#a(∪ i<n: (i, bool))`. They are disjoint, and
/// the first is not a subtype of the second. FAIL-kernel-empty-tuple-diff-union.
pub(super) fn tuple_diff_union_pair(n: usize) -> (Type, Type) {
    let a = |p: Type| Type::atom_with("a", &p);
    let lit = |i: usize| Type::lit(&Value::Int(i as i64)).expect("an integer literal");
    let ib = &Type::int() | &Type::bool();
    let part = a(Type::union_all((0..n).map(|i| {
        &Type::tuple(vec![lit(i), ib.clone()]) - &Type::tuple(vec![lit(i), Type::bool()])
    })));
    let paid = a(Type::union_all(
        (0..n).map(|i| Type::tuple(vec![lit(i), Type::bool()])),
    ));
    (part, paid)
}

/// Whether the meet of the two atoms of [`tuple_diff_union_pair`] is empty, and whether the
/// first is a subtype of the second, cost order n log n in the n tuples
/// (FAIL-kernel-empty-tuple-diff-union). Small instance:
/// `a_union_of_tuple_differences_is_disjoint_from_the_tuples_taken_away`.
#[test]
fn the_emptiness_of_a_meet_of_tuple_differences_scales() {
    let inputs = crate::scaling::inputs(256, tuple_diff_union_pair);
    crate::scaling::check(
        "whether #a(∪ (i, int | bool) \\ (i, bool)) & #a(∪ (i, bool)) is empty, and the subtype test",
        256,
        |n| {
            let (part, paid) = &inputs[&n];
            assert!((part & paid).is_empty());
            assert!(!part.subtype(paid));
        },
    );
}

/// [`tuple_diff_union_pair`] with the second component an atom with a payload, which is not a
/// plain value: `#a(∪ i<n: (i, #b((int | bool))) \ (i, #b((bool))))` and
/// `#a(∪ i<n: (i, #b((bool))))`. Disjoint, and the first not a subtype of the second.
pub(super) fn tuple_diff_union_payload_pair(n: usize) -> (Type, Type) {
    let a = |p: Type| Type::atom_with("a", &p);
    let b = |p: Type| Type::atom_with("b", &Type::tuple(vec![p]));
    let lit = |i: usize| Type::lit(&Value::Int(i as i64)).expect("an integer literal");
    let ib = &Type::int() | &Type::bool();
    let part = a(Type::union_all((0..n).map(|i| {
        &Type::tuple(vec![lit(i), b(ib.clone())]) - &Type::tuple(vec![lit(i), b(Type::bool())])
    })));
    let paid = a(Type::union_all(
        (0..n).map(|i| Type::tuple(vec![lit(i), b(Type::bool())])),
    ));
    (part, paid)
}

/// As [`the_emptiness_of_a_meet_of_tuple_differences_scales`], on
/// [`tuple_diff_union_payload_pair`]: a witness tuple with a scalar component and a component
/// that is not plain, cost order n log n. Small instance:
/// `a_union_of_tuple_differences_with_payloads_is_disjoint_from_the_tuples_taken_away`.
#[test]
fn the_emptiness_of_a_meet_of_tuple_differences_with_payloads_scales() {
    let inputs = crate::scaling::inputs(256, tuple_diff_union_payload_pair);
    crate::scaling::check(
        "whether #a(∪ (i, #b((int | bool))) \\ (i, #b((bool)))) & #a(∪ (i, #b((bool)))) is empty, and the subtype test",
        256,
        |n| {
            let (part, paid) = &inputs[&n];
            assert!((part & paid).is_empty());
            assert!(!part.subtype(paid));
        },
    );
}

/// [`tuple_diff_union_pair`] with the first component an atom with a payload, `#k((i))`, so no
/// component of a witness tuple is a scalar: `#a(∪ i<n: (#k((i)), int | bool) \ (#k((i)),
/// bool))` and `#a(∪ i<n: (#k((i)), bool))`. Disjoint, and the first not a subtype of the second.
/// FAIL-kernel-empty-payload-key-tuple.
pub(super) fn tuple_diff_union_payload_key_pair(n: usize) -> (Type, Type) {
    let a = |p: Type| Type::atom_with("a", &p);
    let k = |i: usize| {
        let lit = Type::lit(&Value::Int(i as i64)).expect("an integer literal");
        Type::atom_with("k", &Type::tuple(vec![lit]))
    };
    let ib = &Type::int() | &Type::bool();
    let part = a(Type::union_all((0..n).map(|i| {
        &Type::tuple(vec![k(i), ib.clone()]) - &Type::tuple(vec![k(i), Type::bool()])
    })));
    let paid = a(Type::union_all(
        (0..n).map(|i| Type::tuple(vec![k(i), Type::bool()])),
    ));
    (part, paid)
}

/// As [`the_emptiness_of_a_meet_of_tuple_differences_scales`], on
/// [`tuple_diff_union_payload_key_pair`]: a witness tuple with no scalar component and a
/// component that is an atom with a payload, cost order n log n. Small instance:
/// `a_union_of_tuple_differences_with_payload_keys_is_disjoint_from_the_tuples_taken_away`.
#[test]
fn the_emptiness_of_a_meet_of_tuple_differences_with_payload_keys_scales() {
    let inputs = crate::scaling::inputs(256, tuple_diff_union_payload_key_pair);
    crate::scaling::check(
        "whether #a(∪ (#k((i)), int | bool) \\ (#k((i)), bool)) & #a(∪ (#k((i)), bool)) is empty, and the subtype test",
        256,
        |n| {
            let (part, paid) = &inputs[&n];
            assert!((part & paid).is_empty());
            assert!(!part.subtype(paid));
        },
    );
}
