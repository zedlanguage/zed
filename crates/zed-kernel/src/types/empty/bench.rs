//! The benchmarks of the emptiness search, run by `tools/run_tests.sh --bench` and left out of
//! its default run (TEST-bench-move-crates). Each check they make besides the ratio has a small
//! instance among the correctness tests in `tests.rs`, named at each benchmark.

use super::tests::{
    rings, tuple_diff_union_pair, tuple_diff_union_payload_key_pair, tuple_diff_union_payload_pair,
};
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
