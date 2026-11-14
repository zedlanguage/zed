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
