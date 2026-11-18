//! The benchmarks of the emptiness search, run by `tools/run_tests.sh --bench` and left out of
//! its default run (TEST-bench-move-crates). Each check they make besides the ratio has a small
//! instance among the correctness tests in `tests.rs`, named at each benchmark.

use std::sync::atomic::{AtomicUsize, Ordering};

use super::tests::{
    RINGS, Ring, ring_family, tuple_diff_union_pair, tuple_diff_union_payload_key_pair,
    tuple_diff_union_payload_pair,
};
use super::*;

/// `runs` copies of the family `i` of [`super::tests::rings`] at `k` types, each built on a
/// thread of its own, so no run of a benchmark reads what another run left in its input.
///
/// One input shared by every run of a size let the first run do work that the later runs found
/// done: on the second family at 2048 and 16384 types, the warm-up took 321.0M instructions and
/// 69.1 MB and the measured run at 2048 247.4M and 54.4 MB, while the one run at 16384 was a first
/// run, 2618.2M and 552.8 MB. The meter compares the second run at n with the first at 8n, so the
/// ratio came out 10.58, over the limit of 10.5, and only the second run at 8n that the meter takes
/// when the first is over (`Meter::again_when_over`) brought it to 8.20. At 4f94e70b9 the same
/// comparison came to 10.497 or 10.498 from one run to the next, so the check passed at 10.50 in
/// some runs and in others went over and was measured again at 8.2: the 3.21G and 2.51G
/// instructions of FAIL-ratio-ring-shared-node. Copies built on the main thread one after another
/// do not help: a group's instance at equal arguments is one per thread
/// (`rec::group::INSTANCES`), so they share their types, and the runs measured the same 321M
/// against 247M.
///
/// A thread's instances end with it: when the building thread ends, its unit ends (`Unit`'s
/// `Drop` in `rec::unfold`), and every run unfolds the types it reads again, in its own unit. So
/// every run of a size does the same work: measured, the warm-up and the run at 2048 took 361.2M
/// instructions within 0.01% and the same 75,014,764 bytes, and the run at 16384 2940.0M and
/// 600,121,900 bytes, ratio 8.14, with no second run at 16384. The one difference left is in
/// what the process keeps: equal definitions are one group (`rec::group::GROUPS`), so the copies
/// of a size share their ring's group, and the first run of the last family allocates 4,992 bytes
/// more than the later ones, the same at 64 types and at 2048, so it does not grow with k
/// (`each_run_of_a_ring_benchmark_does_the_same_work`).
// Complexity tradeoff: the runs that the meter takes (2 at each size on a count of instructions)
// cost one build each, Θ(runs · k) time and memory where one shared input cost Θ(k), all of it
// before any run is timed; a shared input measures a memo in place of the pass.
fn rings_each(k: usize, i: usize, runs: usize) -> Vec<Ring> {
    (0..runs)
        .map(|_| {
            std::thread::spawn(move || ring_family(k, i))
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
        })
        .collect()
}

/// Checks the families `range` of [`super::tests::rings`] at 2048 and 16384 types, each run on an
/// input of its own ([`rings_each`]).
fn rings_scale(range: std::ops::Range<usize>) {
    let n = 2048;
    let (small, large) = crate::scaling::Meter::new().runs();
    for i in range {
        let (what, _, _) = ring_family(1, i);
        let inputs: HashMap<usize, (Vec<Ring>, AtomicUsize)> =
            [(n, small), (crate::scaling::FACTOR * n, large)]
                .into_iter()
                .map(|(k, runs)| (k, (rings_each(k, i, runs), AtomicUsize::new(0))))
                .collect();
        crate::scaling::check(what, n, |k| {
            let (each, next) = &inputs[&k];
            let (_, ts, classes) = &each[next.fetch_add(1, Ordering::Relaxed)];
            assert_eq!(&overlaps(ts.iter()), classes);
        });
    }
}

/// Each run of a ring benchmark allocates the same bytes as every other run of its size, so the
/// meter compares the pass at both sizes and not a memo the first run fills
/// (FAIL-ratio-ring-shared-node, at [`rings_each`]). A run on a copy built apart comes first, as
/// the meter's warm-up does: equal definitions are one group for the process
/// (`rec::group::GROUPS`), so the copies of a family share its ring's group, and the first run of
/// the last family that reads that group allocates 4,992 bytes more than the later ones, at 64
/// types and at 2048. The copy is built on a thread of its own, not by [`rings_each`], so that
/// copies of [`rings_each`] that shared their types would still differ from one run to the next.
#[test]
fn each_run_of_a_ring_benchmark_does_the_same_work() {
    for i in 0..RINGS {
        let (_, ts, classes) = std::thread::spawn(move || ring_family(64, i))
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
        let each = rings_each(64, i, 3);
        crate::scaling::alone(&|| assert_eq!(&overlaps(ts.iter()), &classes));
        let bytes: Vec<u64> = each
            .iter()
            .map(|(_, ts, classes)| {
                crate::scaling::alone(&|| assert_eq!(&overlaps(ts.iter()), classes)).0
            })
            .collect();
        assert!(
            bytes.iter().all(|&b| b == bytes[0]),
            "{}: the runs allocated {bytes:?} bytes",
            each[0].0
        );
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

/// Plan row PERF-value-key-sites-bench: n families of one size and the same end entries given
/// classes by [`ValueKey`] as `stored_class` gives them (`entry`, `or_insert` of the next
/// number), then each found again by a copy built apart: one digest and O(1) expected compares a
/// key, O(n) in all; with the hash that read the size alone, O(n^2). The keys are built before
/// timing; the run is the map's inserts and lookups alone. The classes are checked at small
/// sizes by `equal_families_get_one_class_by_value_key` in `tests.rs`.
#[test]
fn classes_of_families_by_value_key_scale() {
    use crate::value::key_forms::families_of_one_size;
    let inputs = crate::scaling::inputs(20_000, |n| {
        let key = |v: Value| ValueKey::Value(v);
        let keys: Vec<ValueKey> = families_of_one_size(n).into_iter().map(key).collect();
        let probes: Vec<ValueKey> = families_of_one_size(n).into_iter().map(key).collect();
        (keys, probes)
    });
    crate::scaling::check_order(
        "classes of n families of one size by ValueKey, and n lookups",
        20_000,
        1,
        |n| {
            let (keys, probes) = &inputs[&n];
            let mut classes: HashMap<ValueKey, usize> = HashMap::new();
            for k in keys {
                let next = classes.len();
                classes.entry(k.clone()).or_insert(next);
            }
            assert_eq!(classes.len(), n);
            let found = probes.iter().filter(|p| classes.contains_key(p)).count();
            assert_eq!(found, n);
        },
    );
}
