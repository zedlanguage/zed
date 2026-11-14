//! The benchmarks of `tests`, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates, author P178: many cases). The correctness test that keeps a
//! small instance of each is named in its comment.

use super::*;

/// Every order of the seven equalities of `three_small_classes` with every one of the 128
/// orientations, 645,120 joins (1.1 s on 2026-11-14 at load 30), gives one vector. The
/// correctness test `the_representatives_of_joined_equalities_do_not_depend_on_their_order`
/// takes every order once, each with one orientation.
#[test]
fn the_representatives_of_joined_equalities_do_not_depend_on_their_order_or_orientation() {
    let small = three_small_classes();
    let want = small.expected();
    let mut roots = BTreeSet::new();
    each_order(small.edges.len(), &mut |order| {
        for bits in 0..1u32 << small.edges.len() {
            let flip = flipped(&small, bits);
            let (got, r, _) = small.joined(order, &flip);
            assert_eq!(got, want, "order {order:?}, flipped {flip:?}");
            roots.insert(r);
        }
    });
    assert!(roots.len() > 1, "the roots never differ: {roots:?}");
}
