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

/// The 3,000 systems C2-chain compared on (TESTS-C2-chain-old-products, test audit 2026-11-08
/// row 17). Small instance: `difference_ends_are_those_found_by_listing_the_points`, 300.
#[test]
fn difference_ends_of_3000_systems_are_those_found_by_listing_the_points() {
    let start = std::time::Instant::now();
    difference_ends_listed("difference ends of 3000 systems, listed", 3000);
    eprintln!("3000 systems listed in {:.2?}", start.elapsed());
}

/// The merge of two rows, `f·x + g·y` without one variable (`merge`, now
/// `zed_collections::sorted::merge_with`; DRY-sorted-intervals-2026-11-26, group 1), 64 times on
/// two rows of `n` terms, half of their variables shared, the shared terms cancelling: the
/// variables below `3n / 2` whose remainder by 3 is not 0, and not 1, every coefficient 1, with
/// `f = 1` and `g = -1`. Correctness: the tests of `presburger` and of `sorted`.
#[test]
fn a_merge_of_two_rows_scales_with_their_terms() {
    let inputs = crate::scaling::inputs(4096, |n| {
        let row = |skip| -> Vec<Term> {
            (0..3 * n / 2)
                .filter(|i| i % 3 != skip)
                .map(|i| (i, Int::from(1)))
                .collect()
        };
        (row(0), row(1))
    });
    let (one, minus_one) = (Int::from(1), Int::from(-1));
    crate::scaling::check_order("a merge of two rows of n terms, 64 times", 4096, 1, |n| {
        let (x, y) = &inputs[&n];
        for _ in 0..64 {
            let m = merge(
                std::hint::black_box(x),
                &one,
                std::hint::black_box(y),
                &minus_one,
                1,
            );
            assert_eq!(m.len(), n - 1);
        }
    });
}
