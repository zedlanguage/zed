//! The benchmarks of `product::tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness tests that keep a small instance of
//! what `ranks_given_in_one_place_scale` checks besides the ratio are
//! `ranks_given_in_one_place_keep_their_order`, `ranks_keep_the_order_they_are_given_in`,
//! `ranks_given_one_after_another_at_an_end_rank_no_other_again` and
//! `ranks_given_at_either_end_rank_a_full_range_again`. Its sizes stay at 8,000 and 64,000: the
//! ratio is of a count, the components ranked again, not of time, and the piece takes about
//! 1 s. `a_long_pending_list_is_dropped_without_overflow` (TEST-bench-move-l0139) is a deep
//! list, an unusual size (author P178).

use super::*;

/// Components ranked each right after the first, so that the ranks between run out again
/// and again, are ranked again `O(log n)` times each on average (Bender et al., ESA 2002,
/// doi:10.1007/3-540-45749-6_17, cited in the crate's `lib.rs`, References, and sketched in
/// `product.rs`, impl `Potential`): from 8,000 to 64,000 components the number ranked again
/// grows under the limit of 13 of 2026-11-13 for order n (9.8 times measured, 1.24 log2 n each;
/// below n = 4,000, while the ranks fill up, the count each grows faster than `log n`); ranking
/// each later component again, the naive version, would grow it 64 times.
#[test]
fn ranks_given_in_one_place_scale() {
    let moved = |n: usize, front: bool| -> usize {
        let mut pot = Potential::default();
        let mut list = Vec::new();
        rank_at(&mut pot, &mut list, 0);
        let total = (0..n)
            .map(|_| rank_at(&mut pot, &mut list, usize::from(!front)))
            .sum();
        check_ranks(&pot, &list);
        total
    };
    for front in [false, true] {
        crate::scaling::hold(
            &format!("ranks given in one place, front {front}: n = 8,000 and 64,000"),
            "components ranked again",
            moved(8000, front) as u64,
            moved(64_000, front) as u64,
            1,
        );
    }
}

/// A relation with a long list of pending conjuncts is dropped with no overflow, on a
/// thread with the default stack of a test thread, 2 MiB. Each `Arc<Pending>` dropped the
/// next in turn, one frame each, before `Drop for Pending` (TEST-bench-move-l0139, found
/// by `chain_put_against_order` at 8192 in l01_39 `linked`); the depth is about a fifth
/// above the smallest list that overflowed that stack, 65,312 (65,194 passed), measured
/// 2026-11-14.
#[test]
fn a_long_pending_list_is_dropped_without_overflow() {
    let k: i64 = 78_000;
    crate::scaling::on_a_stack(2 << 20, || {
        let x = Lin::atom(Atom::Sym("x".into()));
        let mut r = Relation::default();
        for i in 0..k {
            r.defer(Formula::Con(Con::ge(&x, &Lin::constant(i))));
        }
        drop(r);
    });
}

/// Removing one entry from a [`Pst`] costs O(log k) (PROOF-pst-remove-cost). The trees are
/// Fibonacci trees, the AVL trees of least size for their height, with every slot full:
/// removing the greatest key shortens the right spine, which is the shorter side at every
/// level, so an AVL rebalancing rotates at every second level of the path, each rotation
/// pushing slots down a whole subtree, O(log^2 k) in all; the rank-balanced rebalancing
/// rotates twice at most. Heights 23 and 28 hold 46,368 and 514,229 leaves, 11.1 times as
/// many, more than 8. Order 1 in `log k`, so power 0: the limit is 1.3125 times.
#[test]
fn removing_from_a_priority_search_tree_takes_log_time() {
    let at: PartAt = (
        false,
        Arc::new(Formula::Con(Con::ge(
            &Lin::atom(Atom::Sym("x".into())),
            &Lin::constant(0),
        ))),
    );
    // The Fibonacci tree of height `h`, its leaves numbered from `next` up, each entry
    // `(k, -k)` so that the least key has the greatest priority. Its rank is `h - 1`: each
    // branch is 1 above its left child and 2 above its right one, (R1) of [`Pst`].
    fn fib(h: usize, next: &mut i64, at: &PartAt) -> Pst<i64> {
        if h == 1 {
            let e = (*next, -*next, at.clone());
            *next += 1;
            return Pst::leaf(e.clone(), Some(e));
        }
        let left = fib(h - 1, next, at);
        let right = fib((h - 2).max(1), next, at);
        Pst::pulled_branch(left, right, h - 1)
    }
    let tree = |h: usize| {
        let mut next = 0;
        let t = fib(h, &mut next, &at);
        let last = (next - 1, 1 - next, at.clone());
        (t, last)
    };
    let (small, small_last) = tree(23);
    let (large, large_last) = tree(28);
    let removes = |t: &Pst<i64>, last: &PstEntry<i64>| {
        for _ in 0..2000 {
            std::hint::black_box(t.remove(last));
        }
    };
    crate::scaling::compare(
        "removing the greatest key of a Fibonacci priority search tree of heights 23 and 28",
        0,
        || removes(&small, &small_last),
        || removes(&large, &large_last),
    );
}

/// The second case of the held-back parts of a chain key (row PROOF-chain-left-held-back-bench,
/// [`Block::certifies_held`]), measured on the held set alone: building a [`HeldBack`] and
/// asking it, the branch of `certifies_held` for an entry `Some`, not `None` and not the rest
/// of `Scope::project_block`. c parts with ends (c + j, c + j), j < c, held back in two
/// batches (two wakes), then c idle parts with ends (i, 2c - i), i < c, asked in turn, none
/// below every held part. The scan of before kept, at call i, the c - i held parts with
/// j < c - i, scanned again by each later call: Θ(c^2) over the run. Now each call reads the
/// least ends in O(e) and leaves the entry as it was: holding the c parts costs O(c log c),
/// the calls O(c). Sizes c = 2,000 and 16,000; order n log n in the set's comparisons, under
/// the limit for power 1, 10.5.
#[test]
fn held_back_parts_are_certified_in_constant_time_a_call() {
    let run = |c: i64| {
        let parts: Vec<(Vec<Int>, PartAt)> = (0..c)
            .map(|j| {
                (
                    vec![Int::from(c + j), Int::from(c + j)],
                    super::held_part(j),
                )
            })
            .collect();
        let mut held = HeldBack::default();
        let mut parts = parts.into_iter();
        held.hold(parts.by_ref().take(c as usize / 2));
        held.hold(parts);
        let certified = (0..c)
            .filter(|&i| held.certified_by(&[Int::from(i), Int::from(2 * c - i)]))
            .count();
        assert_eq!(certified, 0);
        std::hint::black_box(&held);
    };
    crate::scaling::compare(
        "c idle parts against c parts held back, none below them all, c = 2,000 and 16,000",
        1,
        || run(2000),
        || run(16_000),
    );
}
