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
/// and again, are ranked again `O(log n)` times each on average (Bender et al.): from
/// 8,000 to 64,000 components the number ranked again grows under the limit of 13 for
/// order n (9.8 times measured, 1.24 log2 n each; below n = 4,000,
/// while the ranks fill up, the count each grows faster than `log n`); ranking each later
/// component again, the naive version, would grow it 64 times.
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
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || {
            let x = Lin::atom(Atom::Sym("x".into()));
            let mut r = Relation::default();
            for i in 0..k {
                r.defer(Formula::Con(Con::ge(&x, &Lin::constant(i))));
            }
            drop(r);
        })
        .expect("a thread")
        .join()
        .expect("no overflow");
}
