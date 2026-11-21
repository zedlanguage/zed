//! The benchmark of [`TreapSet::is_subset`], run by `tools/run_tests.sh --bench` and left out of
//! its default run (PROOF-kernel-treap-is-subset-cost). The walk's work is
//! `O(U + D_out + D_in h + h)` (proof at `is_subset`). For a set of `k` keys with `d` keys removed
//! against the set, `U` is the nodes on the paths the removals made again, `O(d h)`, and
//! `D_in = d`, so `O(d log k)` expected; for a cut of the set to a range, `U <= 2h`, `D_in = 0`
//! and `D_out <= 2h'`, so `O(log k)`. The correctness tests are
//! `every_operation_agrees_with_a_btree_set` and `is_subset_agrees_on_sets_made_from_one_set` in
//! `tests.rs`.

use super::*;
use std::collections::{HashMap, HashSet};

/// The keys `0..k` with `d` keys spread evenly removed, and the keys `0..k`.
fn edited(k: i64, d: i64) -> (TreapSet<i64>, TreapSet<i64>) {
    let all: TreapSet<i64> = (0..k).collect();
    let mut less = all.clone();
    for i in 0..d {
        assert!(less.remove(&(i * (k / d) + k / (2 * d))));
    }
    (less, all)
}

/// The middle half of the keys `0..k`, cut out of them, and the keys `0..k`.
fn middle_half(k: i64) -> (TreapSet<i64>, TreapSet<i64>) {
    let all: TreapSet<i64> = (0..k).collect();
    (all.at_least(&(k / 4)).at_most(&(3 * k / 4)), all)
}

/// `U` of the proof: the nodes of `a` that are not nodes of `b`, as `Arc`s.
fn not_shared(a: &TreapSet<i64>, b: &TreapSet<i64>) -> u64 {
    fn nodes(t: &Tree<i64>, out: &mut Vec<*const Node<i64>>) {
        if let Some(n) = t {
            out.push(Arc::as_ptr(n));
            nodes(&n.left, out);
            nodes(&n.right, out);
        }
    }
    let (mut xs, mut ys) = (Vec::new(), Vec::new());
    nodes(&a.root, &mut xs);
    nodes(&b.root, &mut ys);
    let ys: HashSet<_> = ys.into_iter().collect();
    xs.iter().filter(|x| !ys.contains(*x)).count() as u64
}

/// The depth of `key` in a tree, the root at 0: the nodes above it on its search path.
fn depth(t: &Tree<i64>, key: i64) -> u64 {
    let (mut d, mut n) = (0, t.as_ref());
    while let Some(x) = n {
        if x.key == key {
            return d;
        }
        d += 1;
        n = if key < x.key {
            x.left.as_ref()
        } else {
            x.right.as_ref()
        };
    }
    d
}

/// The nodes on a tree's left spine, or its right one: what `first` or `last` walks.
fn spine(t: &Tree<i64>, left: bool) -> u64 {
    let (mut d, mut n) = (0, t.as_ref());
    while let Some(x) = n {
        d += 1;
        n = if left {
            x.left.as_ref()
        } else {
            x.right.as_ref()
        };
    }
    d
}

/// Tests a run makes, so that the walk and not the meter's fixed cost is measured.
const RUNS: usize = 200;

/// The instructions of `RUNS` tests `a.is_subset(b)`, each `true`, per unit of `bound`.
fn per_unit(
    meter: &mut crate::scaling::Meter,
    a: &TreapSet<i64>,
    b: &TreapSet<i64>,
    bound: u64,
) -> u64 {
    let work = meter.work(|| {
        for _ in 0..RUNS {
            assert!(std::hint::black_box(a).is_subset(b));
        }
    });
    eprintln!(
        "bench is_subset len={} bound={bound} instr={}",
        a.len(),
        work.units
    );
    work.units / bound.max(1)
}

#[test]
fn is_subset_scales_with_the_edits_not_the_size() {
    // `d` and `8d` keys removed from 2^16 keys: `O(d log k)`, linear in `d`.
    let by_edits: HashMap<usize, _> = crate::scaling::inputs(64, |d| edited(1 << 16, d as i64));
    crate::scaling::check_order(
        "is_subset of 2^16 keys with d removed against the 2^16 keys",
        64,
        1,
        |d| {
            let (less, all) = &by_edits[&d];
            for _ in 0..RUNS {
                assert!(std::hint::black_box(less).is_subset(all));
            }
        },
    );
    // `k` and `8k` keys, 64 removed: the work per node of `U`, `O(1)` by the proof, held to the
    // limit of power 0. Not the instructions alone: `U` is the work the 64 removals did, and it
    // depends on the depths of the 64 keys, which grew 1.48 times from 2^14 to 2^17 and 1.38 from
    // 2^17 to 2^20 (617, 916 and 1263 nodes, 2026-11-21), above the 1.31 that an expected depth
    // of `2 ln k` less the 6 levels the 64 paths share gives; the instructions grew 1.44 and 1.37
    // times with them, 135, 131 and 130 per node.
    let mut meter = crate::scaling::Meter::new();
    let [small, large] = [1i64 << 14, 1 << 17].map(|k| {
        let (less, all) = edited(k, 64);
        per_unit(&mut meter, &less, &all, not_shared(&less, &all))
    });
    crate::scaling::hold(
        "is_subset of k keys with 64 removed against the k keys, sizes 2^14 and 2^17",
        "instructions per node of U",
        small,
        large,
        0,
    );
    // A cut to the middle half of `k` and `8k` keys against the keys: the proof's cut case. The
    // work per unit of what the proof charges, held to the limit of power 0: `U`, the depths in
    // `all` of the cut's least and greatest keys (`D_out` is at most their ancestors, step 11)
    // and the two spines of the cut that `first` and `last` walk. Not per unit of the heights,
    // which bound these but do not follow them: the depth of `k / 4` went from 12 to 26 from
    // 2^14 to 2^17 while the height of `all` went from 34 to 43, and the instructions grew 1.71
    // times, 1.30 per unit of `U + h + h'` (2026-11-21).
    let [small, large] = [1i64 << 14, 1 << 17].map(|k| {
        let (cut, all) = middle_half(k);
        let bound = not_shared(&cut, &all)
            + depth(&all.root, k / 4)
            + depth(&all.root, 3 * k / 4)
            + spine(&cut.root, true)
            + spine(&cut.root, false);
        per_unit(&mut meter, &cut, &all, bound)
    });
    crate::scaling::hold(
        "is_subset of the middle half of k keys against the k keys, sizes 2^14 and 2^17",
        "instructions per node of U, the two depths and the two spines",
        small,
        large,
        0,
    );
}

/// `g + 1` cuts of the keys `0..(2g + 1) l`, each of `l` keys with a gap of `l` keys between
/// them, joined in order, and the keys.
fn joined_cuts(g: i64, l: i64) -> (TreapSet<i64>, TreapSet<i64>) {
    let all: TreapSet<i64> = (0..(2 * g + 1) * l).collect();
    let mut joined = TreapSet::new();
    for i in 0..=g {
        joined = joined.concat(&all.at_least(&(2 * i * l)).at_most(&(2 * i * l + l - 1)));
    }
    (joined, all)
}

/// The nodes on the search path of `key` in a tree whose keys lie strictly between `lo` and
/// `hi`: for `key` an end of a gap of `self` and `t` the tree of `other`, the keys of the gap that
/// are ancestors of `key`, which bound the pairs of step 6 at that gap (step 11 at `is_subset`).
fn inside_on_path(t: &Tree<i64>, key: i64, lo: i64, hi: i64) -> u64 {
    let (mut d, mut n) = (0, t.as_ref());
    while let Some(x) = n {
        d += u64::from(lo < x.key && x.key < hi);
        if x.key == key {
            break;
        }
        n = if key < x.key {
            x.left.as_ref()
        } else {
            x.right.as_ref()
        };
    }
    d
}

#[test]
fn is_subset_of_joined_cuts_scales_with_the_gaps() {
    // 64 gaps of `l` and `8l` keys: the proof's case of `g + 1` cuts joined
    // (PROOF-kernel-treap-is-subset-gaps). The work per unit of what the proof charges
    // (`O(U + D + g h + h)`), held to the limit of power 0: `U`; for each gap the keys of the gap
    // on the search paths of its two ends in `other` (they bound `D`, step 11) and the depths of
    // the two ends in both trees (the search path of the gap in `self`, and the ancestors in
    // `other`); and the two spines of `self` that `first` and `last` walk.
    //
    // What this ratio cannot see: the walk without steps 12 to 14 went down the search path of a
    // gap in `self` once for each key of the gap on those paths, about `2 ln l` of them for
    // random priorities, so its work per unit grew only as `log l`, and the work that does not
    // depend on `l` hides most of that: it measured 1.21 times at `l` = 128 and 1024 and 1.38 at
    // 16 and 128 (2026-11-21, units without the term for `D`), close to the limit of 1.31 either
    // way. The test that fails on that walk is `is_subset_work_within_its_bound` in `tests.rs`,
    // which counts the walk's units of work on gaps built with 200 such keys each.
    let g = 64;
    let mut meter = crate::scaling::Meter::new();
    let [small, large] = [16i64, 128].map(|l| {
        let (joined, all) = joined_cuts(g, l);
        let mut bound =
            not_shared(&joined, &all) + spine(&joined.root, true) + spine(&joined.root, false);
        for i in 0..g {
            let (s1, s2) = (2 * i * l + l - 1, 2 * i * l + 2 * l);
            for end in [s1, s2] {
                bound += depth(&joined.root, end)
                    + depth(&all.root, end)
                    + inside_on_path(&all.root, end, s1, s2);
            }
        }
        per_unit(&mut meter, &joined, &all, bound)
    });
    crate::scaling::hold(
        "is_subset of 65 cuts of the keys joined, gaps of l keys, against the keys, l = 16 and 128",
        "instructions per node of U, per key of a gap on its ends' paths, per depth of a gap's \
         ends and per spine",
        small,
        large,
        0,
    );
}
