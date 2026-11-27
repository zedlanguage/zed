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

/// Holds the work of `RUNS` tests `a.is_subset(b)`, each `true`, per unit of `units`, at the
/// sizes `small` and `large` of `make`, to the limit of power 0: the work at `large` at most
/// `limit(0)` times the work at `small` times `units(large) / units(small)`, which is the work
/// per unit at most `limit(0)` times, the limit itself. The units are counted here, on the
/// sets `make` builds, which are the same in every process of one `ZED_TREAP_SEED`.
///
/// Each size is measured as [`crate::scaling::check_order_fresh`] measures it: on a count of
/// instructions, in a process of its own where the test binary runs other tests; on processor
/// time, the fastest of several runs, each on sets built for it, under the allowance `scaling`
/// gives a count that changes with load. FAIL-treap-subset-bench-spread (2026-11-23, Colab std2,
/// 2 cores, no hardware counter): each bench run alone under DynamoRIO's count gave one ratio per
/// seed on every run (seed 0: joined cuts 1.25, removals 0.95, middle half 0.91); on processor
/// time, which the whole `--lib` run measures there, seed 0's joined cuts measured 1.38 (1094
/// and 1511 ns per unit) and the middle half moved from 0.50 to 1.10 between runs, with no
/// allowance for load, as `scaling::hold` gives none. The sets are the same in every run, so
/// what moved was the measure, not the work.
fn hold_per_unit(
    what: &str,
    measure: &str,
    (small, large): (i64, i64),
    make: impl Fn(i64) -> (TreapSet<i64>, TreapSet<i64>) + Sync,
    units: impl Fn(i64, &TreapSet<i64>, &TreapSet<i64>) -> u64,
) {
    let [at_small, at_large] = [small, large].map(|k| {
        let (a, b) = make(k);
        units(k, &a, &b).max(1)
    });
    let allowed = crate::scaling::limit(0) * at_large as f64 / at_small as f64;
    let why = format!(
        "{measure}: {at_small} and {at_large} units, so the work per unit within {:.4} times is \
         the work within {allowed:.4} times",
        crate::scaling::limit(0)
    );
    let to_size = |k: i64| usize::try_from(k).expect("a size of the bench");
    crate::scaling::fresh_inputs_by(
        &mut crate::scaling::Meter::new(),
        crate::scaling::Measures::WorkOnly,
        None,
        what,
        crate::scaling::Bound::Given(allowed, &why),
        (to_size(small), to_size(large)),
        &|k, _| make(i64::try_from(k).expect("a size of the bench")),
        // The sets are returned, so that `fresh_inputs_by` holds them and drops them after the
        // measurement: dropped here, the `O(k)` free of each set was measured with the test
        // (b22-kernel6, 2026-11-23, Colab std2 on processor time: the middle half then measured
        // 6.35 times at 2^14 and 2^17, where the sets of 8 times the keys take 8 times as long
        // to free).
        &|_, (a, b): (TreapSet<i64>, TreapSet<i64>)| {
            for _ in 0..RUNS {
                assert!(std::hint::black_box(&a).is_subset(&b));
            }
            (a, b)
        },
    );
}

#[test]
fn is_subset_scales_with_the_edits_not_the_size() {
    // `d` and `8d` keys removed from 2^16 keys: `O(d log k)`, linear in `d`.
    // Instructions only: since faa55acd0 the walk keeps its stack inline and allocates nothing,
    // so `check_order` refused the run (0 bytes at both sizes; VM l43, 2026-11-26).
    let by_edits: HashMap<usize, _> = crate::scaling::inputs(64, |d| edited(1 << 16, d as i64));
    crate::scaling::check_instructions_only(
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
    hold_per_unit(
        "is_subset of k keys with 64 removed against the k keys, sizes 2^14 and 2^17",
        "the work per node of U",
        (1 << 14, 1 << 17),
        |k| edited(k, 64),
        |_, less, all| not_shared(less, all),
    );
    // A cut to the middle half of `k` and `8k` keys against the keys: the proof's cut case. The
    // work per unit of what the proof charges, held to the limit of power 0: `U`, the depths in
    // `all` of the cut's least and greatest keys (`D_out` is at most their ancestors, step 11)
    // and the two spines of the cut that `first` and `last` walk. Not per unit of the heights,
    // which bound these but do not follow them: the depth of `k / 4` went from 12 to 26 from
    // 2^14 to 2^17 while the height of `all` went from 34 to 43, and the instructions grew 1.71
    // times, 1.30 per unit of `U + h + h'` (2026-11-21).
    hold_per_unit(
        "is_subset of the middle half of k keys against the k keys, sizes 2^14 and 2^17",
        "the work per node of U, the two depths and the two spines",
        (1 << 14, 1 << 17),
        middle_half,
        |k, cut, all| {
            not_shared(cut, all)
                + depth(&all.root, k / 4)
                + depth(&all.root, 3 * k / 4)
                + spine(&cut.root, true)
                + spine(&cut.root, false)
        },
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
    //
    // FAIL-treap-joined-cuts-ratio: per unit of the terms above the ratio was fixed for a seed
    // and ranged 1.19 to 1.38 over `ZED_TREAP_SEED` 0 to 15, past the limit 1.3125 at seeds 3, 7
    // and 9 (b22-kernel6, 2026-11-23; b22-free2, 2026-11-25). Those terms are an estimate of the
    // work, not the work: the depths of the gap ends in `all` (about `2 ln (129 l)`, 1.27 times
    // from 16 to 128) are charged at every gap, where the proof charges what lies above a gap's
    // ends only through `U`, `D` and the `3h` moves (steps 9 and 14), and the terms move with the
    // seed apart from the walk. So the two claims are held apart here. (a) The proof's bound:
    // the walk's own count (`IS_SUBSET_WORK`, a unit per pair taken and per move of `p`) is at
    // most `2U + 2D + 3gh + 1` (steps 9 and 14) on these sets at both sizes, `D` at most the
    // keys of `all` not in `joined` and `h` the height of `joined`, as in
    // `is_subset_work_within_its_bound`. (b) Each unit of that count costs `O(1)` instructions
    // (step 9): instructions per counted unit, with the two spines of `first` and `last`, held to
    // the limit of power 0.
    let g = 64;
    hold_per_unit(
        "is_subset of 65 cuts of the keys joined, gaps of l keys, against the keys, l = 16 and 128",
        "the work per unit the walk counts (pairs and moves) and per node of the two spines",
        (16, 128),
        |l| joined_cuts(g, l),
        |l, joined, all| {
            let u = not_shared(joined, all);
            let d = (all.len() - joined.len()) as u64;
            let h = depths_of(&joined.root).0;
            let bound = 2 * u + 2 * d + 3 * (g as u64) * h + 1;
            IS_SUBSET_WORK.with(|c| c.set(0));
            assert!(joined.is_subset(all));
            let work = IS_SUBSET_WORK.with(|c| c.get());
            let spines = spine(&joined.root, true) + spine(&joined.root, false);
            let ends: u64 = (0..g)
                .map(|i| (2 * i * l + l - 1, 2 * i * l + 2 * l))
                .map(|(s1, s2)| {
                    inside_on_path(&all.root, s1, s1, s2) + inside_on_path(&all.root, s2, s1, s2)
                })
                .sum();
            eprintln!(
                "joined cuts, l = {l}: work {work}, bound {bound} (U = {u}, D <= {d}, g = {g}, \
                 h = {h}), keys of the gaps on their ends' paths {ends}, spines {spines}"
            );
            assert!(
                work <= bound,
                "is_subset did {work} units of work at l = {l}, over the bound 2U + 2D + 3gh + 1 \
                 = {bound}"
            );
            work + spines
        },
    );
}

/// The sets `{i, -i}` for `i` in `1..=n`, each built twice, its keys put in in both orders:
/// `2n` sets in `n` classes of equal sets, every set of one sum of weights, as the weight of an
/// `i64` is linear in it ([`Elem::weight`]): any two keys of one sum weigh alike.
fn opposite_pairs(n: usize) -> Vec<TreapSet<i64>> {
    (1..=n as i64)
        .flat_map(|i| [[i, -i], [-i, i]])
        .map(|keys| keys.into_iter().collect())
        .collect()
}

/// FREE2-tables-hashcons-bench: [`HashConsTable::share`] of `2n` two-key sets of one sum, `n`
/// distinct, each met twice. A table keyed by the sum alone keeps them in one bucket and scans
/// it on each set put in, `O(n^2)`; keyed by a seeded sum, `O(n)` expected. The second set of
/// each class is given the first's tree, which is checked after the run.
#[test]
fn sharing_sets_of_one_sum_scales() {
    crate::scaling::check_order_fresh(
        "HashConsTable::share of 2n sets {i, -i}, all of one sum",
        20_000,
        1,
        |n, _| opposite_pairs(n),
        |_, mut sets| {
            let mut table = HashConsTable::default();
            for s in &mut sets {
                table.share(s);
            }
            for pair in sets.chunks(2) {
                assert!(pair[0].ptr_eq(&pair[1]));
            }
            (table, sets)
        },
    );
}

/// A key whose weight is 0 whatever it is, so every set of such keys has one seeded sum: the
/// keys of [`sharing_tied_sets_scales`] and of `tests::comparing_tied_sets_allocates_nothing`,
/// ordered and prioritized as `i64`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) struct Tied(pub(super) i64);

impl Elem for Tied {
    fn priority(&self) -> u64 {
        self.0.priority()
    }
    fn weight(&self) -> u64 {
        0
    }
    fn class(&self) -> u32 {
        1
    }
}

/// PERF-set-tied-digest-depth, the table's half: [`HashConsTable::share`] of `2n` sets
/// `{Tied(i), Tied(i + 1)}`, `n` distinct, each met twice, all of one seeded sum, so all in one
/// bucket. A bucket that is a list (as before, of weak handles) is scanned on each set put in,
/// `O(n^2)`; the ordered bucket finds a set in `O(log n)` comparisons of two keys each,
/// `O(n log n)`, whose ratio at `n` and `8n` meets 10.5 from `n = 777` (COMPLEXITY.md), so the
/// sizes are 20,000 and 160,000 (`8 ln 160000 / ln 20000 = 9.68`). The second set of each
/// class is given the first's tree, which is checked after the run.
///
/// Cost model. Instructions: each of the `2n` sets costs one hash lookup and at most two
/// searches of a bucket of at most `n` sets (`get`, then `insert` for a new set), each
/// `O(log n)` comparisons of two sets of two keys, `O(1)` each: `O(n log n)`, ratio 9.68.
/// Bytes: the sets are built before the run and do not grow; a new set adds one handle to the
/// bucket's B-tree, `O(1)` amortized, and a comparison allocates nothing while the walks' stacks
/// stay inline (`Iter`, two nodes deep here): `O(n)`, ratio 8. Measured (b22-free2, Colab v5e
/// VM, 2026-11-25): inline stacks 6,152,276 and 49,218,676 bytes, ratio 8.0, and 499,821,628
/// and 4,978,509,145 instructions, ratio 9.96; the same run with `Iter`'s stack a `Vec` (the
/// negative control) 137,048,020 and 1,363,687,412 bytes, ratio 9.95, and 1,574,220,095 and
/// 15,758,428,484 instructions, ratio 10.01: each comparison allocated two stacks.
#[test]
fn sharing_tied_sets_scales() {
    crate::scaling::check_order_fresh(
        "HashConsTable::share of 2n distinct sets {Tied(i), Tied(i + 1)}, all of one seeded sum",
        20_000,
        1,
        |n, _| {
            (0..n as i64)
                .flat_map(|i| [[i, i + 1], [i + 1, i]])
                .map(|keys| keys.into_iter().map(Tied).collect::<TreapSet<Tied>>())
                .collect::<Vec<_>>()
        },
        |_, mut sets| {
            let mut table = HashConsTable::default();
            for s in &mut sets {
                table.share(s);
            }
            assert_eq!(table.table.len(), 1, "one seeded sum");
            for pair in sets.chunks(2) {
                assert!(pair[0].ptr_eq(&pair[1]));
            }
            (table, sets)
        },
    );
}

/// `n` sets of two integer literals `{a, b}`, `a` in `1..=n`, all of one sum of weights: the
/// weight of `Int(a)` is a public bijection of `a` (`types::scalar`, `mix(1, a)`), so `b` is
/// the integer whose weight is the sum less `a`'s, found by [`zed_hash::unstep`]. Each `b` is
/// checked against its weight, and the sets are checked distinct.
fn literal_pairs_of_one_sum(n: usize) -> Vec<TreapSet<crate::value::Value>> {
    use crate::value::Value;
    const SUM: u64 = 0x5eed_f00d_cafe_0001;
    let sets: Vec<TreapSet<Value>> = (1..=n as i64)
        .map(|a| {
            let want = SUM.wrapping_sub(Value::Int(a).weight());
            let b = zed_hash::unstep(1, want) as i64;
            assert_eq!(Value::Int(b).weight(), want, "the weight of {b} inverted");
            [Value::Int(a), Value::Int(b)].into_iter().collect()
        })
        .collect();
    let distinct: std::collections::BTreeSet<Vec<Value>> =
        sets.iter().map(|s| s.iter().cloned().collect()).collect();
    assert_eq!(distinct.len(), n);
    sets
}

/// FREE2-tables-hashcons-bench at the types: `n` types of two integer literals each, distinct
/// and all of one sum of weights, made by [`crate::types::Type::ints_of`], whose `Type::new`
/// puts each literal set in the thread's [`HashConsTable`] (TYPE-hashcons). With the table keyed
/// by the sum alone, each type scans the types before it, `O(n^2)`.
#[test]
fn literal_types_of_one_sum_scale() {
    crate::scaling::check_order_fresh(
        "Type::ints_of of n distinct two-literal sets, all of one sum",
        5_000,
        1,
        |n, _| literal_pairs_of_one_sum(n),
        |_, sets| {
            sets.into_iter()
                .map(crate::types::Type::ints_of)
                .collect::<Vec<_>>()
        },
    );
}

/// The big integers `2^64 + k (2^61 - 1)` for `k` in `1..=n`: one residue modulo `2^61 - 1`, so
/// one digest, which the priorities of big integers read before PERF-fingerprint-montgomery.
fn tied_bigs(n: usize) -> Vec<crate::value::Value> {
    use num_bigint::BigInt;
    let base = BigInt::from(1u8) << 64u32;
    let step = (BigInt::from(1u8) << 61u32) - 1u8;
    (1..=n as u64)
        .map(|k| crate::value::Value::int(&base + &step * k))
        .collect()
}

/// The nodes of a tree, each with its depth counted in nodes (the root's is 1), by a stack of
/// its own: the longest depth and the sum of the depths.
fn depths_of<T>(t: &Tree<T>) -> (u64, u64) {
    let (mut most, mut sum, mut stack) = (0, 0, vec![(t.as_ref(), 0u64)]);
    while let Some((n, d)) = stack.pop() {
        if let Some(n) = n {
            most = most.max(d + 1);
            sum += d + 1;
            stack.push((n.left.as_ref(), d + 1));
            stack.push((n.right.as_ref(), d + 1));
        }
    }
    (most, sum)
}

/// PERF-fingerprint-montgomery, red then green: in a set of `n` big integers of one residue
/// modulo `2^61 - 1` ([`tied_bigs`]), `n` in 1024, 4096 and 16384, the mean depth of a key is
/// at most `1.5 (1 + 2 ln n)`. The expected depth of each key of a treap of distinct,
/// independent priorities is below `1 + 2 ln n`: Seidel and Aragon, "Randomized search trees",
/// Algorithmica 16(4/5), 464-497, 1996, doi:10.1007/BF01940876, Theorem 4.7 (i):
/// "Ex[D(x_l)] = H_l + H_{n+1-l} - 1 < 1 + 2 ln n" (checked 2026-11-25 in the authors' copy),
/// so the mean's expectation is below it too, and the factor 1.5 leaves room for the spread of
/// one draw. Red: when the priorities read the residue modulo `2^61 - 1`
/// (`ZED_FINGERPRINT_FORM=m61`, the form before), every key ties, the ties are broken by the
/// order of the keys, and the set is a path of mean depth `(n + 1) / 2`; green: their
/// fingerprints, residues modulo two drawn primes, differ. Prints the mean and largest depths.
#[test]
fn tied_big_integers_keep_a_logarithmic_depth() {
    for n in [1024usize, 4096, 16384] {
        let set: TreapSet<crate::value::Value> = tied_bigs(n).into_iter().collect();
        assert_eq!(set.len(), n);
        let (most, sum) = depths_of(&set.root);
        let mean = sum as f64 / n as f64;
        let bound = 1.5 * (1.0 + 2.0 * (n as f64).ln());
        println!(
            "bench TIED_BIGS n={n} mean_depth={mean:.2} mean_depth_bound={bound:.1} \
             height={most} (printed, not asserted)"
        );
        assert!(
            mean <= bound,
            "n {n}: mean depth {mean:.2}, over 1.5 (1 + 2 ln n) = {bound:.1}"
        );
    }
}

/// PERF-fingerprint-montgomery: putting `n` big integers of one residue modulo `2^61 - 1`
/// ([`tied_bigs`]) into a set, `n` and `8n` at 20,000, made before the count, so each value's
/// fingerprint is computed in the run, once. `O(n log n)` expected, `8 ln 160000 / ln 20000 =
/// 9.68`, under 10.5; with the residue modulo `2^61 - 1` as the priority every key tied and the
/// set was a path, `O(n^2)` ([`tied_big_integers_keep_a_logarithmic_depth`] is the red).
#[test]
fn tied_big_integers_scale() {
    crate::scaling::check_order_fresh(
        "a set of n big integers of one residue modulo 2^61 - 1",
        20_000,
        1,
        |n, _| tied_bigs(n),
        |n, values| {
            let set: TreapSet<crate::value::Value> = values.into_iter().collect();
            assert_eq!(set.len(), n);
            set
        },
    );
}
