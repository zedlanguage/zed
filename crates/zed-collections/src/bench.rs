//! The scaling benchmarks of the routines whose cost this crate states (TEST-dry-shared-units),
//! run by `tools/run_tests.sh --bench` and left out of its default run. Each runs at n and 8n
//! and holds the ratio of the work to 10.5 (`scaling::LIMIT`); n log n at n = 100,000 is
//! 8 · log(800,000) / log(100,000) = 9.44. The inputs are built before any run is measured.
//! A routine that allocates nothing is held by `check_instructions_only`, which skips the
//! check that a run allocates. The small instances of each are the correctness tests in the
//! routine's own module.

use std::collections::BTreeMap;

use crate::fenwick::Fenwick;
use crate::held::Held;
use crate::intern::Interner;
use crate::scaling;
use crate::search::{first_true, gallop};
use crate::{cartesian, intervals, sorted, spelling};

/// The size of every benchmark here, run again at `8 * N`.
const N: usize = 100_000;

/// The `i`th of a sequence of numbers spread over `u64` (Fibonacci hashing: multiplication by
/// 2^64 / φ), so the inputs are the same on each run and in no order a sort can exploit.
fn spread(i: usize) -> u64 {
    (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

/// The inputs `make` gives at `N` and `8 * N`.
fn built<T>(make: impl Fn(usize) -> T) -> BTreeMap<usize, T> {
    [N, scaling::FACTOR * N]
        .into_iter()
        .map(|m| (m, make(m)))
        .collect()
}

/// `m` numbers in 0..m/2, so about half repeat.
fn with_repeats(m: usize) -> Vec<u64> {
    (0..m).map(|i| spread(i) % (m as u64 / 2)).collect()
}

/// Small instances: `sorted::tests::sorts_with_duplicates_removed_match_a_scan`.
#[test]
fn sort_dedup_takes_n_log_n() {
    let inputs = built(with_repeats);
    scaling::check("sort_dedup of n numbers", N, |m| {
        let mut v = inputs[&m].clone();
        sorted::sort_dedup(&mut v);
        assert!(v.len() < m);
    });
    scaling::check("sort_dedup_by_key of n numbers", N, |m| {
        let mut v = inputs[&m].clone();
        sorted::sort_dedup_by_key(&mut v, |x| *x);
        assert!(v.len() < m);
    });
    scaling::check("sort_dedup_by of n numbers", N, |m| {
        let mut v = inputs[&m].clone();
        // Ordered by the last three digits; only items equal in full are removed.
        sorted::sort_dedup_by(&mut v, |x, y| (x % 1000).cmp(&(y % 1000)));
        assert!(v.len() < m && v.is_sorted_by_key(|x| x % 1000));
    });
}

/// Small instances: `sorted::tests::sorted_get_matches_a_scan_on_random_keys`.
#[test]
fn n_lookups_in_n_pairs_take_n_log_n() {
    let inputs = built(|m| {
        let pairs: Vec<(u64, usize)> = (0..m).map(|i| (2 * i as u64, i)).collect();
        let keys: Vec<u64> = (0..m).map(|i| spread(i) % (2 * m as u64)).collect();
        (pairs, keys)
    });
    scaling::check_instructions_only("sorted_get of n keys in n pairs", N, 1, |m| {
        let (pairs, keys) = &inputs[&m];
        let found = keys
            .iter()
            .filter(|k| sorted::sorted_get(pairs, *k).is_some())
            .count();
        assert!(found > 0 && found < m);
    });
}

/// Two strictly increasing lists of `m` numbers each, every third number shared.
fn two_lists(m: usize) -> (Vec<u64>, Vec<u64>) {
    let a = (0..m as u64).map(|i| 3 * i).collect();
    let b = (0..m as u64).map(|i| 3 * i + (i % 2)).collect();
    (a, b)
}

/// Small instances: `sorted::tests::unions_of_random_lists_match_a_sort` and
/// `sorted::tests::merge_join_matches_a_scan_with_repeats`.
#[test]
fn merges_take_linear_time() {
    let inputs = built(two_lists);
    scaling::check("merge of two lists of n", N, |m| {
        let (a, b) = &inputs[&m];
        assert!(sorted::merge(a, b).len() > m);
    });
    scaling::check_instructions_only("merge_join of two lists of n", N, 1, |m| {
        let (a, b) = &inputs[&m];
        assert!(sorted::merge_join(a, b, u64::cmp).count() > m);
    });
    // union_all promises O(N log k) only for runs longer than about the square root of N (its
    // doc), so the bench holds k = 64 lists of N / 64 numbers each: O(N log 64) = O(N).
    let lists = built(|m| {
        (0..64u64)
            .map(|k| (0..(m / 64) as u64).map(|i| 64 * i + k).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    });
    scaling::check("union_all of 64 lists of n / 64", N, |m| {
        assert_eq!(sorted::union_all(lists[&m].clone()).len(), m / 64 * 64);
    });
}

/// `m` intervals of `i64`, `(4i + s, 4i + s + 1)`: normal, with gaps.
fn intervals_at(m: usize, s: i64) -> Vec<(i64, i64)> {
    (0..m as i64).map(|i| (4 * i + s, 4 * i + s + 1)).collect()
}

/// Small instances: `intervals::tests::window_matches_members` and
/// `intervals::tests::random_spans_of_i8_match_their_members`.
#[test]
fn interval_lists_take_linear_time_and_coalesce_n_log_n() {
    let inputs = built(|m| (intervals_at(m, 0), intervals_at(m, 1)));
    scaling::check("union of two interval lists of n", N, |m| {
        let (a, b) = &inputs[&m];
        assert_eq!(intervals::union(a, b).len(), m);
    });
    scaling::check("intersect of two interval lists of n", N, |m| {
        let (a, b) = &inputs[&m];
        assert_eq!(intervals::intersect(a, b).len(), m);
    });
    scaling::check("minus of two interval lists of n", N, |m| {
        let (a, b) = &inputs[&m];
        assert_eq!(intervals::minus(a, b).len(), m);
    });
    scaling::check("complement of an interval list of n", N, |m| {
        let (a, _) = &inputs[&m];
        assert_eq!(intervals::complement(a, 0, 4 * m as i64).len(), m);
    });
    let spans = built(|m| {
        (0..m as i64)
            .map(|i| (Some(4 * i), Some(4 * i + 1)))
            .collect::<Vec<_>>()
    });
    scaling::check("complement_spans of a list of n", N, |m| {
        assert_eq!(intervals::complement_spans(&spans[&m]).len(), m + 1);
    });
    scaling::check("n pushes of intervals", N, |m| {
        let mut out = Vec::new();
        for r in &inputs[&m].0 {
            intervals::push(&mut out, *r);
        }
        assert_eq!(out.len(), m);
    });
    let shuffled = built(|m| {
        (0..m)
            .map(|i| {
                let lo = (spread(i) % (8 * m as u64)) as i64;
                (lo, lo + 2)
            })
            .collect::<Vec<_>>()
    });
    scaling::check("coalesce of n intervals in no order", N, |m| {
        assert!(!intervals::coalesce(shuffled[&m].clone()).is_empty());
    });
}

/// Small instances: `search::tests::gallop_matches_partition_point_on_long_lists` and
/// `search::tests::random_borders_at_every_width_are_found`.
#[test]
fn a_gallop_walk_is_linear_and_n_searches_n_log_n() {
    let inputs = built(|m| (0..m as u64).collect::<Vec<_>>());
    // A walk of the list by m / 3 searches, each from where the last stopped: O(log d) each,
    // O(m) in all.
    scaling::check_instructions_only("a gallop walk of a list of n", N, 1, |m| {
        let a = &inputs[&m];
        let (mut from, mut steps) = (0, 0);
        while from < m {
            let target = a[from] + 3;
            from = gallop(a, from, |x| *x < target);
            steps += 1;
        }
        assert_eq!(steps, m.div_ceil(3));
    });
    scaling::check_instructions_only("n searches of 0..n", N, 1, |m| {
        let total: usize = (0..m).map(|t| first_true(0usize, m, |i| *i >= t)).sum();
        assert_eq!(total, m * (m - 1) / 2);
    });
}

/// Small instances: `fenwick::tests::long_trees_match_an_array`.
#[test]
fn n_fenwick_changes_and_prefixes_take_n_log_n() {
    scaling::check("n updates and n prefixes of a Fenwick tree of n", N, |m| {
        let mut t = Fenwick::new(m, 0u64);
        for i in 0..m {
            t.update((spread(i) % m as u64) as usize, |s| *s += 1);
        }
        let total: u64 = (0..m).map(|i| t.prefix(i, 0, |a, s| a + s)).sum();
        assert!(total > 0);
    });
    let trees = built(|m| {
        let mut t = Fenwick::new(m, 0u64);
        for i in 0..m {
            t.update(i, |s| *s += 1);
        }
        t
    });
    scaling::check_instructions_only("n descents of a Fenwick tree of n", N, 1, |m| {
        let t = &trees[&m];
        let total: usize = (0..m as u64)
            .map(|target| t.descend(0u64, |a, s| (a + s <= target).then_some(a + s)).0)
            .sum();
        assert_eq!(total, m * (m - 1) / 2);
    });
}

/// Small instances: `held::tests::values_keep_their_addresses_across_block_ends_and_drop_once`
/// and `intern::tests::ids_agree_with_a_search_of_the_values_seen`.
#[test]
fn puts_and_interning_take_n_log_n_at_most() {
    scaling::check("n puts in a holder", N, |m| {
        let held = Held::default();
        let mut sum = 0u64;
        for i in 0..m {
            sum = sum.wrapping_add(*held.put(spread(i)));
        }
        std::hint::black_box(sum);
    });
    let values = built(with_repeats);
    scaling::check("interning n numbers", N, |m| {
        let mut t: Interner<u64> = Interner::default();
        for x in &values[&m] {
            t.intern(*x);
        }
        assert!(t.len() < m);
    });
}

/// The Cartesian tree of n keys by random priorities, and by rising ones (a path n deep).
/// Small instances: `cartesian::tests::the_build_is_the_recursive_definition` and
/// `cartesian::tests::corners_and_deep_paths`.
#[test]
fn a_cartesian_build_takes_linear_time() {
    let inputs = built(|m| {
        let keys: Vec<u64> = (0..m as u64).collect();
        let random: Vec<u64> = (0..m).map(spread).collect();
        (keys, random)
    });
    for rising in [false, true] {
        let what = match rising {
            false => "the Cartesian tree of n keys by random priorities",
            true => "the Cartesian tree of n keys by rising priorities",
        };
        scaling::check(what, N, |m| {
            let (keys, random) = &inputs[&m];
            let prios = if rising { keys } else { random };
            let made = cartesian::build(keys.clone(), prios, |_, _, l: Option<usize>, r| {
                1 + l.unwrap_or(0) + r.unwrap_or(0)
            });
            assert_eq!(made, Some(m));
        });
    }
}

/// `m / 16` names of 6 letters and `m / 16` written names, each name visible from its own place
/// to the end and every other written name one slip from a name, plus one name of `m / 8`
/// letters and a written name with two of its letters swapped: about `m` characters in all.
/// Small instances: `spelling::tests::the_index_agrees_with_a_check_of_each_pair`.
#[test]
fn the_spelling_index_takes_n_log_n() {
    let word = |i: usize, len: usize| -> String {
        (0..len)
            .map(|j| char::from(b'a' + (spread(i * 7 + j) % 26) as u8))
            .collect()
    };
    let inputs = built(|m| {
        let k = m / 16;
        let mut names: Vec<(String, std::ops::Range<usize>)> =
            (0..k).map(|i| (word(i, 6), i..k + 1)).collect();
        let mut written: Vec<(String, usize)> = (0..k)
            .map(|j| {
                let w = if j % 2 == 0 {
                    // The name at j / 2 with its third letter replaced.
                    let mut w: Vec<char> = names[j / 2].0.chars().collect();
                    w[2] = if w[2] == 'z' { 'y' } else { 'z' };
                    w.into_iter().collect()
                } else {
                    word(k + j, 7)
                };
                (w, j)
            })
            .collect();
        let long = word(2 * k, m / 8);
        let mut swapped: Vec<char> = long.chars().collect();
        let at = (0..swapped.len() - 1)
            .find(|&i| swapped[i] != swapped[i + 1])
            .expect("the long name has two different adjacent letters");
        swapped.swap(at, at + 1);
        names.push((long, 0..k + 1));
        written.push((swapped.into_iter().collect(), k));
        (names, written)
    });
    scaling::check("the spelling index of about n characters", N, |m| {
        let (names, written) = &inputs[&m];
        let names: Vec<(&str, std::ops::Range<usize>)> =
            names.iter().map(|(n, r)| (n.as_str(), r.clone())).collect();
        let written: Vec<(&str, usize)> = written.iter().map(|(w, a)| (w.as_str(), *a)).collect();
        let got = spelling::nearest(&names, &written);
        assert!(got.iter().filter(|g| g.is_some()).count() >= m / 32);
        assert_eq!(
            got.last(),
            Some(&Some(names.last().expect("the long name").0))
        );
    });
}
