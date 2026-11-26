//! Benchmarks of `hull`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn a_join_costs_near_the_rows_that_differ() {
    // n joins of hulls of n rows differing in one, whose pivot sorts before every other: near
    // n log n in all. Each join walks the left spine of the hull's treap of pivots, as the case
    // of a row after the others below walks the right one, so it is measured as that case is
    // (the comment there), with the rows past N_JOIN after the others. With one hull per size
    // (pivots `x{i}` before rows_of(m)) the ratios under ZED_TREAP_SEED 0 to 7 read 9.53, 6.36,
    // 8.44, 7.22, 11.14, 9.88 (bytes 10.76), 11.13 and 12.96, failing at seeds 4 to 7 (2026-11-17,
    // nightly-2026-11-18, at 3c9c116a4); with the 8 paired families `FAMILIES` 8.94, 8.88, 8.67,
    // 8.78, 9.02, 9.52, 9.17 and 9.05 (mean 9.00), and with families 1 to 8 8.94 and 8.77 at
    // seeds 0 and 1.
    check_families("the join of hulls", "c", |k, i| format!("s{k}a{i}"));
}

#[test]
fn a_join_costs_near_the_rows_that_differ_wherever_they_sort() {
    // As above, with the new row's pivot among the rows' pivots `y…` (`y12a` sorts between
    // `y12` and `y120`) and after all of them.
    let hulls: BTreeMap<usize, Hull> = [N_JOIN, scaling::FACTOR * N_JOIN]
        .into_iter()
        .map(|m| (m, rows_of(m)))
        .collect();
    scaling::check("the join of hulls, a row among the others", N_JOIN, |m| {
        loop_joins(&hulls[&m], m, |i| format!("y{i}a"))
    });
    // A row after all the others: every join walks the right spine of the hull's treap of
    // pivots, the path to its last pivot. A pivot is on that spine when its priority is above
    // that of every pivot after it. With independent uniform priorities the k-th pivot from the
    // right is so with probability 1/k, independently of the others, so the spine of m pivots
    // holds R_m pivots, H_m = 1 + 1/2 + ... + 1/m in expectation (ln m + 0.577), with variance
    // H_m - (1 + 1/4 + ... + 1/m^2), near ln m - 1.07: 10.28 +- 2.94 at 16,384 and 12.36 +- 3.27
    // at 131,072. (Under the 5-wise independent priorities of `zed_collections::priority` the
    // expectation is O(log m), by Seidel and Aragon's bound cited there.) A join costs a constant
    // c0 and c1 per spine pivot, so m joins cost m (c0 + c1 R_m), and the ratio at 8n that the
    // means predict is from 8 (c1 = 0) to 8 H_8n / H_n = 8 * 12.36 / 10.28 = 9.62 (c0 = 0),
    // under the limit.
    //
    // All the joins of one hull walk one spine, so with one hull per size the ratio was one draw
    // of R_8n / R_n, which failed at ZED_TREAP_SEED 0 and 1 (below). Two changes take the
    // measure off one draw without changing its mean:
    // - Pairing: the hull of a family at 8n holds the n rows of its hull at n and 7n rows whose
    //   pivots sort before them (`family_rows`), so R_8n = R_n + D, D the new pivots above every
    //   pivot after them, of mean and variance near H_8n - H_n = ln 8 = 2.08: the spines at the
    //   two sizes share R_n.
    // - Averaging: the joins of each size are shared among the K families `FAMILIES`, m / K
    //   joins each, a family k having the pivots `s{k}…`. Distinct pivots are distinct points of
    //   the run's priority polynomial, so each family has a treap shape of its own, independent
    //   of the others under one draw (`zed_collections::priority`). The work is then
    //   m c0 + (m / K) c1 (R_1 + ... + R_K), and the spread of the sum of spines is that of one
    //   spine over the square root of K.
    // Neither hides a cost of a join that grows with m: it is in the work at both sizes as
    // before; only the shared random part of the spine cancels. The list is fixed, so every run
    // measures the same families. The ratios measured under ZED_TREAP_SEED 0 to 7 (2026-11-17,
    // nightly-2026-11-18, at 994777f73 and 3c9c116a4):
    //   one hull per size              14.16 11.05 9.69 8.90 8.65 6.10 8.97 9.53
    //   one paired family              11.19 8.93 8.49 8.19 8.93 8.62 8.89 8.59
    //   16 families, not paired        10.30 9.02 9.38 9.39 9.52 9.57 8.22 9.79
    //   32 families, not paired        9.95 9.12 9.02 9.52 9.41 9.32 8.69 9.34 (over 20 s when
    //                                  their hulls were built one after another)
    //   8 paired families, `FAMILIES`  9.44 8.99 8.58 9.06 9.06 9.44 9.17 8.96 (mean 9.09)
    //   the same with families 1 to 8  9.17 8.92 (seeds 0 and 1)
    check_families("the join of hulls, a row after the others", "a", |k, i| {
        format!("s{k}zz{i}")
    });
}

/// The families of hulls over which the cases of a row before or after all the others share
/// their joins.
const FAMILIES: std::ops::Range<usize> = 0..8;

/// Checks `what`: at each size m, m joins shared among the families `FAMILIES`, m / |FAMILIES|
/// joins each, of the family's hull of m rows ([`family_rows`] with `extra`) with itself and one
/// more row, `pivot(k, i) == i` at the `i`th join of the family `k`.
fn check_families(what: &str, extra: &str, pivot: impl Fn(usize, usize) -> String + Sync) {
    let families: BTreeMap<usize, Vec<Hull>> = [N_JOIN, scaling::FACTOR * N_JOIN]
        .into_iter()
        .map(|m| {
            // A thread for each family's hull: building them takes far longer than the joins
            // measured, and only the joins are measured.
            let hulls = std::thread::scope(|s| {
                let built: Vec<_> = FAMILIES
                    .map(|k| s.spawn(move || family_rows(k, m, extra)))
                    .collect();
                built
                    .into_iter()
                    .map(|t| t.join().expect("a family's hull"))
                    .collect()
            });
            (m, hulls)
        })
        .collect();
    scaling::check(what, N_JOIN, |m| {
        for (k, h) in FAMILIES.zip(&families[&m]) {
            let mut h = h.clone();
            for i in 0..m / FAMILIES.len() {
                let b = h.clone().and(&lin(&[(&pivot(k, i), 1)], -(i as i128)));
                h = h.join(&b);
            }
            assert_eq!(h.rows().count(), m);
        }
    });
}

/// The hull of `m` rows of the family `k`: the `N_JOIN` rows `s{k}by{i} - s{k}bz{i} == 0`, the
/// same at both sizes, and past `N_JOIN` the rows `s{k}{extra}y{i} - s{k}{extra}z{i} == 0`,
/// whose pivots sort before those for `extra` "a" and after them for "c".
fn family_rows(k: usize, m: usize, extra: &str) -> Hull {
    let rows: Vec<Lin> = (0..m)
        .map(|i| {
            let (p, i) = if i < N_JOIN {
                ("b", i)
            } else {
                (extra, i - N_JOIN)
            };
            lin(
                &[(&format!("s{k}{p}y{i}"), 1), (&format!("s{k}{p}z{i}"), -1)],
                0,
            )
        })
        .collect();
    Hull::of(&rows)
}

#[test]
fn a_hull_is_built_row_by_row_in_time_near_its_rows() {
    // Each row is added to a hull that no one else holds, so it is changed in place.
    let rows: BTreeMap<usize, Vec<Lin>> = [N_BUILD, scaling::FACTOR * N_BUILD]
        .into_iter()
        .map(|m| (m, star(m)))
        .collect();
    scaling::check("building a hull row by row", N_BUILD, |m| {
        let h = Hull::of(&rows[&m]);
        assert_eq!(h.rows().count(), m + 1);
    });
}

/// The sizes, set so the 1x case runs about 0.3 s (TEST-bench-move-l0139; were 256 and 512).
const N_JOIN: usize = 16_384;
const N_BUILD: usize = 65_536;
