//! The last stages of the Omega test after design R (STATUS.md, L1.38): the box of the bounds
//! with its five points, the merging of proportional columns, and the potential of a
//! UTVPI graph, in topological order when it has no cycle and by Goldberg and Radzik's search
//! when it has. Their corner cases, and the scaling of each at n and 8n: rows of three terms,
//! the coefficients' bit size, columns seen only through two aggregates, a UTVPI hub with and
//! without cycles, and three variables in many rows.

use std::sync::Arc;

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, Refusal, decide, satisfiable};
use zedc::store::utvpi::{Search, integer_empty, integer_empty_by};

use super::scaling::{decides, x};

/// `Σ c·x[i] + k >= 0`.
fn ge(t: &[(usize, i64)], k: i64) -> Formula {
    let l = t
        .iter()
        .fold(Lin::constant(k), |l, (i, c)| l.plus(&x(*i).times(*c)));
    Formula::Con(Con::ge(&l, &Lin::constant(0)))
}

/// `lo <= x[i] <= hi`.
fn within(i: usize, lo: i64, hi: i64) -> [Formula; 2] {
    [ge(&[(i, 1)], -lo), ge(&[(i, -1)], hi)]
}

/// The rows of the checker's refused question, `Σ c·x[i] + k >= 0` over `x0..x3`: every
/// elimination adds terms, and they hold at `(4, 0, 1, 0)`.
const WIDE: [([i64; 4], i64); 4] = [
    ([4, -10, -12, -12], 11),
    ([10, -10, -11, 4], -28),
    ([4, -1, 12, 11], -28),
    ([-5, 12, -1, -8], 31),
];

fn wide() -> Vec<Formula> {
    WIDE.iter()
        .map(|(c, k)| ge(&[(0, c[0]), (1, c[1]), (2, c[2]), (3, c[3])], *k))
        .collect()
}

/// The value of `x[i]` in a model, zero when absent.
fn value(m: &Model, i: usize) -> i64 {
    let v = m
        .get(&Atom::Sym(Arc::from(format!("x{i}"))))
        .map_or(Some(0), Int::to_i128);
    v.and_then(|v| i64::try_from(v).ok())
        .expect("a small model value")
}

/// `decide(f)` is `answer`, and `satisfiable(f)` agrees, with a model that holds.
fn answers(f: &Formula, answer: Result<bool, Refusal>) {
    assert_eq!(decide(f), answer, "{f}");
    let found = satisfiable(f);
    assert_eq!(
        found.as_ref().map(Option::is_some).map_err(Refusal::clone),
        answer,
        "{f}"
    );
    if let Ok(Some(m)) = found {
        assert!(f.holds(&m), "{m:?} fails {f}");
    }
}

/// Whether some point of the box `[-half, half]^n` meets every row `Σ c·x[i] + k >= 0`.
fn enumerate(rows: &[(Vec<(usize, i64)>, i64)], n: usize, half: i64) -> bool {
    let mut p = vec![-half; n];
    loop {
        if rows
            .iter()
            .all(|(t, k)| t.iter().map(|(i, c)| c * p[*i]).sum::<i64>() + k >= 0)
        {
            return true;
        }
        let mut i = 0;
        loop {
            if i == n {
                return false;
            }
            if p[i] < half {
                p[i] += 1;
                break;
            }
            p[i] = -half;
            i += 1;
        }
    }
}

#[test]
fn no_rows_have_a_point() {
    answers(&Formula::and(Vec::new()), Ok(true));
}

#[test]
fn rows_with_an_empty_box_have_no_point() {
    let mut f = wide();
    f.extend(within(0, 5, 4));
    answers(&Formula::and(f), Ok(false));
}

#[test]
fn rows_whose_box_is_a_single_point_have_that_point() {
    let mut f = wide();
    for (i, v) in [4, 0, 1, 0].into_iter().enumerate() {
        f.extend(within(i, v, v));
    }
    let f = Formula::and(f);
    answers(&f, Ok(true));
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert_eq!(
        (0..4).map(|i| value(&m, i)).collect::<Vec<_>>(),
        [4, 0, 1, 0]
    );
}

#[test]
fn a_variable_with_equal_bounds_is_answered_as_enumeration_answers_or_refused() {
    // `x0` fixed at each of -6..=6 and the others in [-2, 2]. The rows left are three-term rows
    // over (x1, x2, x3) that no elimination keeps; the answer is enumeration's or Growth. At 4
    // the rows hold at (0, 1, 0), which the point of the box nearest zero misses on the third
    // row; another of the five points of the box stage holds every row, so the answer is a
    // point, as the linear program before design R found.
    let mut answered = Vec::new();
    for v in -6..=6 {
        let rows: Vec<(Vec<(usize, i64)>, i64)> = WIDE
            .iter()
            .map(|(c, k)| (vec![(0, c[1]), (1, c[2]), (2, c[3])], k + c[0] * v))
            .collect();
        let truth = enumerate(&rows, 3, 2);
        let mut f = wide();
        f.extend(within(0, v, v));
        for i in 1..4 {
            f.extend(within(i, -2, 2));
        }
        let f = Formula::and(f);
        let got = decide(&f);
        assert!(
            got == Ok(truth) || got == Err(Refusal::Growth),
            "{f}: {got:?}"
        );
        answers(&f, got.clone());
        answered.push((v, got));
    }
    eprintln!("x0 fixed: {answered:?}");
    assert_eq!(answered[10], (4, Ok(true)));
}

#[test]
fn rows_of_three_terms_that_hold_at_zero_have_a_point() {
    // Three rows of three variables at each place around a cycle of 5, each 5 at zero: no
    // elimination keeps them, and the point of the box nearest zero holds every row.
    let n = 5;
    let mut f = Vec::new();
    for i in 0..n {
        let (a, b, c) = (i, (i + 1) % n, (i + 2) % n);
        f.push(ge(&[(a, 2), (b, -3), (c, 1)], 5));
        f.push(ge(&[(a, -3), (b, 1), (c, -2)], 5));
        f.push(ge(&[(a, 1), (b, 2), (c, -3)], 5));
    }
    answers(&Formula::and(f), Ok(true));
}

#[test]
fn a_row_below_zero_over_the_box_shows_the_rows_empty() {
    // `x0 + x1 + x2 >= 4` with each in [-1, 1].
    let mut f = vec![ge(&[(0, 1), (1, 1), (2, 1)], -4)];
    for i in 0..3 {
        f.extend(within(i, -1, 1));
    }
    answers(&Formula::and(f), Ok(false));
}

#[test]
fn proportional_columns_of_mixed_signs_are_decided() {
    // The columns of x0, x1 and x2 are 2, -3 and 5 times one column, so the rows see only
    // `u = 2·x0 - 3·x1 + 5·x2`, which takes every integer: `u == 7` has a point.
    let u = |m: i64| [(0, 2 * m), (1, -3 * m), (2, 5 * m)];
    let f = Formula::and(vec![ge(&u(1), -7), ge(&u(-1), 7), ge(&u(2), -14)]);
    answers(&f, Ok(true));
    // `2·u == 7` has none, by parity.
    let f = Formula::and(vec![ge(&u(2), -7), ge(&u(-2), 7), ge(&u(4), -14)]);
    answers(&f, Ok(false));
    // Two aggregates of opposite signs, `3·a + 5·b` in [7, 8] and `7·a - 4·b` in [3, 4], with
    // `a = x0 - 2·x1` and `b = -x2 + 3·x3`: a = 1, b = 1 is the only point.
    let agg = |p: i64, q: i64| [(0, p), (1, -2 * p), (2, -q), (3, 3 * q)];
    let f = Formula::and(vec![
        ge(&agg(3, 5), -7),
        ge(&agg(-3, -5), 8),
        ge(&agg(7, -4), -3),
        ge(&agg(-7, 4), 4),
    ]);
    answers(&f, Ok(true));
}

/// Rows `x[u] - x[v] + w >= 0` as the parity test takes them.
fn differences(rows: &[(usize, usize, i64)]) -> Vec<(Vec<(usize, Int)>, Int)> {
    rows.iter()
        .map(|&(u, v, w)| {
            let mut t = vec![(u, Int::from(1)), (v, Int::from(-1))];
            t.sort_by_key(|t| t.0);
            (t, Int::from(w))
        })
        .collect()
}

/// Whether the rows have no integer point, by the race of the searches for a potential.
fn raced(n: usize, rows: &[(Vec<(usize, Int)>, Int)]) -> bool {
    let rows: Vec<(&[(usize, Int)], &Int)> = rows.iter().map(|(t, k)| (&t[..], k)).collect();
    integer_empty(n, &rows)
}

/// [`raced`], after checking that each search for a potential, run to its end alone, gives the
/// same answer.
fn empty(n: usize, rows: &[(Vec<(usize, Int)>, Int)]) -> bool {
    let terms: Vec<(&[(usize, Int)], &Int)> = rows.iter().map(|(t, k)| (&t[..], k)).collect();
    let answer = raced(n, rows);
    for search in [Search::GoldbergRadzik, Search::BfDijkstra, Search::Duong] {
        assert_eq!(
            integer_empty_by(n, &terms, search),
            answer,
            "{search:?} on {rows:?}"
        );
    }
    answer
}

#[test]
fn acyclic_and_cyclic_unit_rows_are_decided() {
    // A path with negative weights and no cycle has a point.
    assert!(!empty(
        4,
        &differences(&[(1, 0, -1), (2, 1, -5), (3, 2, -2)])
    ));
    // Two rows around a cycle of weight -1 have none.
    assert!(empty(2, &differences(&[(1, 0, -1), (0, 1, 0)])));
    // A cycle of weight 0 has a point.
    assert!(!empty(
        3,
        &differences(&[(1, 0, -1), (2, 1, -1), (0, 2, 2)])
    ));
    // `x0 + x1 == 1` and `x0 == x1`: the rational point 1/2 and no integer point.
    let one = |t: [(usize, i64); 2], k: i64| {
        (
            t.iter()
                .map(|&(i, c)| (i, Int::from(c)))
                .collect::<Vec<_>>(),
            Int::from(k),
        )
    };
    let odd = [
        one([(0, 1), (1, 1)], -1),
        one([(0, -1), (1, -1)], 1),
        one([(0, 1), (1, -1)], 0),
        one([(0, -1), (1, 1)], 0),
    ];
    assert!(empty(2, &odd));
    // The hub with and without its cycles has a point.
    assert!(!empty(64, &hub(64, false)));
    assert!(!empty(64, &hub(64, true)));
}

/// The hub: `x[i] >= x[i-1] + 1` along half the variables, each of them at least `x[0]`, and
/// `x[0]` at least each of the other half. With `cyclic`, each variable is also within `2n` of
/// its three next neighbors around a cycle, which gives the graph cycles.
fn hub(n: usize, cyclic: bool) -> Vec<(Vec<(usize, Int)>, Int)> {
    let mut r = Vec::new();
    for i in 2..n / 2 {
        r.push((i, i - 1, -1));
    }
    for i in 1..n / 2 {
        r.push((i, 0, 0));
    }
    for i in n / 2..n {
        r.push((0, i, 0));
    }
    if cyclic {
        let w = 2 * n as i64;
        for i in 0..n {
            for d in 1..=3 {
                r.push((i, (i + d) % n, w));
                r.push(((i + d) % n, i, w));
            }
        }
    }
    differences(&r)
}

#[test]
fn the_acyclic_hub_scales() {
    // Through the parity test itself: through `decide` the work around it hides the search's.
    let (small, large) = (hub(512, false), hub(scaling::FACTOR * 512, false));
    assert!(!raced(512, &small) && !raced(scaling::FACTOR * 512, &large));
    scaling::check("the acyclic hub", 512, |n| {
        let rows = if n == 512 { &small } else { &large };
        std::hint::black_box(raced(n, rows));
    });
}

#[test]
fn unit_rows_around_cycles_are_decided() {
    // `x0 >= x1 + 1` and `x1 >= x0`: a cycle of weight -1, no point.
    assert!(empty(2, &differences(&[(0, 1, -1), (1, 0, 0)])));
    // Each step of a path one or two up: edges both ways along the path, a point.
    assert!(!empty(512, &two_way_path(512)));
    // The graph on which the search's passes grow with the nodes has a point.
    let (n, rows) = bad_gor(64, 1);
    assert!(!empty(n, &rows));
}

/// Five variables whose pairwise sums lie in `[-100, 100]`, with the cycle `x0 <= x2 <= x1 <=
/// x3 <= x0`, so `x0 = x1 = x2 = x3`, and `x0 + x4 >= 0`, `x4 <= x1 - 1`, so `2·x0 >= 1` and,
/// over the integers, `x0 >= 1`. With `obstruction`, also `x0 + x1 <= 1`, so `2·x0 <= 1`:
/// the rows meet at `x0 = 1/2` and at no integer point. No row states the equalities; they come
/// from a cycle of weight zero, odd through `x4`.
fn octagon(obstruction: bool) -> Formula {
    let mut rows = Vec::new();
    for i in 0..5 {
        for j in i + 1..5 {
            rows.push(ge(&[(i, 1), (j, 1)], 100));
            rows.push(ge(&[(i, -1), (j, -1)], 100));
        }
    }
    if obstruction {
        rows.push(ge(&[(0, -1), (1, -1)], 1));
    }
    for t in [
        [(0, -1), (2, 1)],
        [(2, -1), (1, 1)],
        [(1, -1), (3, 1)],
        [(3, -1), (0, 1)],
        [(0, 1), (4, 1)],
    ] {
        rows.push(ge(&t, 0));
    }
    rows.push(ge(&[(4, -1), (1, 1)], -1));
    Formula::and(rows)
}

#[test]
fn a_dense_octagon_with_a_parity_obstruction_has_no_point() {
    // From the xt round 1 review (wt/xt2/r1_codex_zed_impl.patch). `random_graphs_get_the_
    // decisions_of_bellman_ford_moore` in utvpi.rs checks the searches against one another and
    // the parity test against itself; this checks `decide` against an answer found by hand.
    answers(&octagon(true), Ok(false));
    answers(&octagon(false), Ok(true));
    let rows: Vec<(Vec<(usize, i64)>, i64)> = vec![
        (vec![(0, -1), (1, -1)], 1),
        (vec![(0, -1), (2, 1)], 0),
        (vec![(2, -1), (1, 1)], 0),
        (vec![(1, -1), (3, 1)], 0),
        (vec![(3, -1), (0, 1)], 0),
        (vec![(0, 1), (4, 1)], 0),
        (vec![(4, -1), (1, 1)], -1),
    ];
    assert!(!enumerate(&rows, 5, 6));
}

/// A cycle of `n` variables with `x[j+d] >= x[j] + d` for `d` in 1 to 3, indices mod `n`, the
/// rows that wrap around loosened by `n + 3`: one strongly connected component whose shortest
/// paths hold about `n` negative edges, ordered against the order of the variables. It has the
/// point `x[j] = j`. From the xt round 2 synthesis (wt/xt2/synth/gemini-work/verify_gemini.rs),
/// measured there at 12.8 times from 64 to 512 on the race of that time.
fn negchain(n: usize) -> Formula {
    let c = n as i64 + 3;
    let mut rows = Vec::new();
    for j in 0..n {
        for d in 1..=3 {
            let t = (j + d) % n;
            let wrap = if j + d >= n { c } else { 0 };
            rows.push(ge(&[(t, 1), (j, -1)], -(d as i64) + wrap));
        }
    }
    Formula::and(rows)
}

#[test]
fn a_cycle_of_negative_edges_scales() {
    for n in [4, 5, 64] {
        let f = negchain(n);
        let m = satisfiable(&f).expect("decided").expect("a point");
        assert!(f.holds(&m), "{m:?}");
        // With `x0 >= x[n-1] + n + 3` as well, the rows of `d = 1` give
        // `x[n-1] >= x0 + n - 1`, so `x0 >= x0 + 2n + 2`: no point.
        let c = n as i64 + 3;
        let tight = Formula::and(vec![f, ge(&[(0, 1), (n - 1, -1)], -c)]);
        answers(&tight, Ok(false));
    }
    // From 2048 variables (6144 rows), so that a quadratic step is caught however cheap the
    // work per pair of rows: a scan of all rows per row comparing only their lengths gave
    // 18.8 times from 512 and passed, and gives 43.5 times from 2048 (2026-11-05, load 78).
    decides("a cycle of negative edges", 2048, Ok(true), negchain);
}

/// `x[i] + 1 <= x[i+1] <= x[i] + 2` for each `i < n - 1`.
fn two_way_path(n: usize) -> Rows {
    let rows: Vec<(usize, usize, i64)> = (0..n - 1)
        .flat_map(|i| [(i + 1, i, -1), (i, i + 1, 2)])
        .collect();
    differences(&rows)
}

/// Rows of one or two unit terms and their constants, as the parity test takes them.
type Rows = Vec<(Vec<(usize, Int)>, Int)>;

/// BAD-GOR of Cherkassky and Goldberg as Cassis et al. 2025 (arXiv 2502.11999, appendix) give
/// it, over `2k + 1` variables, its nodes 1 to 2k + 1 at 0 to 2k, an edge `u → v` of weight `w`
/// the row `x[v] <= x[u] + w`. Augmented as there: 5m random rows of one weight above every
/// path's, and the variables renamed by a random permutation, from `seed`. On it the
/// topological order of the edges of negative reduced cost moves one step per pass of
/// Goldberg and Radzik's search (COMPLEXITY.md C24).
fn bad_gor(k: usize, seed: u64) -> (usize, Rows) {
    augmented(2 * k + 1, bad_gor_edges(k), seed)
}

/// The edges over `n` nodes augmented as BAD-GOR is in [`bad_gor`], as rows.
fn augmented(n: usize, mut edges: Vec<(usize, usize, i64)>, seed: u64) -> (usize, Rows) {
    let heavy = n as i64 + 1 + edges.iter().map(|e| e.2.abs()).sum::<i64>();
    let mut g = Rng::new(seed);
    for _ in 0..5 * edges.len() {
        let (a, b) = (g.below(n), g.below(n));
        if a != b {
            edges.push((a, b, heavy));
        }
    }
    let mut name: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        name.swap(i, g.below(i + 1));
    }
    // The row `x[v] <= x[u] + w` is `x[u] - x[v] + w >= 0`.
    let rows: Vec<(usize, usize, i64)> = edges
        .into_iter()
        .map(|(u, v, w)| (name[u], name[v], w))
        .collect();
    (n, differences(&rows))
}

/// The edges `(u, v, w)` of BAD-GOR before it is augmented, over the nodes 0 to 2k: a path from
/// 1 to k - 1 of weight 1 edges, an edge from 0 to 1 of weight -3k, an edge from each of 0 to
/// k - 1 into k, and edges of weight -1 from k to the k leaves k + 1 to 2k. It has no cycle.
fn bad_gor_edges(k: usize) -> Vec<(usize, usize, i64)> {
    let mut edges = vec![(0, 1, -3 * k as i64), (0, k, -1)];
    edges.extend((1..k - 1).map(|i| (i, i + 1, 1)));
    edges.extend((1..=k).map(|i| (k, k + i, -1)));
    edges.extend((1..k).map(|i| (i, k, 2 * (k - 1 - i) as i64)));
    edges
}

/// The edges of the fan of [`bad_gor_and_fan`] on the `2k + 2` nodes from `a`: a path of `k`
/// edges of weight -1 from `a`, an edge of weight 0 from each of its first `k` nodes into the hub
/// `a + k + 1`, and edges of weight 0 from the hub to `k` leaves; with `back`, an edge of weight
/// `k + 1 + back` from each leaf to `a`, and without, no cycle.
fn fan_edges(a: usize, k: usize, back: Option<i64>) -> Vec<(usize, usize, i64)> {
    let hub = a + k + 1;
    let mut fan = Vec::new();
    for i in 0..k {
        fan.push((a + i, a + i + 1, -1));
        fan.push((a + i, hub, 0));
        fan.push((hub, hub + 1 + i, 0));
        if let Some(back) = back {
            fan.push((hub + 1 + i, a, k as i64 + 1 + back));
        }
    }
    fan
}

/// BAD-GOR unaugmented over `2k + 1` variables and beside it the fan of [`bad_gor_and_fan`]
/// without its edges back to `a`: a graph with no cycle, over `4k + 3` variables. Without the
/// pass in topological order, Goldberg and Radzik's search takes passes in proportion to `k` on
/// the first part, and BF-Dijkstra `k` rounds of `k` work on the second.
fn acyclic_bad_gor_and_fan(k: usize) -> (usize, Rows) {
    let a = 2 * k + 1;
    let mut edges = bad_gor_edges(k);
    edges.extend(fan_edges(a, k, None));
    (a + 2 * k + 2, differences(&edges))
}

#[test]
fn the_cyclic_hub_scales() {
    // Goldberg and Radzik's search takes three passes at both sizes; Bellman–Ford–Moore took
    // 41.9 times the work (measured on this branch; XT3 measured 42.5).
    let (small, large) = (hub(512, true), hub(scaling::FACTOR * 512, true));
    assert!(!raced(512, &small) && !raced(scaling::FACTOR * 512, &large));
    scaling::check("the cyclic hub", 512, |n| {
        let rows = if n == 512 { &small } else { &large };
        std::hint::black_box(raced(n, rows));
    });
}

#[test]
fn bad_gor_scales() {
    // Goldberg and Radzik's search alone takes 129 passes at k = 256 and 1,026 at k = 2,048:
    // 59.8 times the work (78.2M to 4.68G instructions, measured on this branch as the negative
    // control and not kept; XT3 measured 62). The race with BF-Dijkstra and Duong's search
    // takes 26.8M to 209M instructions, 7.8 times (COMPLEXITY.md C24).
    let (small, large) = (bad_gor(256, 1), bad_gor(scaling::FACTOR * 256, 1));
    assert!(!raced(small.0, &small.1) && !raced(large.0, &large.1));
    scaling::check("BAD-GOR augmented, by k", 256, |k| {
        let (n, rows) = if k == 256 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

/// BAD-GOR augmented as in [`bad_gor`], with each weight 1 edge `i → i + 1` of its path split
/// through a node of its own into an edge of weight -1 and one of weight 2, over `3k - 1`
/// variables. The path's labels are BAD-GOR's, so Goldberg and Radzik's search still moves one
/// step per pass (the weight 2 edge has reduced cost 1 at the start of the pass), and each step
/// now holds a negative edge, so BF-Dijkstra takes a round per step, each lowering the hub `k`
/// and its `k` leaves again: slow for both along the same shortest paths.
fn split_bad_gor(k: usize, seed: u64) -> (usize, Rows) {
    augmented(3 * k - 1, split_bad_gor_edges(k), seed)
}

/// The edges of [`split_bad_gor`] before it is augmented, over the nodes 0 to 3k - 2.
fn split_bad_gor_edges(k: usize) -> Vec<(usize, usize, i64)> {
    let mut edges = vec![(0, 1, -3 * k as i64), (0, k, -1)];
    for i in 1..k - 1 {
        let mid = 2 * k + i;
        edges.extend([(i, mid, -1), (mid, i + 1, 2)]);
    }
    edges.extend((1..=k).map(|i| (k, k + i, -1)));
    edges.extend((1..k).map(|i| (i, k, 2 * (k - 1 - i) as i64)));
    edges
}

/// [`split_bad_gor`] beside its reverse, every edge turned around, on `3k - 1` further
/// variables, augmented together as in [`bad_gor`], so that the random rows join them in one
/// strongly connected component: slow for Goldberg and Radzik's search and BF-Dijkstra on the
/// graph and on its reverse.
fn split_bad_gor_both_ways(k: usize) -> (usize, Rows) {
    let half = 3 * k - 1;
    let mut edges = split_bad_gor_edges(k);
    let back: Vec<(usize, usize, i64)> = edges
        .iter()
        .map(|&(u, v, w)| (half + v, half + u, w))
        .collect();
    edges.extend(back);
    augmented(2 * half, edges, 1)
}

#[test]
fn split_bad_gor_is_decided() {
    let (n, rows) = split_bad_gor(64, 1);
    assert!(!empty(n, &rows));
    let (n, rows) = split_bad_gor_both_ways(64);
    assert!(!empty(n, &rows));
}

#[test]
fn split_bad_gor_scales() {
    // Measured in instructions from k = 128 to k = 1,024 (UTVPI-both-slow, load 58 to 68):
    // Goldberg and Radzik's search alone 32.7M to 1,694M (51.8 times), BF-Dijkstra alone 46.6M
    // to 2,826M (60.7 times), the two sharing labels 98.2M to 5,943M (60.5 times; sharing one
    // way only, 56 to 58 times), Duong's search alone 535M to 6,218M (11.6 times), and the race
    // of the pair and Duong's search 175M to 9,778M (55.9 times; 33.5 times the bytes). On
    // the reverse of the graph the pair is quick, and the race with a second pair searching
    // it takes 24.2M to 198M (8.2 times; COMPLEXITY.md C24).
    let (small, large) = (
        split_bad_gor(128, 1),
        split_bad_gor(scaling::FACTOR * 128, 1),
    );
    assert!(!raced(small.0, &small.1) && !raced(large.0, &large.1));
    scaling::check("BAD-GOR with its path split, by k", 128, |k| {
        let (n, rows) = if k == 128 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

#[test]
fn split_bad_gor_both_ways_scales() {
    // Slow for both quick searches on the graph and on its reverse, so Duong's search finishes
    // first. From k = 128 to 1,024 the race takes 445M to 9,425M instructions (21.2 times; 17.2
    // times the bytes; load 11 to 21). Before Duong's constant factor was lowered it took 385M
    // to 30,322M (78.7 times; UTVPI-both-ways): a race of quadratic searches with Duong's passes
    // such a family only from about a third of the size where Duong's search starts to finish
    // first (COMPLEXITY.md C24).
    let (small, large) = (
        split_bad_gor_both_ways(128),
        split_bad_gor_both_ways(scaling::FACTOR * 128),
    );
    scaling::check(
        "BAD-GOR with its path split, and its reverse, by k",
        128,
        |k| {
            let (n, rows) = if k == 128 { &small } else { &large };
            std::hint::black_box(raced(*n, rows));
        },
    );
}

/// BAD-GOR augmented over `2k + 1` variables, and beside it on `2k + 2` further variables a fan:
/// a path of `k` edges of weight -1 from `a = 2k + 1`, an edge of weight 0 from each of its
/// first `k` nodes into a hub, edges of weight 0 from the hub to `k` leaves, and an edge of
/// weight `k + 1 + back` from each leaf to `a`. The fan alone makes BF-Dijkstra take `k`
/// rounds of `k` work; BAD-GOR alone makes Goldberg and Radzik's search take `k / 2` passes.
/// With `back = -3` the fan has a cycle of weight -1.
fn bad_gor_and_fan(k: usize, back: i64) -> (usize, Rows) {
    let (a, mut rows) = bad_gor(k, 1);
    // The row `x[v] <= x[u] + w` is `x[u] - x[v] + w >= 0`.
    rows.extend(differences(&fan_edges(a, k, Some(back))));
    (a + 2 * k + 2, rows)
}

#[test]
fn bad_gor_and_a_fan_are_decided() {
    let (n, rows) = bad_gor_and_fan(64, 0);
    assert!(!empty(n, &rows));
    let (n, rows) = bad_gor_and_fan(64, -3);
    assert!(empty(n, &rows));
}

#[test]
fn bad_gor_and_a_fan_scale() {
    // BAD-GOR and the fan share no variable, so the split by strongly connected components
    // searches each alone, and each is slow for only one of the searches. Measured in
    // instructions from k = 256 to k = 2,048 (UTVPI-union): 36.1M to 301.2M, 8.3 times. The race
    // over the whole graph, before the split, took 202M to 12,236M (60.6 times; 48.8 times the
    // bytes in the negative control, run once and not committed), since both quadratic searches
    // are cheaper than Duong's below k = 2,048 (COMPLEXITY.md C24).
    let (small, large) = (
        bad_gor_and_fan(256, 0),
        bad_gor_and_fan(scaling::FACTOR * 256, 0),
    );
    assert!(!raced(small.0, &small.1) && !raced(large.0, &large.1));
    scaling::check("BAD-GOR augmented and a fan, by k", 256, |k| {
        let (n, rows) = if k == 256 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

#[test]
fn bad_gor_and_a_fan_with_no_cycle_scale() {
    // The split by strongly connected components decides this graph in one pass in topological
    // order, since every component is one node; each of the three searches alone is slow on it.
    // Measured in instructions from k = 256 to k = 2,048: the split 5.29M to 42.3M (8.0 times);
    // Goldberg and Radzik's search 20.7M to 1,093M (52.8 times); BF-Dijkstra 44.6M to 2,891M
    // (64.8 times); Duong's search 573M to 6,203M (10.8 times, but the most work at both sizes).
    // Before UTVPI-union, the race without the pass took 141.3M to 9,142.5M (64.7 times). Since
    // UTVPI-union the race shares labels between its two quadratic searches, and without the
    // split it passes here, 20.1M to 166.4M (8.3 times), as does `the_acyclic_hub_scales` (the
    // control, run once and not committed); the split costs 8.4 times less than BF-Dijkstra
    // alone at k = 256, and 3.8 times less than the race without it.
    let (small, large) = (
        acyclic_bad_gor_and_fan(256),
        acyclic_bad_gor_and_fan(scaling::FACTOR * 256),
    );
    assert!(!empty(small.0, &small.1));
    scaling::check("BAD-GOR and a fan with no cycle, by k", 256, |k| {
        let (n, rows) = if k == 256 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

/// The rows `Σ c·x[i] + k >= 0` as a conjunction, for `decide`.
fn formula(rows: &[(Vec<(usize, Int)>, Int)]) -> Formula {
    Formula::and(
        rows.iter()
            .map(|(t, k)| {
                let l = t.iter().fold(Lin::constant(k.clone()), |l, (i, c)| {
                    l.plus(&x(*i).times(c.clone()))
                });
                Formula::Con(Con::ge(&l, &Lin::constant(0)))
            })
            .collect(),
    )
}

/// [`bad_gor_and_fan`] with no negative cycle, and edges of a weight above every path's from
/// each node of the fan to the next two around a ring of its `2k + 2` nodes. The ring lies on no
/// shortest path, and leaves each variable of the fan in three rows or more each way, so that
/// eliminating it adds rows (fill above 0) and `decide` passes the graph to the search whole.
/// With `joined`, two more such edges, from variable 0 of BAD-GOR to the fan's first node and
/// back, make the whole graph one strongly connected component. With `flipped`, every edge of
/// the fan is reversed, which puts the half slow for BF-Dijkstra in the same sign of the literal
/// graph as the half slow for Goldberg and Radzik's search; unflipped, they fall in opposite
/// signs, so different components, even when joined.
fn union_family(k: usize, joined: bool, flipped: bool) -> (usize, Rows) {
    let (a, len) = (2 * k + 1, 2 * k + 2);
    let (n, mut rows) = (a + len, bad_gor(k, 1).1);
    let fan = fan_edges(a, k, Some(0));
    let fan = if flipped {
        fan.into_iter().map(|(u, v, w)| (v, u, w)).collect()
    } else {
        fan
    };
    rows.extend(differences(&fan));
    let heavy = (n * n) as i64;
    let mut edges: Vec<(usize, usize, i64)> = (0..len)
        .flat_map(|i| [1, 2].map(|d| (a + i, a + (i + d) % len, heavy)))
        .collect();
    if joined {
        edges.extend([(0, a, heavy), (a, 0, heavy)]);
    }
    rows.extend(differences(&edges));
    (n, rows)
}

/// [`union_family`] not joined, and a row of three terms that joins its halves through a fresh
/// variable `y` of coefficient 1: `y + x[0] - x[a] >= 0`. Since `y` is bounded on one side only,
/// `decide` drops it and its row, and the halves reach the search apart: before UTVPI-union,
/// `decide` took 421M to 3,852M instructions here, as on the family unjoined.
fn wide_row_family(k: usize) -> Formula {
    let (n, rows) = union_family(k, false, false);
    let wide = ge(&[(n, 1), (0, 1), (2 * k + 1, -1)], 0);
    Formula::and(vec![formula(&rows), wide])
}

#[test]
fn the_union_family_is_decided() {
    for (joined, flipped) in [(false, false), (true, false), (false, true), (true, true)] {
        let (n, rows) = union_family(64, joined, flipped);
        assert!(!empty(n, &rows));
    }
    assert_eq!(decide(&wide_row_family(64)), Ok(true));
}

#[test]
fn the_joined_union_family_scales() {
    // Joined and flipped, both slow halves lie in one strongly connected component: the split
    // by components leaves 459k to 25.9M units (56 times) to the old race. The race whose two
    // quadratic searches share labels takes 38.1M to 332.8M instructions (8.7 times). The old
    // code took 253M to 15,604M (47.6 times the bytes; negative control, not committed).
    let (small, large) = (
        union_family(256, true, true),
        union_family(scaling::FACTOR * 256, true, true),
    );
    assert!(!raced(small.0, &small.1) && !raced(large.0, &large.1));
    scaling::check("the joined union family, by k", 256, |k| {
        let (n, rows) = if k == 256 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

#[test]
fn the_union_family_scales_through_decide() {
    decides(
        "the union family through decide, by k",
        256,
        Ok(true),
        |k| formula(&union_family(k, false, false).1),
    );
}

#[test]
fn the_joined_union_family_scales_through_decide() {
    // The old code took 618M to 18,351M instructions here (29.7 times). Unjoined, and joined by
    // a wide row, `decide` splits the halves into parts before the search and passed before too.
    decides(
        "the joined union family through decide, by k",
        256,
        Ok(true),
        |k| formula(&union_family(k, true, true).1),
    );
}

#[test]
fn the_wide_row_family_scales_through_decide() {
    decides(
        "the union family joined by a wide row, through decide, by k",
        256,
        Ok(true),
        wide_row_family,
    );
}

/// `2n` rows of up to three terms over `n` variables, as the tight family, each coefficient
/// times `2^bits` plus a small odd number, each row holding at a fixed point with slack at most
/// 3.
fn tight_bits(n: usize, bits: u32) -> Formula {
    let mut g = Rng::new(0xfeed_beef_1380);
    let p: Vec<i64> = (0..n).map(|_| g.int(-50, 50)).collect();
    let mut r = Vec::new();
    for _ in 0..2 * n {
        let mut t: Vec<(usize, i64)> = Vec::new();
        for _ in 0..3 {
            let i = g.below(n);
            if !t.iter().any(|q| q.0 == i) {
                let c = g.int(-5, 5);
                t.push((i, if c == 0 { 1 } else { c }));
            }
        }
        let mut scale = |c: i64| -> Int {
            let mut v = Int::from(c);
            for _ in 0..bits {
                v = &v * &Int::from(2);
            }
            &v + &Int::from(g.int(0, 3) * 2 + 1)
        };
        let cs: Vec<(usize, Int)> = t.iter().map(|(i, c)| (*i, scale(*c))).collect();
        let at = cs
            .iter()
            .fold(Int::from(0), |s, (i, c)| &s + &(c * &Int::from(p[*i])));
        let k = &Int::from(g.int(0, 3)) - &at;
        let l = cs.iter().fold(Lin::constant(k), |l, (i, c)| {
            l.plus(&x(*i).times(c.clone()))
        });
        r.push(Formula::Con(Con::ge(&l, &Lin::constant(0))));
    }
    Formula::and(r)
}

#[test]
fn coefficients_of_many_bits_scale() {
    // 64 variables, coefficients of 64 and of 512 bits: the work is linear in the bits, and
    // the answer is the same.
    let (small, large) = (tight_bits(64, 64), tight_bits(64, 512));
    for f in [&small, &large] {
        assert_eq!(decide(f), Err(Refusal::Growth));
    }
    scaling::check("the tight family by coefficient bits", 64, |b| {
        let f = if b == 64 { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}

/// `n` variables seen only through two aggregates, `a` over the first half and `b` over the
/// second, each variable's coefficient `1 + j % 3`: `7 <= 3·a + 5·b <= 8` and
/// `3 <= 7·a - 4·b <= 4`, whose only point is a = b = 1. Merging the proportional columns
/// leaves two variables, which the count under the envelopes decides.
fn aggregates(n: usize) -> Formula {
    let h = n / 2;
    let agg = |lo: usize, s: i64| {
        (lo..lo + h).fold(Lin::constant(0), |l, j| {
            l.plus(&x(j).times(s * (1 + (j % 3) as i64)))
        })
    };
    let a3 = agg(0, 3).plus(&agg(h, 5));
    let a7 = agg(0, 7).plus(&agg(h, -4));
    Formula::and(vec![
        Formula::Con(Con::ge(&a3, &Lin::constant(7))),
        Formula::Con(Con::ge(&Lin::constant(8), &a3)),
        Formula::Con(Con::ge(&a7, &Lin::constant(3))),
        Formula::Con(Con::ge(&Lin::constant(4), &a7)),
    ])
}

#[test]
fn columns_seen_through_two_aggregates_scale() {
    decides("two aggregates", 64, Ok(true), aggregates);
    let f = aggregates(64);
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert!(f.holds(&m), "{m:?}");
}

/// `m` rows over three variables, half lower and half upper bounds of `x2` with unit
/// coefficient over `x0` and `x1` with coefficients up to a million, each holding at
/// (3, -2, 5) with slack at most 3.
fn three_rows(m: usize) -> Formula {
    let mut g = Rng::new(0x3_3333);
    let p = [3i64, -2, 5];
    let mut r = Vec::new();
    for i in 0..m {
        let s = if i % 2 == 0 { 1 } else { -1 };
        let (a, b) = (g.int(-1_000_000, 1_000_000), g.int(-1_000_000, 1_000_000));
        let t = [(0usize, a), (1, b), (2, s)];
        let at: i64 = t.iter().map(|(i, c)| c * p[*i]).sum();
        r.push(ge(&t, g.int(0, 3) - at));
    }
    Formula::and(r)
}

#[test]
fn three_variables_in_many_rows_scale() {
    // The rows hold at (3, -2, 5). No elimination keeps them from growing and none of the
    // five points of the box meets every row, so `live3` decides them, in O(m log m). `x2` has
    // a unit coefficient in every row. With the `hull3` stage, which projected it out first,
    // the work grew 14.2 times from 64 to 512 rows, so the stage was removed (HULL3-subsumed).
    // At 64 rows `live3` finds the point in 6.7M instructions and 0.85 MB, a path the larger
    // sizes do not take, so the sizes are 128 and 1,024: 210M to 399M instructions, 8.3 MB to
    // 26.7 MB (512 to 4,096 rows: 392M to 454M, 22.2 MB to 56.4 MB). The cost depends on the
    // instance, not on its size: this seed takes 215M at 32 rows, 6.7M at 64 and 9.9M at 96, and
    // summed over 12 seeds 64 to 512 rows is 2.8 times the instructions and 4.7 the bytes
    // (HULL3-subsumed merge), so the ratio at 64 is that one cheap instance's.
    decides("three variables in many rows", 128, Ok(true), three_rows);
    let f = three_rows(64);
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert!(f.holds(&m), "{m:?}");
}

/// Three variables in `[-10, 10]` and `m` rows `c·x + k >= 0` with coefficients up to a
/// million, each holding at the upper corner (10, 10, 10) with slack up to `10·Σ|c|`, so that
/// the rows are spread over the box and one of the five points holds them all.
fn rows_held_in_a_box(m: usize) -> Formula {
    let mut g = Rng::new(0x3_5555);
    let mut r: Vec<Formula> = (0..3).flat_map(|i| within(i, -10, 10)).collect();
    for _ in 0..m {
        let c = [0, 1, 2].map(|_| g.int(-1_000_000, 1_000_000));
        let reach: i64 = c.iter().map(|c| 10 * c.abs()).sum();
        let at: i64 = c.iter().map(|c| 10 * c).sum();
        let t = [(0usize, c[0]), (1, c[1]), (2, c[2])];
        r.push(ge(&t, g.int(0, reach) - at));
    }
    Formula::and(r)
}

#[test]
fn a_box_point_held_by_many_rows_scales() {
    // No elimination keeps these rows, so the box stage answers, and a point holds every row:
    // the stage reads each row once for each point it tries, which is linear in the rows.
    decides(
        "a box point held by many rows",
        256,
        Ok(true),
        rows_held_in_a_box,
    );
}

#[test]
fn twice_a_variable_odd_has_no_point() {
    // 2·x2 = 2·x0 + 1 has a real point for every x0 in -5..5 and no integer one. `x2` has
    // coefficient 2 on both sides, so its real projection is not its integer one; `live3`
    // decides the rows over three variables exactly.
    let mut r = vec![ge(&[(2, 2), (0, -2)], -1), ge(&[(2, -2), (0, 2)], 1)];
    r.extend(within(0, -5, 5));
    r.extend(within(1, -5, 5));
    r.push(ge(&[(0, 1), (1, 3), (2, -1)], 20));
    answers(&Formula::and(r), Ok(false));
}

/// A row `Σ c·x[i] + k >= 0`, as the pairs `(i, c)` and `k`.
pub(super) type Row = (Vec<(usize, i64)>, i64);

/// Whether the rows `Σ c·x[i] + k >= 0` over `n` variables have no rational point:
/// Fourier–Motzkin over every variable, each row divided by the gcd of its entries, with
/// checked `i128` arithmetic (the rows here are small enough; an overflow panics).
pub(super) fn rationally_empty(rows: &[Row], n: usize) -> bool {
    let mut cur: Vec<(Vec<i128>, i128)> = rows
        .iter()
        .map(|(t, k)| {
            let mut c = vec![0i128; n];
            for (i, x) in t {
                c[*i] += i128::from(*x);
            }
            (c, i128::from(*k))
        })
        .collect();
    let gcd = |mut a: i128, mut b: i128| {
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a.abs()
    };
    let mul = |a: i128, b: i128| a.checked_mul(b).expect("no overflow");
    let add = |a: i128, b: i128| a.checked_add(b).expect("no overflow");
    for j in 0..n {
        let (mut pos, mut neg, mut rest) = (Vec::new(), Vec::new(), Vec::new());
        for r in cur {
            match r.0[j].signum() {
                1 => pos.push(r),
                -1 => neg.push(r),
                _ => rest.push(r),
            }
        }
        for (pa, pk) in &pos {
            for (qa, qk) in &neg {
                let (a, b) = (pa[j], -qa[j]);
                let mut c: Vec<i128> = (0..n).map(|i| add(mul(b, pa[i]), mul(a, qa[i]))).collect();
                let mut k = add(mul(b, *pk), mul(a, *qk));
                let g = c.iter().fold(k, |g, x| gcd(g, *x));
                if g > 1 {
                    c.iter_mut().for_each(|x| *x /= g);
                    k /= g;
                }
                rest.push((c, k));
            }
        }
        rest.sort();
        rest.dedup();
        cur = rest;
    }
    cur.iter().any(|(_, k)| *k < 0)
}

/// One of the oracle's 400 systems over four variables in [-4, 4] (seed 0x38_0a,
/// `oracle::small_coefficients_over_four_variables_match_enumeration`), as `(c, k)` for
/// `Σ c·x[i] + k >= 0`: every elimination adds terms and no row is below zero over the box,
/// but two rows bound a variable by rationals that cross.
pub(super) const CROSSING: [([i64; 4], i64); 4] = [
    ([-6, -6, 2, -7], -17),
    ([2, -3, -4, -1], -20),
    ([2, -2, 4, 1], -17),
    ([3, 5, -7, -1], -12),
];

/// The rows of [`CROSSING`] with each constant raised by `s`, and the formula of those rows
/// with each variable in [-4, 4] except where `free` drops its lower bound.
fn crossing(s: i64, free: Option<usize>) -> (Vec<Row>, Formula) {
    let mut rows: Vec<Row> = CROSSING
        .iter()
        .map(|(c, k)| ((0..4).map(|i| (i, c[i])).collect(), k + s))
        .collect();
    let mut f: Vec<Formula> = rows.iter().map(|(t, k)| ge(t, *k)).collect();
    for i in 0..4 {
        let [lo, hi] = within(i, -4, 4);
        if free != Some(i) {
            f.push(lo);
            rows.push((vec![(i, 1)], 4));
        }
        f.push(hi);
        rows.push((vec![(i, -1)], 4));
    }
    (rows, Formula::and(f))
}

#[test]
fn two_rows_that_bound_a_variable_past_each_other_show_the_rows_empty() {
    // The box of the bounds is [-4, 4] × [-4, 2] × [0, 1] × [-4, 4]; with the other variables
    // in it, one row bounds a variable from below past the bound another row gives it from
    // above. Fourier–Motzkin and enumeration agree that there is no point (Q1-ROWBOX).
    let (rows, f) = crossing(0, None);
    assert!(rationally_empty(&rows, 4));
    assert!(!enumerate(&rows, 4, 4));
    answers(&f, Ok(false));
    // Without the lower bound of x0 the rows still have no rational point, and the bounds
    // the other rows give x0 show it.
    let (rows, f) = crossing(0, Some(0));
    assert!(rationally_empty(&rows, 4));
    answers(&f, Ok(false));
}

#[test]
fn rows_with_a_rational_point_are_not_shown_empty_by_the_box() {
    // The same rows, each constant raised by 8 to 11, have rational and integer points, and
    // the row test of the box keeps them: they are refused with Growth, as before the row
    // test (deciding them needs a complete method at four live variables, cross-review XR3
    // Q1). A box test that showed empty a system with a rational point would answer Ok(false).
    // With x3 or x0 unbounded below they keep their points. With x3 unbounded below its
    // exact elimination adds no terms once the rows it writes are counted (`System::shrink`,
    // Q1-LOCAL), and they are decided, with a model that `answers` checks.
    for free in [None, Some(0), Some(3)] {
        for s in 8..=11 {
            let (rows, f) = crossing(s, free);
            assert!(!rationally_empty(&rows, 4), "s = {s}, {free:?}");
            if free.is_none() {
                assert!(enumerate(&rows, 4, 4), "s = {s}");
            }
            let answer = if free == Some(3) {
                Ok(true)
            } else {
                Err(Refusal::Growth)
            };
            answers(&f, answer);
        }
    }
}

#[test]
fn rows_the_one_pass_test_does_not_show_empty_stay_refused() {
    // Raised by 1 to 7 the rows have no rational point, but no single row bounds a variable
    // past another's bound over the tightened box, so the one-pass test does not find it
    // (the resolvent stage that would was not adopted, XR3 Q1). With x3 unbounded below even
    // the rows of `CROSSING` are not shown empty: the row with -7·x3 then bounds only x3.
    // Measured 2026-11-03; a stronger complete method may later decide these Ok(false).
    // With x0 unbounded below they stay refused. With x3 unbounded below they are decided
    // since Q1-LOCAL: the exact elimination of x3 adds no terms counted by the rows it writes
    // (`System::shrink`), and the rows left show no point (measured 2026-11-08).
    for s in 1..=7 {
        let (rows, f) = crossing(s, None);
        assert!(rationally_empty(&rows, 4), "s = {s}");
        assert!(!enumerate(&rows, 4, 4), "s = {s}");
        answers(&f, Err(Refusal::Growth));
        let (rows, f) = crossing(s, Some(0));
        assert!(rationally_empty(&rows, 4), "s = {s}");
        answers(&f, Err(Refusal::Growth));
    }
    for s in 0..=7 {
        let (rows, f) = crossing(s, Some(3));
        assert!(rationally_empty(&rows, 4), "s = {s}");
        answers(&f, Ok(false));
    }
}

#[test]
fn a_row_with_no_variables_decides_by_its_constant() {
    // `-1 >= 0` with the rows of `CROSSING` raised by 8 (which have a point): no point;
    // `0 >= 0` changes nothing.
    let (_, f) = crossing(8, None);
    answers(&Formula::and(vec![f.clone(), ge(&[], -1)]), Ok(false));
    answers(&Formula::and(vec![f, ge(&[], 0)]), Err(Refusal::Growth));
}
