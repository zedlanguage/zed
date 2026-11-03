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
use zedc::store::utvpi::integer_empty;

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
        found.as_ref().map(Option::is_some).map_err(|r| *r),
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
        answers(&f, got);
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

fn empty(n: usize, rows: &[(Vec<(usize, Int)>, Int)]) -> bool {
    let rows: Vec<(&[(usize, Int)], &Int)> = rows.iter().map(|(t, k)| (&t[..], k)).collect();
    integer_empty(n, &rows)
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
    assert!(!empty(512, &small) && !empty(scaling::FACTOR * 512, &large));
    scaling::check("the acyclic hub", 512, |n| {
        let rows = if n == 512 { &small } else { &large };
        std::hint::black_box(empty(n, rows));
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
    let n = 2 * k + 1;
    let mut edges: Vec<(usize, usize, i64)> = vec![(0, 1, -3 * k as i64), (0, k, -1)];
    edges.extend((1..k - 1).map(|i| (i, i + 1, 1)));
    edges.extend((1..=k).map(|i| (k, k + i, -1)));
    edges.extend((1..k).map(|i| (i, k, 2 * (k - 1 - i) as i64)));
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

#[test]
fn the_cyclic_hub_scales() {
    // Goldberg and Radzik's search takes three passes at both sizes; Bellman–Ford–Moore took
    // 41.9 times the work (measured on this branch; XT3 measured 42.5).
    let (small, large) = (hub(512, true), hub(scaling::FACTOR * 512, true));
    assert!(!empty(512, &small) && !empty(scaling::FACTOR * 512, &large));
    scaling::check("the cyclic hub", 512, |n| {
        let rows = if n == 512 { &small } else { &large };
        std::hint::black_box(empty(n, rows));
    });
}

#[test]
#[ignore = "fails: the worst case of the potential search, O(V·E), open in item UTVPI-NEAR (COMPLEXITY.md C24)"]
fn bad_gor_scales() {
    // 129 passes at k = 256 and 1,026 at k = 2,048: 58.4 times the work
    // measured on this branch (XT3 measured 62), above the limit of 24.
    let (small, large) = (bad_gor(256, 1), bad_gor(scaling::FACTOR * 256, 1));
    assert!(!empty(small.0, &small.1) && !empty(large.0, &large.1));
    scaling::check("BAD-GOR augmented, by k", 256, |k| {
        let (n, rows) = if k == 256 { &small } else { &large };
        std::hint::black_box(empty(*n, rows));
    });
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
    // five points of the box meets every row, but `x2` has a unit coefficient in every row:
    // the `hull3` stage replaces its rows by the O(m) pairs of the edges of the polyhedron
    // and `twovar` decides the rest, in O(m log m) (XT3 B4).
    decides("three variables in many rows", 64, Ok(true), three_rows);
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
    // coefficient 2 on both sides, no unit side, so the `hull3` stage, whose projection is
    // the real one, does not take it (XT3 B4, the unit condition).
    let mut r = vec![ge(&[(2, 2), (0, -2)], -1), ge(&[(2, -2), (0, 2)], 1)];
    r.extend(within(0, -5, 5));
    r.extend(within(1, -5, 5));
    r.push(ge(&[(0, 1), (1, 3), (2, -1)], 20));
    answers(&Formula::and(r), Ok(false));
}
