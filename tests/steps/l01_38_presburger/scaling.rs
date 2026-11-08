//! The Omega test at the rule of low complexity (DESIGN.md Part G). The solver is one loop, and
//! a step touches only the rows of the variable it removes, so the work follows the rows
//! rather than doubling with each variable: `chain(v, 3)` is solved by the dark shadow after one
//! test of the real shadow, and the empty `chain(v, 0)` and `rising(v)` are shown empty by that
//! test alone. Each formula is built before it is timed.

use std::sync::Arc;

use super::stages::Row;

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, decide, satisfiable};

pub(super) fn x(i: usize) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(format!("x{i}"))))
}

/// `3·x[i+1] >= 2·x[i] + 1` and `2·x[i] + k >= 3·x[i+1]` for `i < v`: no elimination is
/// exact, the chain has a point when `k >= 1`, and none when `k == 0`.
fn chain(v: usize, k: i128) -> Formula {
    let mut cons = Vec::new();
    for i in 0..v {
        let a = x(i).times(2);
        let b = x(i + 1).times(3);
        cons.push(Formula::Con(Con::ge(&b, &a.plus(&Lin::constant(1)))));
        cons.push(Formula::Con(Con::ge(&a.plus(&Lin::constant(k)), &b)));
    }
    Formula::and(cons)
}

/// `3·x[i] + 1 <= 2·x[i+1] <= 3·x[i] + 5` for `i < v`, `x[0] >= 0` and `x[v] <= 0`: empty,
/// since each `x[i+1]` is above `x[i]`, but no single step shows it.
fn rising(v: usize) -> Formula {
    let zero = Lin::constant(0);
    let mut cons = vec![
        Formula::Con(Con::ge(&x(0), &zero)),
        Formula::Con(Con::ge(&zero, &x(v))),
    ];
    for i in 0..v {
        let a = x(i).times(3);
        let b = x(i + 1).times(2);
        cons.push(Formula::Con(Con::ge(&b, &a.plus(&Lin::constant(1)))));
        cons.push(Formula::Con(Con::ge(&a.plus(&Lin::constant(5)), &b)));
    }
    Formula::and(cons)
}

#[test]
fn chains_of_inexact_eliminations_are_answered() {
    for v in 1..=15 {
        let m = satisfiable(&chain(v, 3)).expect("answered");
        let m = m.unwrap_or_else(|| panic!("the chain of {v} has a point"));
        assert!(chain(v, 3).holds(&m), "{m:?}");
        assert_eq!(
            satisfiable(&chain(v, 0)),
            Ok(None),
            "the chain of {v} is empty"
        );
        assert_eq!(
            satisfiable(&rising(v)),
            Ok(None),
            "the rising chain of {v} is empty"
        );
    }
}

/// Times `satisfiable` on the formulas of `make` at `n` and 8n variables, built first, each
/// first checked to have a point or none as `point` says: a refusal would be quick and wrong.
fn scales(what: &str, n: usize, point: bool, make: impl Fn(usize) -> Formula) {
    let (small, large) = (make(n), make(scaling::FACTOR * n));
    for f in [&small, &large] {
        let found = satisfiable(f).expect("answered");
        assert_eq!(found.is_some(), point, "{what}");
    }
    scaling::check(what, n, |m| {
        let f = if m == n { &small } else { &large };
        drop(satisfiable(f));
    });
}

#[test]
fn a_chain_of_inexact_eliminations_with_a_point_scales() {
    scales("the chain with a point", 32, true, |v| chain(v, 3));
}

#[test]
fn an_empty_chain_scales() {
    scales("the empty chain", 256, false, |v| chain(v, 0));
}

#[test]
fn a_rising_chain_scales() {
    scales("the rising chain", 128, false, rising);
}

// A cost quadratic with a small constant stays below the limit at the sizes above and shows at
// these. Controls, each a patch to `crates/zedc-presburger/src/presburger.rs`, to run on all six
// tests:
//
// Rows rescanned, in `System::take`, in place of `std::mem::take(&mut self.vars[j].rows)`:
//     let held = |a: &Coefs| a.binary_search_by_key(&j, |t| t.0).is_ok();
//     let ids: Vec<usize> = (0..self.ids.len())
//         .filter(|&id| self.ids[id].as_ref().is_some_and(held))
//         .collect();
//
// A row looked up by scanning, in `System::add`, in place of `self.rows.get_mut(&r.a)`:
//     if let Some((_, old)) = self.rows.iter_mut().find(|(a, _)| **a == r.a) {
//
// The rows copied at each elimination, as a step that builds its rows anew would, at the start
// of `System::eliminate`:
//     drop(self.rows.iter().map(|(a, r)| (a.to_vec(), r.k.clone())).collect::<Vec<_>>());
//
// Variables rescanned, in `System::exact_step` and `System::inexact_step`:
// `self.exact.iter().rev().last()` for `self.exact.first()` and
// `self.inexact.iter().rev().last()` for `self.inexact.first()`.
//
// The real shadow tested at every inexact elimination rather than at the first only, in
// `Omega::run`: `if true {` for `if !self.tested {`, so that `relaxed_empty` runs before each
// dark elimination.

/// The cycle `x[0] >= x[1] >= ... >= x[k-1] >= x[0]`, each in `[-1, 1]`, with the sum in
/// `[1, k - 1]`: the cycle makes the variables equal, so the sum is `-k`, 0 or `k` and there
/// is no integer point; every elimination would add terms to the rows of the sum.
fn cycle(k: usize) -> Formula {
    let one = Lin::constant(1);
    let mut cons = Vec::new();
    let mut sum = Lin::constant(0);
    for i in 0..k {
        cons.push(Formula::Con(Con::ge(&x(i), &x((i + 1) % k))));
        cons.push(Formula::Con(Con::ge(&x(i).plus(&one), &Lin::constant(0))));
        cons.push(Formula::Con(Con::ge(&one, &x(i))));
        sum = sum.plus(&x(i));
    }
    cons.push(Formula::Con(Con::ge(&sum, &one)));
    cons.push(Formula::Con(Con::ge(&Lin::constant(k as i128 - 1), &sum)));
    Formula::and(cons)
}

/// OMEGA-cycle-growth: the cycle's equalities are found as strongly connected components, in
/// O(m log m), before any elimination.
#[test]
fn a_cycle_of_rows_scales() {
    scales("a cycle of rows", 512, false, cycle);
}

#[test]
fn a_long_chain_with_a_point_scales() {
    scales("the long chain with a point", 4096, true, |v| chain(v, 3));
}

#[test]
fn a_long_empty_chain_scales() {
    scales("the long empty chain", 2048, false, |v| chain(v, 0));
}

#[test]
fn a_long_rising_chain_scales() {
    scales("the long rising chain", 2048, false, rising);
}

/// `Σ c·x[i] + k >= 0` over the pairs `(i, c)`, with each `x[i]` moved by `shift(i)` when
/// `shifted`, so that neither the origin nor small values stay points.
fn row(t: &[(usize, i64)], k: i64, shifted: bool) -> Formula {
    let shift = |i: usize| ((i as i64 * 7919 + 13) % 2001) - 1000;
    let k = if shifted {
        k - t.iter().map(|(i, c)| c * shift(*i)).sum::<i64>()
    } else {
        k
    };
    let l = t
        .iter()
        .fold(Lin::constant(k), |l, (i, c)| l.plus(&x(*i).times(*c)));
    Formula::Con(Con::ge(&l, &Lin::constant(0)))
}

/// Three rows of three variables at each `i`, cyclically, shifted: the family on which Bland's
/// rule alone took 453 to 3,132 pivots, not an exponential number. No elimination keeps the rows, so the answer is the
/// refusal [`Refusal::Growth`], given once the box of the bounds shows no row empty and its
/// five points (nearest zero, the corners, the midpoints) each miss a row.
fn sparse(n: usize) -> Formula {
    let mut r = Vec::new();
    for i in 0..n {
        let (a, b, c) = (i, (i + 1) % n, (i + 2) % n);
        r.push(row(&[(a, 2), (b, -3), (c, 1)], 5, true));
        r.push(row(&[(a, -3), (b, 1), (c, -2)], 5, true));
        r.push(row(&[(a, 1), (b, 2), (c, -3)], 5, true));
    }
    Formula::and(r)
}

/// `2n` rows `±x[a] ± x[b] + k >= 0`, shifted, with a point: decided by the parity test.
fn utvpi(n: usize) -> Formula {
    let mut r = Vec::new();
    for i in 0..2 * n {
        let a = (i * 37 + 11) % n;
        let mut b = (i * 53 + 5) % n;
        if a == b {
            b = (b + 1) % n;
        }
        let (ca, cb) = (
            if i % 3 == 0 { -1 } else { 1 },
            if i % 2 == 0 { -1 } else { 1 },
        );
        r.push(row(&[(a, ca), (b, cb)], (i % 4) as i64, true));
    }
    Formula::and(r)
}

/// `x[0] + x[1] == 1` and `x[i] == x[i+1]` around a cycle of `n`: the rational point `1/2`
/// and no integer point, shown by the parity of a zero-weight cycle.
fn odd_cycle(n: usize) -> Formula {
    let mut r = vec![
        row(&[(0, 1), (1, 1)], -1, false),
        row(&[(0, -1), (1, -1)], 1, false),
    ];
    for i in 1..n {
        r.push(row(&[(i, 1), ((i + 1) % n, -1)], 0, false));
        r.push(row(&[((i + 1) % n, 1), (i, -1)], 0, false));
    }
    Formula::and(r)
}

/// `n` disjoint copies of Pugh's example, shifted: each part has two variables and is decided
/// exactly, and each is empty.
fn pugh_pairs(n: usize) -> Formula {
    let mut r = Vec::new();
    for i in 0..n {
        let (a, b) = (2 * i, 2 * i + 1);
        r.push(row(&[(a, 11), (b, 13)], -27, true));
        r.push(row(&[(a, -11), (b, -13)], 45, true));
        r.push(row(&[(a, 7), (b, -9)], 10, true));
        r.push(row(&[(a, -7), (b, 9)], 4, true));
    }
    Formula::and(r)
}

/// Times `decide` on the formulas of `make` at `n` and 8n, built first, each first checked to
/// give `answer`.
pub(super) fn decides(
    what: &str,
    n: usize,
    answer: Result<bool, Refusal>,
    make: impl Fn(usize) -> Formula,
) {
    let (small, large) = (make(n), make(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert_eq!(decide(f), answer, "{what}");
    }
    scaling::check(what, n, |m| {
        let f = if m == n { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}

#[test]
fn the_shifted_sparse_family_scales() {
    decides(
        "the shifted sparse family",
        128,
        Err(Refusal::Growth),
        sparse,
    );
}

#[test]
fn rows_of_two_unit_coefficients_scale() {
    decides("rows of two unit coefficients", 256, Ok(true), utvpi);
}

#[test]
fn an_odd_cycle_scales() {
    decides("an odd cycle", 256, Ok(false), odd_cycle);
}

#[test]
fn disjoint_two_variable_parts_scale() {
    decides(
        "disjoint copies of Pugh's example",
        256,
        Ok(false),
        pugh_pairs,
    );
}

/// `chain(n, 3)` joined at `x[n]` to a block of three rows of three variables at each of `m`
/// places around a cycle, shifted: the chain's dark eliminations come first, and the block
/// then has no elimination that keeps it, so the question is refused with
/// [`Refusal::Growth`]. The splinters of the chain's eliminations are not searched, since a
/// refused dark shadow leaves the answer refused whatever they hold; searching them ran the
/// test again once per elimination.
fn chain_into_block(n: usize) -> Formula {
    let m = 8;
    let mut r = vec![chain(n, 3)];
    for i in 0..m {
        let (a, b, c) = (n + i, n + (i + 1) % m, n + (i + 2) % m);
        r.push(row(&[(a, 2), (b, -3), (c, 1)], 5, true));
        r.push(row(&[(a, -3), (b, 1), (c, -2)], 5, true));
        r.push(row(&[(a, 1), (b, 2), (c, -3)], 5, true));
    }
    Formula::and(r)
}

#[test]
fn a_chain_into_a_refused_block_scales() {
    decides(
        "a chain into a refused block",
        64,
        Err(Refusal::Growth),
        chain_into_block,
    );
}

/// `rows` random rows `±x[i] ± x[j] + k >= 0` over `n` variables, each holding at a random
/// point with slack 0 or 1, so that many are tight there and the system has a point: decided
/// by the parity test, whose shortest-path search must give integer potentials on graphs with
/// long paths of tight edges.
fn random_unit_rows(n: usize, rows: usize, seed: u64) -> Formula {
    let mut g = Rng::new(seed);
    let p: Vec<i64> = (0..n).map(|_| g.int(-50, 50)).collect();
    let mut r = Vec::new();
    for _ in 0..rows {
        let i = g.below(n);
        let mut j = g.below(n);
        if j == i {
            j = (i + 1) % n;
        }
        let t = [(i, 1 - 2 * g.int(0, 1)), (j, 1 - 2 * g.int(0, 1))];
        let at: i64 = t.iter().map(|(i, c)| c * p[*i]).sum();
        r.push(row(&t, g.int(0, 1) - at, false));
    }
    Formula::and(r)
}

#[test]
fn random_rows_of_two_unit_coefficients_with_a_point_are_decided() {
    for n in [16, 64, 256, 1024] {
        for d in [1, 2, 4] {
            let f = random_unit_rows(n, d * n, 0xabc + n as u64);
            assert_eq!(decide(&f), Ok(true), "{n} variables, {} rows", d * n);
            let m = satisfiable(&f).expect("answered").expect("a point");
            assert!(f.holds(&m), "{n} variables, {} rows", d * n);
        }
    }
}

#[test]
fn random_rows_of_two_unit_coefficients_scale() {
    decides("random rows of two unit coefficients", 256, Ok(true), |n| {
        random_unit_rows(n, 4 * n, 0xabc)
    });
}

/// A chain `2·x[i] - 5 <= 3·x[i+1] <= 2·x[i] + 5` with Pugh's example on the link at the
/// middle: empty, since that link is, and no shadow shows it. The first splinter of the chain's
/// dark eliminations that is refused is the answer, [`Refusal::Shadows`]; searching on ran the
/// test again once per bound.
fn pugh_in_a_chain(n: usize) -> Formula {
    let mut r = Vec::new();
    for i in 0..n {
        let (a, b) = (i, i + 1);
        if i == n / 2 {
            r.push(row(&[(a, 11), (b, 13)], -27, false));
            r.push(row(&[(a, -11), (b, -13)], 45, false));
            r.push(row(&[(a, 7), (b, -9)], 10, false));
            r.push(row(&[(a, -7), (b, 9)], 4, false));
        } else {
            r.push(row(&[(b, 3), (a, -2)], 5, false));
            r.push(row(&[(a, 2), (b, -3)], 5, false));
        }
    }
    Formula::and(r)
}

#[test]
fn pughs_example_in_a_chain_scales() {
    decides(
        "Pugh's example in a chain",
        512,
        Err(Refusal::Shadows),
        pugh_in_a_chain,
    );
}

/// Rows `Σ c·x[i] + k >= 0`.
fn rows_of(rows: &[Row]) -> Formula {
    Formula::and(
        rows.iter()
            .map(|(t, k)| {
                let lin = t
                    .iter()
                    .fold(Lin::constant(*k), |l, (i, c)| l.plus(&x(*i).times(*c)));
                Formula::Con(Con::ge(&lin, &Lin::constant(0)))
            })
            .collect(),
    )
}

/// Gemini's relaxed blocks of cross-review XR3 Q1 (`verify_r3.rs`): a block of five rows over
/// x0..x3 and `n - 1` blocks of three rows over four variables each, with a hub `x[4n]` added
/// with coefficient +1 (even blocks) or -1 (odd blocks) to the third row of every block after
/// the first, every variable in [-4, 4]. The hub joins the blocks into one part with `n - 1`
/// wide rows of the hub; no row is below zero over the box and no two rows bound a variable
/// past each other, so the box stage passes every row once and the question is refused.
fn blocks_with_a_hub(n: usize) -> Vec<Row> {
    let mut r: Vec<Row> = [
        ([5, 5, -7, -4], 3),
        ([7, -7, -3, -6], 40),
        ([2, 3, -2, -6], -18),
        ([7, 3, 7, 4], -10),
        ([-7, 2, 5, 4], -5),
    ]
    .iter()
    .map(|(c, k)| ((0..4).map(|j| (j, c[j])).collect(), *k))
    .collect();
    for b in 1..n {
        let rows = [
            ([2, -3, 1, 2], 15),
            ([-3, 1, -2, 3], 15),
            ([1, 2, -3, -2], 15),
        ];
        for (m, (c, k)) in rows.iter().enumerate() {
            let mut t: Vec<(usize, i64)> = (0..4).map(|j| (4 * b + j, c[j])).collect();
            if m == 2 {
                t.push((4 * n, if b % 2 == 0 { 1 } else { -1 }));
            }
            r.push((t, *k));
        }
    }
    for i in 0..=4 * n {
        r.push((vec![(i, 1)], 4));
        r.push((vec![(i, -1)], 4));
    }
    r
}

#[test]
fn the_box_stage_with_a_hub_in_one_row_per_block_scales() {
    // HUB-SCALE: the row test of the box stage (Q1-ROWBOX) is one pass over the terms, so a
    // hub in a row of every block costs nothing per row beyond its own term. Measured
    // 2026-11-03: 9.1 times the instructions from 16 to 128 and 9.3 from 64 to 512; with
    // `row_box_empty` run again over every row of each variable of a row it was 44.6 and
    // 175.2, and with the bounds rebuilt for each row from the rows before it, 32.8 and 49.6.
    decides(
        "the box stage with a hub in one row per block",
        64,
        Err(Refusal::Growth),
        |n| rows_of(&blocks_with_a_hub(n)),
    );
}

/// [`blocks_with_a_hub`] with the rows of `stages::CROSSING` over four more variables, joined
/// to the hub by a row that holds over the box: the row test finds two rows that bound a
/// variable past each other, after it has kept the bounds of about a third of the wide rows
/// (518 of 1538 at n = 512, measured 2026-11-03), so it runs over more rows at 8n.
fn blocks_with_a_hub_and_a_crossing(n: usize) -> Vec<Row> {
    let mut r = blocks_with_a_hub(n);
    let base = 4 * n + 1;
    for (c, k) in super::stages::CROSSING {
        r.push(((0..4).map(|j| (base + j, c[j])).collect(), k));
    }
    r.push((vec![(4 * n, 1), (base, 1)], 8));
    for i in base..base + 4 {
        r.push((vec![(i, 1)], 4));
        r.push((vec![(i, -1)], 4));
    }
    r
}

#[test]
fn the_row_test_of_the_box_scales() {
    // Measured 2026-11-03: 8.7 times the instructions from 16 to 128 and 9.2 from 64 to 512;
    // 46.5 and 209.5 with `row_box_empty` run again over every row of each variable of a row.
    // With the bounds rebuilt for each row it was 12.4 and 21.3, under the limit, since the
    // crossing is found early; the hub family above shows that cost.
    decides(
        "the row test of the box with a crossing after the hub's blocks",
        64,
        Ok(false),
        |n| rows_of(&blocks_with_a_hub_and_a_crossing(n)),
    );
}

/// `x[i] - x[j] <= (i + j) % 3 + 1` for every ordered pair `i != j` of `v` names: indices
/// that lie pairwise within small distances, `v (v - 1)` rows.
fn all_pairs(v: usize) -> Formula {
    let mut cons = Vec::new();
    for i in 0..v {
        for j in 0..v {
            if i != j {
                let d = Lin::constant(((i + j) % 3 + 1) as i64);
                cons.push(Formula::Con(Con::ge(&x(j).plus(&d), &x(i))));
            }
        }
    }
    Formula::and(cons)
}

/// `x[a] - x[b] <= 1` both ways between neighbors in a `v` by `v` grid of names, as the
/// heights of neighboring cells: `4 v (v - 1)` rows.
fn grid(v: usize) -> Formula {
    let mut cons = Vec::new();
    let one = Lin::constant(1);
    let mut pair = |a: usize, b: usize| {
        cons.push(Formula::Con(Con::ge(&x(b).plus(&one), &x(a))));
        cons.push(Formula::Con(Con::ge(&x(a).plus(&one), &x(b))));
    };
    for i in 0..v {
        for j in 0..v {
            if i + 1 < v {
                pair(i * v + j, (i + 1) * v + j);
            }
            if j + 1 < v {
                pair(i * v + j, i * v + j + 1);
            }
        }
    }
    Formula::and(cons)
}

/// `0 <= x[0] <= x[1] <= … <= x[v-1] < n` for a symbolic `n`: `v` sorted indices into an
/// array of length `n`, `3 v - 1` rows; with `strict`, `x[i] < x[i+1]` instead.
fn sorted(v: usize, strict: bool) -> Formula {
    let n = Lin::atom(Atom::Sym(Arc::from("n")));
    let gap = Lin::constant(i64::from(strict));
    let mut cons = Vec::new();
    for i in 0..v {
        cons.push(Formula::Con(Con::ge(&x(i), &Lin::constant(0))));
        cons.push(Formula::Con(Con::ge(&n.minus(&Lin::constant(1)), &x(i))));
        if i + 1 < v {
            cons.push(Formula::Con(Con::ge(&x(i + 1), &x(i).plus(&gap))));
        }
    }
    Formula::and(cons)
}

/// `0 <= x[i] + x[i+1] + x[i+2] <= 10` and `x[i] >= 0` for `i < v`: overlapping sums of three
/// lengths, `3 v` rows.
fn sums(v: usize) -> Formula {
    let mut cons = Vec::new();
    for i in 0..v {
        let s = x(i).plus(&x(i + 1)).plus(&x(i + 2));
        cons.push(Formula::Con(Con::ge(&s, &Lin::constant(0))));
        cons.push(Formula::Con(Con::ge(&Lin::constant(10), &s)));
        cons.push(Formula::Con(Con::ge(&x(i), &Lin::constant(0))));
    }
    Formula::and(cons)
}

/// `f` and `a >= b + k`.
fn with_gap(f: Formula, a: usize, b: usize, k: i64) -> Formula {
    Formula::and(vec![
        f,
        Formula::Con(Con::ge(&x(a), &x(b).plus(&Lin::constant(k)))),
    ])
}

/// `f` and `n <= k` for the symbolic `n` of [`sorted`].
fn with_length_at_most(f: Formula, k: i64) -> Formula {
    let n = Lin::atom(Atom::Sym(Arc::from("n")));
    Formula::and(vec![f, Formula::Con(Con::ge(&Lin::constant(k), &n))])
}

/// The point `satisfiable` finds, checked against `f`; a refusal or an empty answer fails.
fn point_of(what: &str, f: &Formula) {
    match satisfiable(f) {
        Ok(Some(m)) => assert!(f.holds(&m), "{what}: {m:?}"),
        other => panic!("{what}: a point exists, but {other:?}"),
    }
}

#[test]
fn shapes_of_programs_are_answered() {
    // Each family is answered at every size here, none refused (2026-11-05). At f425b32 the
    // ordered pairs were refused from four names on (cross-review xe round 2).
    for v in [2, 3, 4, 5, 8] {
        point_of(&format!("all ordered pairs of {v}"), &all_pairs(v));
        point_of(&format!("a grid of {v} by {v}"), &grid(v));
        point_of(&format!("{v} sorted indices"), &sorted(v, false));
        point_of(&format!("{v} sorted distinct indices"), &sorted(v, true));
        point_of(&format!("{v} overlapping sums"), &sums(v));
        // `x0 - x1 <= 2`, so `x0 >= x1 + 100` is empty.
        let far = with_gap(all_pairs(v), 0, 1, 100);
        assert_eq!(satisfiable(&far), Ok(None), "all ordered pairs of {v}, far");
        // Opposite corners of the grid are `2 (v - 1)` steps apart.
        let corners = with_gap(grid(v), 0, v * v - 1, 2 * (v as i64 - 1));
        point_of(&format!("a grid of {v}, corners at most apart"), &corners);
        let corners = with_gap(grid(v), 0, v * v - 1, 2 * v as i64 - 1);
        assert_eq!(satisfiable(&corners), Ok(None), "a grid of {v}, corners");
        let far = with_gap(grid(v), 0, v * v - 1, 10 * v as i64);
        assert_eq!(satisfiable(&far), Ok(None), "a grid of {v}, far");
        // `v` distinct indices need an array of at least `v`.
        let fits = with_length_at_most(sorted(v, true), v as i64);
        point_of(&format!("{v} distinct indices into {v}"), &fits);
        let short = with_length_at_most(sorted(v, true), v as i64 - 1);
        assert_eq!(
            satisfiable(&short),
            Ok(None),
            "{v} distinct indices into fewer"
        );
        // With `x1, x2 >= 0` (from three sums on), `x0 <= 10`, so `x0 >= x1 + 11` is empty;
        // with two, `x2` may be negative and it is not.
        let long = with_gap(sums(v), 0, 1, 11);
        if v >= 3 {
            assert_eq!(satisfiable(&long), Ok(None), "{v} overlapping sums, long");
        } else {
            point_of(&format!("{v} overlapping sums, long"), &long);
        }
    }
}

/// [`scales`] for a family whose rows grow as the square of its names: `v` names at the
/// sizes `small` and `large`, whose rows are `rows(v)`, eight times as many at `large`.
fn scales_by_rows(
    what: &str,
    (small, large): (usize, usize),
    rows: impl Fn(usize) -> usize,
    make: impl Fn(usize) -> Formula,
) {
    let n = rows(small);
    assert_eq!(rows(large), scaling::FACTOR * n, "{what}");
    let (fs, fl) = (make(small), make(large));
    point_of(what, &fs);
    point_of(what, &fl);
    scaling::check(&format!("{what} (rows)"), n, |m| {
        drop(satisfiable(if m == n { &fs } else { &fl }));
    });
}

#[test]
fn all_ordered_pairs_of_differences_scale() {
    scales_by_rows(
        "all ordered pairs of differences",
        (12, 33),
        |v| v * (v - 1),
        all_pairs,
    );
}

#[test]
fn a_grid_of_differences_scales() {
    scales_by_rows("a grid of differences", (12, 33), |v| 4 * v * (v - 1), grid);
}

#[test]
fn sorted_indices_under_a_symbolic_length_scale() {
    scales("sorted indices", 512, true, |v| sorted(v, false));
}

#[test]
fn overlapping_sums_of_three_scale() {
    scales("overlapping sums of three", 512, true, sums);
}

#[test]
fn a_grid_of_differences_is_decided_in_scale() {
    let (small, large) = (grid(12), grid(33));
    for f in [&small, &large] {
        assert_eq!(decide(f), Ok(true), "a grid of differences");
    }
    scaling::check("deciding a grid of differences (rows)", 528, |m| {
        let _ = std::hint::black_box(decide(if m == 528 { &small } else { &large }));
    });
}

/// The point of a grid of 33 and of 93 names, 4224 and 34224 rows (8.1 times). Until
/// UTVPI-model, once `utvpi::integer_empty` had shown a point, `Omega::run` placed it by
/// eliminating every variable with fill allowed, and this took 31.1 times the instructions
/// (2026-11-05); the point is now rounded from a potential (`utvpi::integer_point`).
/// COMPLEXITY.md S38.
#[test]
fn the_point_of_a_larger_grid_of_differences_scales() {
    let (small, large) = (grid(33), grid(93));
    point_of("a grid of 33", &small);
    point_of("a grid of 93", &large);
    scaling::compare(
        "the point of a grid of differences: 4224 and 34224 rows",
        "8.1 times the rows; the rule of low complexity allows 24 times for 8 (DESIGN.md Part G)",
        scaling::RATIO,
        || drop(satisfiable(&small)),
        || drop(satisfiable(&large)),
    );
}

/// `x[a] - x[b] + k >= 0` for each ordered pair of neighbors in a sparse expander, three
/// neighbors `2v + 1`, `3v + 2` and `v + 1` of each `v`, with `k` a hidden potential's difference
/// plus 1 to 3, so a point exists (cross-review xt2, its `expander` family).
fn expander(n: usize) -> Formula {
    let mut g = Rng::new(0x38_9e);
    let p: Vec<i64> = (0..n).map(|_| g.int(0, 1000)).collect();
    let mut r = Vec::new();
    for v in 0..n {
        for u in [(2 * v + 1) % n, (3 * v + 2) % n, (v + 1) % n] {
            if u == v {
                continue;
            }
            for (a, b) in [(v, u), (u, v)] {
                r.push(row(&[(a, 1), (b, -1)], g.int(1, 3) + p[a] - p[b], false));
            }
        }
    }
    Formula::and(r)
}

/// The point of `expander`'s rows at 256 and 2048 variables, checked against each row
/// (UTVPI-model). Before, placing it eliminated with fill allowed: 277M to 1,500M instructions
/// from 128 to 256 variables (cross-review xt2, note3b.tsv).
#[test]
fn the_point_of_an_expander_of_differences_scales() {
    let (small, large) = (expander(256), expander(scaling::FACTOR * 256));
    point_of("an expander of differences", &small);
    point_of("an expander of differences", &large);
    scaling::check("the point of an expander of differences", 256, |m| {
        drop(satisfiable(if m == 256 { &small } else { &large }));
    });
}
