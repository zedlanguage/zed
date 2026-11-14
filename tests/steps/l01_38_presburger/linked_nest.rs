//! A nest of shared disjunctions whose disjuncts link each level to the one below it by rows
//! that differ by branch: a test `step(i)` named once and used in both arms of the test above
//! it, each arm relating its own value to the one `step(i - 1)` reads in a different way,
//! `step(i) = (x[i] == x[i - 1] && step(i - 1)) || (x[i] == x[i - 1] + w[i] && step(i - 1))`,
//! `step(0) = x[0] == 0`, with the top value restricted to a residue, `x[k] == m * h + r`, as
//! a running total of optional charges checked for parity at the end. There are 2^k ways
//! through the nest, one for each subset of the weights, and k shared parts. The projection
//! reads each part once per base it is read with (COMPLEXITY.md S31b, PRES-below-key); the base the level
//! above gives a part keeps the residue as a row over the witness `h` whose constant depends on
//! the way taken (`2 h == x[i] + 15` on one, `2 h == x[i] - 1` on another), and those rows are
//! moved to one form before the memo reads them, so the nest costs time linear in k, not 2^k.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_tests::scaling::Meter;
use zedc::store::interval::IntervalSet;
use zedc::store::presburger::{Atom, Con, Formula, Lin, project_each};

pub(super) fn v(s: &str) -> Atom {
    Atom::Sym(Arc::from(s))
}

fn lin(t: &[(&str, i64)], k: i64) -> Lin {
    (t.iter()).fold(Lin::constant(k), |l, (a, c)| {
        l.plus(&Lin::atom(v(a)).times(*c))
    })
}

fn eq(t: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::eq(&lin(t, k), &Lin::constant(0)))
}

/// `step(i)` over the symbols `{x}0`, `{x}1`, … with weights `w[1..=i]`, each level held once
/// (`shared`) or written out with a copy of the level below in each arm.
fn step(x: &str, i: usize, w: &[i64], shared: bool) -> Formula {
    if i == 0 {
        return eq(&[(&format!("{x}0"), 1)], 0);
    }
    let (a, b) = (format!("{x}{i}"), format!("{x}{}", i - 1));
    let below = step(x, i - 1, w, shared);
    let other = if shared {
        below.clone()
    } else {
        step(x, i - 1, w, false)
    };
    Formula::or(vec![
        Formula::and(vec![eq(&[(&a, 1), (&b, -1)], 0), below]),
        Formula::and(vec![eq(&[(&a, 1), (&b, -1)], -w[i]), other]),
    ])
}

/// The nest of `k` levels on `x`, with `x[k] == m * h + r`.
pub(super) fn nest(k: usize, w: &[i64], (m, r): (i64, i64), shared: bool) -> Formula {
    let top = format!("x{k}");
    Formula::and(vec![
        step("x", k, w, shared),
        eq(&[(&top, 1), ("h", -m)], -r),
    ])
}

/// Two nests alike, on `x` and on `y`, with `x[k] + y[k] == m * h + r`: their symbols have one
/// color each pair, so the projection asks its questions as sets (`project_parts` with `sets`).
pub(super) fn twin(k: usize, w: &[i64], (m, r): (i64, i64), shared: bool) -> Formula {
    let (xt, yt) = (format!("x{k}"), format!("y{k}"));
    Formula::and(vec![
        step("x", k, w, shared),
        step("y", k, w, shared),
        eq(&[(&xt, 1), (&yt, 1), ("h", -m)], -r),
    ])
}

/// The partial sums `x[0..=k]` of each way through the nest, one way per subset of `w[1..=k]`.
fn ways(k: usize, w: &[i64]) -> Vec<Vec<i64>> {
    (0..1u32 << k)
        .map(|s| {
            let mut x = vec![0];
            for i in 1..=k {
                let add = if s >> (i - 1) & 1 == 1 { w[i] } else { 0 };
                x.push(x[i - 1] + add);
            }
            x
        })
        .collect()
}

fn set_of(vs: impl IntoIterator<Item = i64>) -> IntervalSet {
    (vs.into_iter().collect::<BTreeSet<i64>>().into_iter())
        .fold(IntervalSet::empty(), |s, x| s.join(&IntervalSet::single(x)))
}

pub(super) const WEIGHTS: [fn(usize) -> i64; 3] =
    [|i| 1 << i, |i| 2 * i as i64 + 1, |i| 3 * i as i64];
pub(super) const RESIDUES: [(i64, i64); 7] =
    [(2, 0), (2, 1), (4, 2), (4, 3), (8, 6), (3, 1), (5, 0)];

/// Each symbol's projection is the set of its values over the ways whose top meets the residue,
/// counted one by one, and the nest held once projects as the nest written out.
#[test]
fn a_linked_nest_projects_to_the_values_of_the_ways_through_it() {
    for k in 1..=5 {
        for weight in WEIGHTS {
            let w: Vec<i64> = (0..=k).map(weight).collect();
            let ways = ways(k, &w);
            for (m, r) in RESIDUES {
                let kept: Vec<&Vec<i64>> = (ways.iter())
                    .filter(|x| (x[k] - r).rem_euclid(m) == 0)
                    .collect();
                let syms = [v("x0"), v("x1"), v(&format!("x{k}"))];
                let want: Vec<IntervalSet> = [0, 1, k]
                    .iter()
                    .map(|&i| set_of(kept.iter().map(|x| x[i])))
                    .collect();
                let what = format!("k = {k}, w = {w:?}, x{k} == {m} h + {r}");
                let shared = project_each(&nest(k, &w, (m, r), true), &syms);
                let apart = project_each(&nest(k, &w, (m, r), false), &syms);
                assert_eq!(format!("{shared:?}"), format!("{apart:?}"), "{what}");
                let (each, skipped) = shared.unwrap_or_else(|e| panic!("{what}: refused {e:?}"));
                assert!(skipped.is_empty(), "{what}: skipped {skipped:?}");
                let got: Vec<IntervalSet> = (each.into_iter())
                    .map(|s| s.unwrap_or_else(|e| panic!("{what}: refused {e:?}")))
                    .collect();
                assert_eq!(got, want, "{what}");
            }
        }
    }
}

/// Two nests whose symbols pair up, answered as sets: the pair held once projects as the pair
/// written out, and each projection holds every value of the ways counted one by one. Depth 1
/// with both weights and every residue; depth 2 with four residues of each weight, among them
/// `x2 + y2 == 4 h + 3` over the weights `2^i`, the slowest at that depth (0.2 s at load 60).
/// Depths 1 to 3 with every residue are in `bench::linked_nest` (4.7 s at load 25; 4.2 s at
/// load 60 of it in two cases at depth 3).
#[test]
fn twin_linked_nests_project_as_written_out_and_keep_every_value() {
    for weight in &WEIGHTS[..2] {
        for (m, r) in RESIDUES {
            twin_projects_as_written_out(1, weight, (m, r));
        }
    }
    for (m, r) in [(2, 0), (4, 2), (4, 3), (5, 0)] {
        twin_projects_as_written_out(2, &WEIGHTS[0], (m, r));
    }
    for (m, r) in [(2, 0), (2, 1), (4, 3), (5, 0)] {
        twin_projects_as_written_out(2, &WEIGHTS[1], (m, r));
    }
}

/// The twin nests of depth `k` and weights `weight(i)` with `x{k} + y{k} == m h + r`: the pair
/// held once projects as the pair written out, and each projection holds every value of the
/// ways counted one by one.
pub(super) fn twin_projects_as_written_out(
    k: usize,
    weight: &fn(usize) -> i64,
    (m, r): (i64, i64),
) {
    let w: Vec<i64> = (0..=k).map(weight).collect();
    let ways = ways(k, &w);
    let syms = [v("x0"), v(&format!("x{k}")), v(&format!("y{k}"))];
    let what = format!("k = {k}, w = {w:?}, x{k} + y{k} == {m} h + {r}");
    let shared = project_each(&twin(k, &w, (m, r), true), &syms);
    let apart = project_each(&twin(k, &w, (m, r), false), &syms);
    assert_eq!(format!("{shared:?}"), format!("{apart:?}"), "{what}");
    let Ok((each, _)) = shared else { return };
    for x in &ways {
        for y in &ways {
            if (x[k] + y[k] - r).rem_euclid(m) != 0 {
                continue;
            }
            for (s, value) in each.iter().zip([x[0], x[k], y[k]]) {
                if let Ok(s) = s {
                    assert!(s.contains(value), "{what}: {value} missing from {s:?}");
                }
            }
        }
    }
}

/// The weights `w[i] = 2^(1 + i mod 50)` of the benchmarks, for `i` in `0..=k`: all even, so
/// that no way through the nest has `x[k]` odd.
pub(super) fn even_weights(k: usize) -> Vec<i64> {
    (0..=k).map(|i| 1i64 << (1 + i % 50)).collect()
}

/// The weights `w[i] = 2^i` of the benchmarks of [`twin`], for `i` in `0..=k`.
pub(super) fn powers_of_two(k: usize) -> Vec<i64> {
    (0..=k).map(|i| 1i64 << i).collect()
}

/// The check the benchmark of [`nest`] makes at each depth: over [`even_weights`] with `x[k]`
/// odd, the projection of `x0` is answered and empty.
pub(super) fn assert_no_way_has_an_odd_top(f: &Formula) {
    let (each, _) = project_each(f, &[v("x0")]).expect("an answer");
    assert!(
        matches!(&each[0], Ok(s) if s.is_empty()),
        "no way has x[k] odd: {each:?}"
    );
}

/// The check the benchmark of [`twin`] makes at each depth: the projection of `x0` and `y0` is
/// answered, not refused.
pub(super) fn assert_twin_answered(f: &Formula) {
    project_each(f, &[v("x0"), v("y0")]).expect("an answer");
}

/// The checks of the benchmarks in `bench/linked_nest.rs`, at small depths.
#[test]
fn the_nests_of_the_benchmarks_are_answered_at_small_depths() {
    for k in [1, 2, 3, 8] {
        assert_no_way_has_an_odd_top(&nest(k, &even_weights(k), (2, 1), true));
    }
    for k in [1, 2, 4] {
        assert_twin_answered(&twin(k, &powers_of_two(k), (2, 1), true));
    }
    exponents("the nest, x[k] odd", &[1, 2, 4], |k| {
        assert_no_way_has_an_odd_top(&nest(k, &even_weights(k), (2, 1), true));
    });
}

/// The instructions of `run` at each of `sizes`, each with its exponent against the size
/// before: 1 for work linear in the size.
pub(super) fn exponents(what: &str, sizes: &[usize], run: impl Fn(usize)) {
    let mut meter = Meter::new();
    let mut last: Option<(usize, u64)> = None;
    for &k in sizes {
        let units = meter.work(|| run(k)).units;
        let exponent =
            last.map(|(k0, u0)| (units as f64 / u0 as f64).ln() / (k as f64 / k0 as f64).ln());
        println!(
            "{what}: k = {k}, {units} {}, exponent {exponent:.2?}",
            meter.unit()
        );
        last = Some((k, units));
    }
}
