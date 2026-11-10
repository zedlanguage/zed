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

use zed_tests::scaling::{self, Meter};
use zedc::store::interval::IntervalSet;
use zedc::store::presburger::{Atom, Con, Formula, Lin, project_each};

fn v(s: &str) -> Atom {
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
fn nest(k: usize, w: &[i64], (m, r): (i64, i64), shared: bool) -> Formula {
    let top = format!("x{k}");
    Formula::and(vec![
        step("x", k, w, shared),
        eq(&[(&top, 1), ("h", -m)], -r),
    ])
}

/// Two nests alike, on `x` and on `y`, with `x[k] + y[k] == m * h + r`: their symbols have one
/// color each pair, so the projection asks its questions as sets (`project_parts` with `sets`).
fn twin(k: usize, w: &[i64], (m, r): (i64, i64), shared: bool) -> Formula {
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

const WEIGHTS: [fn(usize) -> i64; 3] = [|i| 1 << i, |i| 2 * i as i64 + 1, |i| 3 * i as i64];
const RESIDUES: [(i64, i64); 7] = [(2, 0), (2, 1), (4, 2), (4, 3), (8, 6), (3, 1), (5, 0)];

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
/// written out, and each projection holds every value of the ways counted one by one.
#[test]
fn twin_linked_nests_project_as_written_out_and_keep_every_value() {
    for k in 1..=3 {
        for weight in &WEIGHTS[..2] {
            let w: Vec<i64> = (0..=k).map(weight).collect();
            let ways = ways(k, &w);
            for (m, r) in RESIDUES {
                let syms = [v("x0"), v(&format!("x{k}")), v(&format!("y{k}"))];
                let what = format!("k = {k}, w = {w:?}, x{k} + y{k} == {m} h + {r}");
                let shared = project_each(&twin(k, &w, (m, r), true), &syms);
                let apart = project_each(&twin(k, &w, (m, r), false), &syms);
                assert_eq!(format!("{shared:?}"), format!("{apart:?}"), "{what}");
                let Ok((each, _)) = shared else { continue };
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
        }
    }
}

/// The instructions of `run` at each of `sizes`, each with its exponent against the size
/// before: 1 for work linear in the size.
fn exponents(what: &str, sizes: &[usize], run: impl Fn(usize)) {
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

#[test]
fn a_linked_nest_projects_in_time_linear_in_its_depth() {
    let sizes = [16, 32, 64, 128];
    let w: Vec<i64> = (0..=128).map(|i| 1i64 << (1 + i % 50)).collect();
    let inputs = scaling::inputs(16, |k| nest(k, &w, (2, 1), true));
    let syms = [v("x0")];
    let all: Vec<(usize, Formula)> = sizes
        .iter()
        .map(|&k| (k, nest(k, &w, (2, 1), true)))
        .collect();
    exponents("project_each of the linked nest, x[k] odd", &sizes, |k| {
        let f = &all.iter().find(|(n, _)| *n == k).expect("an input").1;
        let (each, _) = project_each(f, &syms).expect("an answer");
        assert!(
            matches!(&each[0], Ok(s) if s.is_empty()),
            "no way has x[k] odd"
        );
    });
    scaling::check("project_each of a linked nest k deep, x[k] odd", 16, |k| {
        let (each, _) = project_each(&inputs[&k], &syms).expect("an answer");
        assert!(
            matches!(&each[0], Ok(s) if s.is_empty()),
            "no way has x[k] odd"
        );
    });
}

#[test]
fn twin_linked_nests_project_in_time_linear_in_their_depth() {
    let sizes = [4, 8, 16, 32];
    let w: Vec<i64> = (0..=32).map(|i| 1i64 << i).collect();
    let syms = [v("x0"), v("y0")];
    let all: Vec<(usize, Formula)> = sizes
        .iter()
        .map(|&k| (k, twin(k, &w, (2, 1), true)))
        .collect();
    exponents(
        "project_each of the twin nests, x[k] + y[k] odd",
        &sizes,
        |k| {
            let f = &all.iter().find(|(n, _)| *n == k).expect("an input").1;
            project_each(f, &syms).expect("an answer");
        },
    );
    let inputs = scaling::inputs(4, |k| twin(k, &w, (2, 1), true));
    scaling::check("project_each of twin linked nests k deep", 4, |k| {
        project_each(&inputs[&k], &syms).expect("an answer");
    });
}
