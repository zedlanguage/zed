//! Chains of definitions guarded by one input, decided by cells of that input
//! (PERF-project-each-superlinear). The chain `t_j = if (i <= j mod 7 - 3) { t } else { c - t }`
//! over `i` in `[-20, 20]`, asked whether `t_n == 0` at some `i`, is the complement that the
//! transfer before S22a decides for `t_n != 0` (`preimage_ref::linear`): each level is a
//! disjunction whose two disjuncts bound `i` to `..=g` and `g+1..`, and each level's value is
//! written twice, once for each branch that reads it, as the translation writes it. Where no `i`
//! gives zero, the probe over the disjunctions tested each disjunct by a search or a
//! propagation of the whole chain, round after round. The ends of the guards cut `i` into 8
//! cells, in each of which the chain is one conjunction, solved once.

use std::collections::BTreeSet;
use std::sync::Arc;

use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared, decide};

/// The guard at level `j`: `i <= j mod 7 - 3`.
fn guard(j: usize) -> i128 {
    (j % 7) as i128 - 3
}

/// The constant at level `j`: 2, or `j mod 5`.
fn constant(j: usize, varied: bool) -> i128 {
    if varied { (j % 5) as i128 } else { 2 }
}

/// The value of level `j`'s first copy (`twin` false) or second, as an auxiliary atom; level 0
/// is `i` itself.
fn level(j: usize, twin: bool) -> Lin {
    match j {
        0 => Lin::atom(Atom::Sym(Arc::from("i"))),
        _ => Lin::atom(Atom::Aux(2 * (j as u32 - 1) + u32::from(twin))),
    }
}

/// The chain of `n` levels with `t_n == 0` and `i` in `[-20, 20]`, each level but the last
/// written twice: `(i <= g && t == q) || (!(i <= g) && t' + q == c)`, `t` and `t'` the two
/// copies of the level below.
pub(super) fn chain(n: usize, varied: bool) -> Formula {
    let i = level(0, false);
    let le = |l: &Lin, k: i128| Formula::Con(Con::ge(&Lin::constant(k), l));
    let mut parts = vec![le(&i, 20), Formula::Con(Con::ge(&i, &Lin::constant(-20)))];
    for j in 1..=n {
        let copies: &[bool] = if j < n { &[false, true] } else { &[false] };
        for &twin in copies {
            let q = level(j, twin);
            let g = le(&i, guard(j));
            parts.push(Formula::or(vec![
                Formula::and(vec![
                    g.clone(),
                    Formula::Con(Con::eq(&level(j - 1, false), &q)),
                ]),
                Formula::and(vec![
                    Formula::Not(Shared::new(g)),
                    Formula::Con(Con::eq(
                        &level(j - 1, true).plus(&q),
                        &Lin::constant(constant(j, varied)),
                    )),
                ]),
            ]));
        }
    }
    parts.push(Formula::Con(Con::eq(&level(n, false), &Lin::constant(0))));
    Formula::and(parts)
}

/// Whether some `i` in `[-20, 20]` gives `t_n == 0`, by running the chain at each.
pub(super) fn reaches_zero(n: usize, varied: bool) -> bool {
    (-20..=20).any(|i: i128| {
        let t = (1..=n).fold(i, |t, j| {
            if i <= guard(j) {
                t
            } else {
                constant(j, varied) - t
            }
        });
        t == 0
    })
}

/// Decides [`chain`] and checks the answer against [`reaches_zero`].
fn decides(n: usize, varied: bool) {
    let got = decide(&chain(n, varied)).expect("decided");
    assert_eq!(got, reaches_zero(n, varied), "{n} levels, varied {varied}");
}

/// Every chain from 1 to `top` levels, with either constant, is decided as running it decides.
pub(super) fn guarded_chains_up_to(top: usize) {
    for varied in [false, true] {
        for n in 1..=top {
            decides(n, varied);
        }
    }
}

/// The chains from 1 to 35 levels, a whole period of the guards (7) and of the varied constants
/// (5); those up to 96 levels are a long run, so they run in `bench::cells` (author P178).
#[test]
fn guarded_chains_are_decided_as_run() {
    guarded_chains_up_to(35);
}

/// The guard of one level of [`guarded`]: the then-branch keeps `t`, the else-branch gives
/// `2 - t'`, with the guard as written.
#[derive(Clone, Copy)]
pub(super) enum Guard {
    /// `i <= g`.
    Le(i128),
    /// `lo <= i && i <= hi`: the else-branch holds `i < lo || i > hi`, a disjunction.
    And(i128, i128),
    /// `i <= lo || i >= hi`: a disjunction in the then-branch, its pieces overlapping when
    /// `hi <= lo`.
    Or(i128, i128),
    /// `i <= g` with the nested `if (i >= h) { t } else { 2 - t' }` as its then-branch, and
    /// `3 - t'` as its else-branch.
    Nest(i128, i128),
}

/// `i <= k` or `i >= k`.
fn bound(at_most: bool, k: i128) -> Formula {
    let i = level(0, false);
    match at_most {
        true => Formula::Con(Con::ge(&Lin::constant(k), &i)),
        false => Formula::Con(Con::ge(&i, &Lin::constant(k))),
    }
}

fn not(f: Formula) -> Formula {
    Formula::Not(Shared::new(f))
}

/// The chain of `n` levels guarded by `guard(n, j)` over `i` in `[-r, r]`, with `t_n == target`;
/// each level but the last written twice, as [`chain`].
pub(super) fn guarded(
    n: usize,
    r: i128,
    guard: impl Fn(usize, usize) -> Guard,
    target: i128,
) -> Formula {
    let mut parts = vec![bound(true, r), bound(false, -r)];
    for j in 1..=n {
        let copies: &[bool] = if j < n { &[false, true] } else { &[false] };
        for &twin in copies {
            let q = level(j, twin);
            let same = Formula::Con(Con::eq(&level(j - 1, false), &q));
            let flip =
                |c: i128| Formula::Con(Con::eq(&level(j - 1, true).plus(&q), &Lin::constant(c)));
            let (g, then, other) = match guard(n, j) {
                Guard::Le(g) => (bound(true, g), same, flip(2)),
                Guard::And(lo, hi) => (
                    Formula::and(vec![bound(false, lo), bound(true, hi)]),
                    same,
                    flip(2),
                ),
                Guard::Or(lo, hi) => (
                    Formula::or(vec![bound(true, lo), bound(false, hi)]),
                    same,
                    flip(2),
                ),
                Guard::Nest(g, h) => (
                    bound(true, g),
                    Formula::or(vec![
                        Formula::and(vec![bound(false, h), same]),
                        Formula::and(vec![not(bound(false, h)), flip(2)]),
                    ]),
                    flip(3),
                ),
            };
            parts.push(Formula::or(vec![
                Formula::and(vec![g.clone(), then]),
                Formula::and(vec![not(g), other]),
            ]));
        }
    }
    parts.push(Formula::Con(Con::eq(
        &level(n, false),
        &Lin::constant(target),
    )));
    Formula::and(parts)
}

/// The values of `t_n` over `i` in `[-r, r]`, by running the chain at each.
pub(super) fn guarded_run(
    n: usize,
    r: i128,
    guard: impl Fn(usize, usize) -> Guard,
) -> BTreeSet<i128> {
    (-r..=r)
        .map(|i| {
            (1..=n).fold(i, |t, j| match guard(n, j) {
                Guard::Le(g) if i <= g => t,
                Guard::And(lo, hi) if lo <= i && i <= hi => t,
                Guard::Or(lo, hi) if i <= lo || i >= hi => t,
                Guard::Nest(g, h) if i <= g => {
                    if i >= h {
                        t
                    } else {
                        2 - t
                    }
                }
                Guard::Nest(..) => 3 - t,
                _ => 2 - t,
            })
        })
        .collect()
}

/// The guards of the families: `wide` cuts `i` into about `n / 2` cells; `nest` nests an `if` in
/// each then-branch, also over about `n / 2` cells; `or` and `and` join guards by `||` and `&&`
/// (the disjunctions that the cells of [`chain`] left to the probe).
pub(super) fn family(name: &str) -> fn(usize, usize) -> Guard {
    match name {
        "wide" => |n, j| Guard::Le((j / 2) as i128 - (n / 4) as i128),
        "nest" => |n, j| {
            let g = (j / 2) as i128 - (n / 4) as i128;
            Guard::Nest(g, g - 3 - (j % 3) as i128)
        },
        "or" => |_, j| Guard::Or((j % 7) as i128 - 3, (j % 5) as i128 - 2),
        "and" => |_, j| Guard::And((j % 5) as i128 - 2, (j % 7) as i128 - 3),
        other => panic!("no family {other}"),
    }
}

/// The range of `i` for a family at `n` levels: `[-n/2, n/2]` for the wide ones, `[-20, 20]`
/// else.
pub(super) fn family_range(name: &str, n: usize) -> i128 {
    match name {
        "wide" | "nest" => (n / 2).max(1) as i128,
        _ => 20,
    }
}

/// A value of `t_n` inside the range of those reached that no `i` reaches, else one past it.
pub(super) fn missed(reached: &BTreeSet<i128>) -> i128 {
    let (lo, hi) = (reached.first().copied(), reached.last().copied());
    let (lo, hi) = (lo.expect("some value"), hi.expect("some value"));
    (lo..=hi).find(|v| !reached.contains(v)).unwrap_or(hi + 1)
}

/// Every chain of each family from 1 to `top` levels is decided as running it decides, for the
/// least value reached, the greatest, and one inside that is not reached.
pub(super) fn guarded_families_up_to(top: usize) {
    for name in ["wide", "nest", "or", "and"] {
        let guard = family(name);
        for n in 1..=top {
            let r = family_range(name, n);
            let reached = guarded_run(n, r, guard);
            let first = *reached.first().expect("some value");
            let last = *reached.last().expect("some value");
            for target in [first, last, missed(&reached)] {
                let got = decide(&guarded(n, r, guard, target)).expect("decided");
                assert_eq!(
                    got,
                    reached.contains(&target),
                    "{name}, {n} levels, {target}"
                );
            }
        }
    }
}

/// The chains of each family from 1 to 12 levels; those up to 40 levels are a long run, so they
/// run in `bench::cells` (author P178).
#[test]
fn wide_nested_and_joined_guards_are_decided_as_run() {
    guarded_families_up_to(12);
}
