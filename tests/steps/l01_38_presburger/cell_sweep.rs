//! Guarded chains that reach the cell sweep's less common paths (row
//! TEST-presburger-unreached-paths): a definition two guards can both pick (the overlap and
//! involution sweep), definitions affine in the guard variable, a target given as an equation,
//! a bound, a range or nothing, a top-level disjunction on `i` alone, and a bounded parameter
//! `k`. Every answer is checked against enumeration of the chain's values.

use std::collections::BTreeSet;
use std::sync::Arc;

use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared, decide};

/// Level 0 is `i`; level `j >= 1` has two copies, `t_j` and its twin `t'_j`, defined alike.
fn level(j: usize, twin: bool) -> Lin {
    match j {
        0 => Lin::atom(Atom::Sym(Arc::from("i"))),
        _ => Lin::atom(Atom::Aux(2 * (j as u32 - 1) + u32::from(twin))),
    }
}

fn i_lin() -> Lin {
    level(0, false)
}

fn k_lin() -> Lin {
    Lin::atom(Atom::Sym(Arc::from("k")))
}

fn le(k: i128) -> Formula {
    Formula::Con(Con::ge(&Lin::constant(k), &i_lin()))
}

fn ge(k: i128) -> Formula {
    Formula::Con(Con::ge(&i_lin(), &Lin::constant(k)))
}

/// `t_{j-1} == q`.
fn same(j: usize, q: &Lin) -> Formula {
    Formula::Con(Con::eq(&level(j - 1, false), q))
}

/// `t'_{j-1} + q == c`.
fn flip(j: usize, q: &Lin, c: &Lin) -> Formula {
    Formula::Con(Con::eq(&level(j - 1, true).plus(q), c))
}

fn not(f: Formula) -> Formula {
    Formula::Not(Shared::new(f))
}

fn two() -> Lin {
    Lin::constant(2)
}

/// Builds the definition of `q` at level `j`; the third argument is `k` as a term.
type Make = fn(usize, &Lin, &Lin) -> Formula;
/// The values level `j` can take for `i`, `k`, `t_{j-1}` and `t'_{j-1}`.
type Step = fn(usize, i128, i128, i128, i128) -> Vec<i128>;

pub(crate) struct Family {
    r: i128,
    make: Make,
    step: Step,
    /// `Some((lo, hi))` adds `lo <= k <= hi`; `None` leaves `k` out (its value is then 2).
    k: Option<(i128, i128)>,
    /// Adds the top-level `i <= -2 || i >= 2`.
    split_i: bool,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Target {
    Eq(i128),
    Ge(i128),
    Le(i128),
    Range(i128, i128),
    None,
}

impl Family {
    fn ks(&self) -> Vec<i128> {
        match self.k {
            Some((lo, hi)) => (lo..=hi).collect(),
            None => vec![2],
        }
    }

    fn is(&self) -> impl Iterator<Item = i128> + '_ {
        (-self.r..=self.r).filter(|&i| !self.split_i || !(-2 < i && i < 2))
    }

    /// The values `t_n` takes over every `i` and `k`, with the twin copies chosen
    /// independently below level `n`.
    pub(crate) fn reachable(&self, n: usize) -> BTreeSet<i128> {
        let mut out = BTreeSet::new();
        for k in self.ks() {
            for i in self.is() {
                let mut pairs: BTreeSet<(i128, i128)> = BTreeSet::from([(i, i)]);
                for j in 1..=n {
                    let mut next = BTreeSet::new();
                    for &(t, u) in &pairs {
                        let opts = (self.step)(j, i, k, t, u);
                        for &a in &opts {
                            if j == n {
                                next.insert((a, a));
                            } else {
                                for &b in &opts {
                                    next.insert((a, b));
                                }
                            }
                        }
                    }
                    pairs = next;
                }
                out.extend(pairs.into_iter().map(|(t, _)| t));
            }
        }
        out
    }

    pub(crate) fn chain(&self, n: usize, target: Target) -> Formula {
        let mut parts = vec![le(self.r), ge(-self.r)];
        if self.split_i {
            parts.push(Formula::or(vec![le(-2), ge(2)]));
        }
        let k = match self.k {
            Some((lo, hi)) => {
                parts.push(Formula::Con(Con::ge(&k_lin(), &Lin::constant(lo))));
                parts.push(Formula::Con(Con::ge(&Lin::constant(hi), &k_lin())));
                k_lin()
            }
            None => two(),
        };
        for j in 1..=n {
            let copies: &[bool] = if j < n { &[false, true] } else { &[false] };
            for &twin in copies {
                parts.push((self.make)(j, &level(j, twin), &k));
            }
        }
        let t = level(n, false);
        let c = |v: i128| Lin::constant(v);
        match target {
            Target::Eq(v) => parts.push(Formula::Con(Con::eq(&t, &c(v)))),
            Target::Ge(v) => parts.push(Formula::Con(Con::ge(&t, &c(v)))),
            Target::Le(v) => parts.push(Formula::Con(Con::ge(&c(v), &t))),
            Target::Range(a, b) => {
                parts.push(Formula::Con(Con::ge(&t, &c(a))));
                parts.push(Formula::Con(Con::ge(&c(b), &t)));
            }
            Target::None => {}
        }
        Formula::and(parts)
    }

    fn check(&self, name: &str) {
        let mut wrong = Vec::new();
        for n in 1..=5 {
            let reached = self.reachable(n);
            let lo = *reached.first().expect("some value is reached");
            let hi = *reached.last().expect("some value is reached");
            let miss = (lo..=hi).find(|v| !reached.contains(v));
            let mut targets = vec![
                Target::Eq(lo),
                Target::Eq(hi),
                Target::Eq(hi + 1),
                Target::Ge(hi),
                Target::Ge(hi + 1),
                Target::Le(lo),
                Target::Le(lo - 1),
                Target::None,
            ];
            if let Some(m) = miss {
                targets.push(Target::Eq(m));
                targets.push(Target::Range(m, m));
            }
            for target in targets {
                let expect = match target {
                    Target::Eq(v) => reached.contains(&v),
                    Target::Ge(v) => hi >= v,
                    Target::Le(v) => lo <= v,
                    Target::Range(a, b) => reached.range(a..=b).next().is_some(),
                    Target::None => true,
                };
                let got = decide(&self.chain(n, target));
                if got != Ok(expect) {
                    wrong.push(format!(
                        "n = {n}, target {target:?}: {got:?}, expected Ok({expect})"
                    ));
                }
            }
        }
        assert!(wrong.is_empty(), "{name}:\n{}", wrong.join("\n"));
    }
}

/// `(i <= g && t_n == t_{n-1}) || (i >= h && t_n == c - t'_{n-1})`.
fn guarded_make(j: usize, q: &Lin, c: &Lin, g: i128, h: i128) -> Formula {
    Formula::or(vec![
        Formula::and(vec![le(g), same(j, q)]),
        Formula::and(vec![ge(h), flip(j, q, c)]),
    ])
}

fn guarded_step(i: i128, k: i128, t: i128, u: i128, g: i128, h: i128) -> Vec<i128> {
    let mut v = Vec::new();
    if i <= g {
        v.push(t);
    }
    if i >= h {
        v.push(k - u);
    }
    v
}

/// Guards `i <= (j % 7) - 3` and `i >= (j % 5) - 2`: disjoint below level 5, overlapping on
/// `[-2, 2]` at level 5.
fn late_make(j: usize, q: &Lin, c: &Lin) -> Formula {
    guarded_make(j, q, c, (j % 7) as i128 - 3, (j % 5) as i128 - 2)
}

fn late_step(j: usize, i: i128, k: i128, t: i128, u: i128) -> Vec<i128> {
    guarded_step(i, k, t, u, (j % 7) as i128 - 3, (j % 5) as i128 - 2)
}

/// Guards `i <= 1` and `i >= -1`: both hold on `[-1, 1]` at every level, so the middle
/// levels too are defined by overlapping pieces.
fn mid_make(j: usize, q: &Lin, c: &Lin) -> Formula {
    guarded_make(j, q, c, 1, -1)
}

fn mid_step(_: usize, i: i128, k: i128, t: i128, u: i128) -> Vec<i128> {
    guarded_step(i, k, t, u, 1, -1)
}

/// Disjoint guards `i <= (j / 2) - 1` and its negation.
fn half(j: usize) -> i128 {
    (j / 2) as i128 - 1
}

/// `(i <= g && t_n == t_{n-1}) || (i > g && t'_{n-1} + t_n + i == c)`.
fn affine_flip_make(j: usize, q: &Lin, c: &Lin) -> Formula {
    Formula::or(vec![
        Formula::and(vec![le(half(j)), same(j, q)]),
        Formula::and(vec![
            not(le(half(j))),
            Formula::Con(Con::eq(&level(j - 1, true).plus(q).plus(&i_lin()), c)),
        ]),
    ])
}

fn affine_flip_step(j: usize, i: i128, k: i128, t: i128, u: i128) -> Vec<i128> {
    vec![if i <= half(j) { t } else { k - u - i }]
}

/// `(i <= g && t_n == t_{n-1} + i) || (i > g && t_n == c - t'_{n-1})`.
fn affine_same_make(j: usize, q: &Lin, c: &Lin) -> Formula {
    Formula::or(vec![
        Formula::and(vec![
            le(half(j)),
            Formula::Con(Con::eq(&level(j - 1, false).plus(&i_lin()), q)),
        ]),
        Formula::and(vec![not(le(half(j))), flip(j, q, c)]),
    ])
}

fn affine_same_step(j: usize, i: i128, k: i128, t: i128, u: i128) -> Vec<i128> {
    vec![if i <= half(j) { t + i } else { k - u }]
}

fn late(k: Option<(i128, i128)>, split_i: bool) -> Family {
    Family {
        r: 20,
        make: late_make,
        step: late_step,
        k,
        split_i,
    }
}

pub(crate) fn mid(k: Option<(i128, i128)>, split_i: bool) -> Family {
    Family {
        r: 6,
        make: mid_make,
        step: mid_step,
        k,
        split_i,
    }
}

fn affine_flip(k: Option<(i128, i128)>, split_i: bool) -> Family {
    Family {
        r: 6,
        make: affine_flip_make,
        step: affine_flip_step,
        k,
        split_i,
    }
}

fn affine_same(k: Option<(i128, i128)>, split_i: bool) -> Family {
    Family {
        r: 6,
        make: affine_same_make,
        step: affine_same_step,
        k,
        split_i,
    }
}

#[test]
fn overlap_at_last_level() {
    late(None, false).check("late");
}

#[test]
fn overlap_at_last_level_split_i() {
    late(None, true).check("late, split i");
}

#[test]
fn overlap_at_last_level_with_k() {
    late(Some((0, 3)), false).check("late, k");
}

/// Every target, bounds included, is decided where the guards overlap at every level, with and
/// without `k` (row FAIL-pres-overlap-every-level-refused; these were refused with
/// `Err(Disjuncts)` at n = 3 to 5).
#[test]
fn overlap_at_every_level() {
    mid(None, false).check("mid");
}

#[test]
fn overlap_at_every_level_split_i() {
    mid(None, true).check("mid, split i");
}

#[test]
fn affine_in_flip() {
    affine_flip(None, false).check("affine flip");
}

#[test]
fn affine_in_flip_split_i() {
    affine_flip(None, true).check("affine flip, split i");
}

#[test]
fn affine_in_flip_split_i_with_k() {
    affine_flip(Some((-1, 2)), true).check("affine flip, split i, k");
}

#[test]
fn affine_in_same() {
    affine_same(None, false).check("affine same");
}

#[test]
fn affine_in_same_with_k() {
    affine_same(Some((0, 3)), false).check("affine same, k");
}

#[test]
fn overlap_at_every_level_with_k() {
    mid(Some((0, 3)), false).check("mid, k");
}

#[test]
fn overlap_at_every_level_split_i_with_k() {
    mid(Some((-2, 1)), true).check("mid, split i, k");
}
