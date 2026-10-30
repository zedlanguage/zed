//! Step L1.38: the linear-relation domain (DESIGN.md sec:domains, "linear-integer relations
//! among in-scope keys and cardinalities (Presburger)", and sec:verification, rung 2).
//!
//! `entailment` checks rung 2 on the facts the design names, written as Zed functions:
//! `y * w + x < h * w` follows from `0 <= y < h` and `0 <= x < w`, and not from `y <= h`.
//! `preimage` checks the z3 fixtures and the relation a non-box preimage keeps. `random`
//! checks the translation, the Omega test, the projection and entailment against the
//! interpreter at every point of a window, and `controls` checks the budgets of step M0.5
//! and that each check of `random` rejects a wrong answer.

mod controls;
mod entailment;
mod preimage;
mod random;

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Term, Value, eval};
use zedc::store::interval::IntervalSet;
use zedc::store::preimage::relations;
use zedc::store::presburger::{Atom, Model, Relation};

use crate::l01_25_preimage_catalog::function;

/// The parameters of `ok` in `src`, and the relation its body states, products of two
/// symbols as atoms.
fn relation(src: &str) -> (Vec<Arc<str>>, Relation) {
    let (ps, body) = function(src);
    let r = relations(&[&body], &ps, true)
        .unwrap_or_else(|| panic!("{src}: outside the linear-relation domain"));
    (ps, r.into_iter().next().expect("one relation"))
}

/// The value of `t` with each of `names` bound to its value in `point`.
fn at(t: &Term, names: &[Arc<str>], point: &[i64]) -> Option<Value> {
    let mut t = t.clone();
    for (n, v) in names.iter().zip(point).rev() {
        t = Term::Let(n.clone(), Arc::new(Term::Lit(Value::Int(*v))), Arc::new(t));
    }
    eval(&t).ok()
}

/// Whether the test `t` holds at `point`.
fn holds(t: &Term, names: &[Arc<str>], point: &[i64]) -> bool {
    at(t, names, point) == Some(Value::Bool(true))
}

/// The values of `names` in a model, each absent one zero, as a point.
fn point(m: &Model, names: &[Arc<str>]) -> Vec<i64> {
    names
        .iter()
        .map(|n| {
            let v = *m.get(&Atom::Sym(n.clone())).unwrap_or(&0);
            i64::try_from(v).expect("a model value within i64")
        })
        .collect()
}

/// Each point of the square window `[lo..=hi]` in `n` dimensions, the last axis fastest.
fn window(n: usize, lo: i64, hi: i64) -> Vec<Vec<i64>> {
    let mut out = vec![Vec::new()];
    for _ in 0..n {
        out = out
            .into_iter()
            .flat_map(|p| {
                (lo..=hi).map(move |v| {
                    let mut q = p.clone();
                    q.push(v);
                    q
                })
            })
            .collect();
    }
    out
}

/// The values each coordinate takes over `points`, as sets.
fn projections(points: &[Vec<i64>], n: usize) -> Vec<IntervalSet> {
    let mut vals: Vec<BTreeMap<i64, ()>> = vec![BTreeMap::new(); n];
    for p in points {
        for (j, v) in p.iter().enumerate() {
            vals[j].insert(*v, ());
        }
    }
    vals.into_iter()
        .map(|vs| {
            vs.keys().fold(IntervalSet::empty(), |s, v| {
                s.join(&IntervalSet::single(*v))
            })
        })
        .collect()
}
