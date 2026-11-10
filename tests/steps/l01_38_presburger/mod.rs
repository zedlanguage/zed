//! Step L1.38: the linear-relation domain (DESIGN.md sec:domains, "linear-integer relations
//! among in-scope keys and cardinalities (Presburger)", and sec:verification, rung 2).
//!
//! `entailment` checks rung 2 on the facts the design names, written as Zed functions:
//! `y * w + x < h * w` follows from `0 <= y < h` and `0 <= x < w`, and not from `y <= h`.
//! `preimage` checks the z3 fixtures and the relation a non-box preimage keeps. `random`
//! checks the translation, the Omega test, the projection and entailment against the
//! interpreter at every point of a window, and `controls` checks that a relation of any size is decided, that a question outside
//! the polynomial fragment is refused, and that each check of `random` rejects a wrong
//! answer. `omega` holds the solver's corner cases, and `repair` the greedy
//! search over disjunctions and its repair of one disjunct.

mod canonical;
mod carrier;
mod checker;
mod controls;
mod deep;
mod disj_groups;
mod entailment;
mod extend;
mod front_cost;
mod ids;
mod ladder;
mod linked_nest;
mod live3;
mod mod_symbol;
mod model;
mod model_keys;
mod names;
mod near;
mod omega;
mod one_scope;
mod oracle;
mod preimage;
mod probe;
mod product_parity;
mod q1_local;
pub(crate) mod random;
mod repair;
pub(crate) mod scaling;
mod shared;
mod small_cost;
mod stages;
mod tight;

use std::collections::BTreeMap;
use std::sync::Arc;
use zed_kernel::Shared;

use zed_kernel::{Term, Value, eval};
use zedc::store::int::Int;
use zedc::store::interval::IntervalSet;
use zedc::store::preimage::relations;
use zedc::store::presburger::{Atom, Model};

/// The value of `t` with each of `names` bound to its value in `point`.
fn at(t: &Term, names: &[Arc<str>], point: &[i64]) -> Option<Value> {
    let mut t = t.clone();
    for (n, v) in names.iter().zip(point).rev() {
        t = Term::Let(
            n.clone(),
            Shared::new(Term::Lit(Value::Int(*v))),
            Shared::new(t),
        );
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
            let v = m.get(&Atom::Sym(n.clone())).map_or(Some(0), Int::to_i128);
            v.and_then(|v| i64::try_from(v).ok())
                .expect("a model value within i64")
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
