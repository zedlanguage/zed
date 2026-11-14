//! The point helpers of step L1.38 (tests/steps/l01_38_presburger and l01_38_omega_test): a
//! term's value at a point, a model as a point, the points of a window and the values each
//! coordinate takes over a set of points.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Shared, Term, Value, eval};
use zedc::store::int::Int;
use zedc::store::interval::IntervalSet;
use zedc::store::presburger::{Atom, Model};

/// The value of `t` with each of `names` bound to its value in `point`.
pub fn at(t: &Term, names: &[Arc<str>], point: &[i64]) -> Option<Value> {
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
pub fn holds(t: &Term, names: &[Arc<str>], point: &[i64]) -> bool {
    at(t, names, point) == Some(Value::Bool(true))
}

/// The values of `names` in a model, each absent one zero, as a point.
pub fn point(m: &Model, names: &[Arc<str>]) -> Vec<i64> {
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
pub fn window(n: usize, lo: i64, hi: i64) -> Vec<Vec<i64>> {
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
pub fn projections(points: &[Vec<i64>], n: usize) -> Vec<IntervalSet> {
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
