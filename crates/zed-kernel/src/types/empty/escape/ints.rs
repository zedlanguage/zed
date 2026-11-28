//! The integer sets of the escape solve ([`super`]): `Ints`, and `only_ints`, which says when a
//! type's parts are integers alone. They have a file of their own so that [`super::crossing`]
//! can use them without importing `escape.rs`, which imports `crossing.rs`: Zed allows no import
//! cycle between files (step S.1f).

use std::collections::BTreeSet;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::digest::Digest;
use crate::types::{Lits, Parts, Type};
use crate::value::Value;

/// A set of integers: `vals` when not `cof`, else the integers less `vals`.
// Complexity tradeoff: `n` rows sharing a width-`w` head `not_a` (`xr_bucket`) previously cloned,
// hashed and compared `BTreeSet<Value>` of size `w` once per row in `Nodes::ints`, `orig_live`,
// `U1` partner bucketing and `ids`, costing `Theta(n * w)`. Wrapping `vals` in `Rc` with a
// precomputed 64-bit `Digest` makes `Clone` and `Hash` `O(1)`, and `PartialEq` `O(1)` whenever
// hashes differ or `Rc::ptr_eq` holds (such as shared `Nodes::heads` and memoized place-1 cells).
#[derive(Clone, Debug)]
pub(in super::super) struct Ints {
    pub(in super::super) cof: bool,
    hash: u64,
    pub(in super::super) vals: Rc<BTreeSet<Value>>,
}

impl PartialEq for Ints {
    #[inline]
    fn eq(&self, o: &Ints) -> bool {
        self.cof == o.cof
            && self.hash == o.hash
            && (Rc::ptr_eq(&self.vals, &o.vals) || *self.vals == *o.vals)
    }
}

impl Eq for Ints {}

/// By `cof`, the hash, then the values, so that a [`crate::digest::TiedMap`] can keep sets of
/// one hash in order (PERF-typeset-tied-digest). It agrees with `==`: `hash` is a function of
/// `cof` and the values ([`Ints::new`]), so sets equal by `==` compare `Equal`, and sets that
/// compare `Equal` have equal `cof` and values, so are equal by `==`.
impl Ord for Ints {
    fn cmp(&self, o: &Ints) -> std::cmp::Ordering {
        let head = (self.cof, self.hash).cmp(&(o.cof, o.hash));
        if head.is_ne() || Rc::ptr_eq(&self.vals, &o.vals) {
            return head;
        }
        self.vals.cmp(&o.vals)
    }
}

impl PartialOrd for Ints {
    fn partial_cmp(&self, o: &Ints) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}

impl Hash for Ints {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

impl Ints {
    pub(super) fn new(cof: bool, vals: BTreeSet<Value>) -> Ints {
        let mut d = Digest::default();
        cof.hash(&mut d);
        vals.hash(&mut d);
        Ints {
            cof,
            hash: d.finish(),
            vals: Rc::new(vals),
        }
    }

    /// The integer set of `t`, if `t` holds integers and nothing else. Wide integers
    /// (`Value::Big`) are kept as values too: the escape only compares and hashes them (round 10).
    pub(in super::super) fn of(t: &Type) -> Option<Ints> {
        let p = t.p();
        if !only_ints(&p) {
            return None;
        }
        let mut vals = BTreeSet::new();
        for v in p.ints.values.iter() {
            match v {
                v @ (Value::Int(_) | Value::Big(_)) => {
                    vals.insert(v.clone());
                }
                // The integers of a type hold `Value::Int` and `Value::Big` alone: they are
                // made by `Type::lit` of an integer, `Type::ints_of` (which asserts it) and the
                // universe (cofinite, no values), and changed only by `Lits::zip` and
                // `Lits::not` with other integer sets, which keep values from their operands
                // (TEST-kernel-unreached-paths-4, kernel12). Checked again by kernel13 over every
                // write of a `Parts`'s `ints` in the crate: besides those, `Parts::join_literals`
                // inserts the values of another type's `ints`, and `Type::split`
                // (`types/empty.rs`) and the clones `q.ints = p.ints.clone()` copy one type's
                // `ints` whole; none moves a value between the kinds of literal.
                _ => unreachable!("a value in a type's integers that is no integer"),
            }
        }
        Some(Ints::new(p.ints.cofinite, vals))
    }

    pub(in super::super) fn is_empty(&self) -> bool {
        !self.cof && self.vals.is_empty()
    }

    /// Whether `self ⊆ o`.
    pub(super) fn subset(&self, o: &Ints) -> bool {
        match (self.cof, o.cof) {
            (false, false) => {
                self.vals.len() <= o.vals.len() && self.vals.iter().all(|x| o.vals.contains(x))
            }
            (false, true) => {
                if self.vals.len() <= o.vals.len() {
                    self.vals.iter().all(|x| !o.vals.contains(x))
                } else {
                    o.vals.iter().all(|x| !self.vals.contains(x))
                }
            }
            (true, false) => false,
            (true, true) => {
                o.vals.len() <= self.vals.len() && o.vals.iter().all(|x| self.vals.contains(x))
            }
        }
    }

    /// Whether `self ∩ o` is empty.
    pub(super) fn disjoint(&self, o: &Ints) -> bool {
        match (self.cof, o.cof) {
            (false, _) => self.vals.iter().all(|x| o.cof == o.vals.contains(x)),
            (true, false) => o.disjoint(self),
            (true, true) => false,
        }
    }

    pub(in super::super) fn meet(&self, o: &Ints) -> Ints {
        match (self.cof, o.cof) {
            (false, _) => Ints::new(
                false,
                self.vals
                    .iter()
                    .filter(|x| o.cof != o.vals.contains(x))
                    .cloned()
                    .collect(),
            ),
            (true, false) => o.meet(self),
            (true, true) => Ints::new(true, self.vals.union(&o.vals).cloned().collect()),
        }
    }

    /// `self \ o`.
    pub(super) fn minus(&self, o: &Ints) -> Ints {
        match (self.cof, o.cof) {
            (false, _) => Ints::new(
                false,
                self.vals
                    .iter()
                    .filter(|x| o.cof == o.vals.contains(x))
                    .cloned()
                    .collect(),
            ),
            (true, false) => Ints::new(true, self.vals.union(&o.vals).cloned().collect()),
            (true, true) => Ints::new(false, o.vals.difference(&self.vals).cloned().collect()),
        }
    }

    /// One value of a set that is not empty: its least value, or the least natural number
    /// not excluded.
    pub(super) fn pick(&self) -> Value {
        if !self.cof {
            return self.vals.iter().next().expect("not empty").clone();
        }
        (0..)
            .map(Value::Int)
            .find(|x| !self.vals.contains(x))
            .expect("a cofinite set has a natural number")
    }

    pub(in super::super) fn contains(&self, v: &Value) -> bool {
        self.cof != self.vals.contains(v)
    }

    pub(super) fn pick_in(&self, dom: &Ints) -> Value {
        if !self.cof {
            return self.vals.iter().next().expect("not empty").clone();
        }
        (0..)
            .map(Value::Int)
            .find(|x| !self.vals.contains(x) && dom.contains(x))
            .expect("an intersection of two cofinite sets has a natural number")
    }

    /// Intersects a non-empty slice of `Ints` in `O(S log S)` time where
    /// `S = \sum_r (1 + |s_r.vals|)`.
    // Complexity tradeoff: folding `Ints::meet` left-to-right across `k` cofinite partners in one
    // `U1` bucket (`\bigcap_{q=1}^k (\mathbb{Z} \setminus \{q\})`) clones an excluded set of size
    // `q` at step `q`, costing `Theta(k^2)` (`xr_r2_bench_escape_single_bucket_scales_n_log_n`).
    // Cloning the smallest finite set once (or, when all sets are cofinite, the largest excluded
    // set once) and mutating that single `BTreeSet` in place costs `O(S log S)`.
    pub(super) fn intersect_many(sets: &[&Ints]) -> Ints {
        debug_assert!(!sets.is_empty());
        // No shortcut for one set: both callers pass two or more (U1 merges a group of two
        // clauses or more, U2 a place's set and one unit at least), and the two branches below
        // give the set itself for one set (TEST-kernel-unreached-paths-4, kernel12).
        if let Some((min_idx, min_fin)) = sets
            .iter()
            .enumerate()
            .filter(|(_, s)| !s.cof)
            .min_by_key(|(_, s)| s.vals.len())
        {
            let mut vals: BTreeSet<Value> = (*min_fin.vals).clone();
            for (idx, s) in sets.iter().enumerate() {
                if idx == min_idx || vals.is_empty() {
                    continue;
                }
                if s.cof {
                    for v in s.vals.iter() {
                        vals.remove(v);
                    }
                } else {
                    vals.retain(|x| s.vals.contains(x));
                }
            }
            Ints::new(false, vals)
        } else {
            let (max_idx, max_cof) = sets
                .iter()
                .enumerate()
                .max_by_key(|(_, s)| s.vals.len())
                .expect("non-empty cofinite slice");
            let mut vals = (*max_cof.vals).clone();
            for (idx, s) in sets.iter().enumerate() {
                if idx != max_idx {
                    for v in s.vals.iter() {
                        vals.insert(v.clone());
                    }
                }
            }
            Ints::new(true, vals)
        }
    }
}

/// Whether `p` holds integers only (or nothing).
pub(super) fn only_ints(p: &Parts) -> bool {
    p.bools == 0
        && [&p.rats, &p.floats, &p.f32s, &p.strings]
            .iter()
            .all(|l: &&Lits| !l.cofinite && l.values.is_empty())
        && !p.structs
        && p.morphisms.is_leaf() == Some(false)
        && p.tuples.is_default()
        && !p.atoms.cofinite()
        && p.atoms
            .names()
            .values()
            .all(|a| !a.bare && a.payload == Type::empty())
}

/// The finite set of `vals`, for tests.
#[cfg(test)]
pub(super) fn finite(vals: impl IntoIterator<Item = Value>) -> Ints {
    Ints::new(false, vals.into_iter().collect())
}

/// The integers less `vals`, for tests.
#[cfg(test)]
pub(super) fn cofinite(vals: impl IntoIterator<Item = Value>) -> Ints {
    Ints::new(true, vals.into_iter().collect())
}
