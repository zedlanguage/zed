//! The linear relation of a scope (step L1.39) as a persistent set of conjuncts, with the
//! conjuncts that mention each name and, of the constraints on each term, the tighter one.
//!
//! A scope is copied for each case of a test and the cases are joined, so the relation is held
//! in persistent maps: a copy costs O(1), a new conjunct O(log n) in the size of the relation,
//! and two relations made from one by a few changes are compared, and their differing
//! conjuncts found, in time near the number of changes. The conjuncts are in the order of
//! formulas, so a relation does not depend on the order its conjuncts were added in.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use imbl::{OrdMap, OrdSet};

use super::int::Int;
use super::presburger::{Atom, Con, Formula, Rel};

/// The values of a set kept for each name, in a persistent map.
#[derive(Clone, PartialEq, Debug)]
pub struct Uses<T: Ord + Clone>(OrdMap<Arc<str>, OrdSet<T>>);

impl<T: Ord + Clone> Default for Uses<T> {
    fn default() -> Self {
        Uses(OrdMap::new())
    }
}

impl<T: Ord + Clone> Uses<T> {
    /// Records that `name` is used by `t`.
    pub fn add(&mut self, name: &Arc<str>, t: &T) {
        self.0.entry(name.clone()).or_default().insert(t.clone());
    }

    /// Forgets that `name` is used by `t`.
    pub fn remove(&mut self, name: &Arc<str>, t: &T) {
        if let Some(s) = self.0.get_mut(name) {
            s.remove(t);
            if s.is_empty() {
                self.0.remove(name);
            }
        }
    }

    /// The values that use `name`.
    pub fn of(&self, name: &str) -> impl Iterator<Item = &T> {
        self.0.get(name).into_iter().flatten()
    }

    /// The names that are used.
    pub fn names(&self) -> impl Iterator<Item = &Arc<str>> {
        self.0.keys()
    }
}

/// The key of a constraint for the rule that keeps the tighter of two: its term and relation.
type Tight = (BTreeMap<Atom, Int>, Rel);

/// A conjunction of formulas, `true` when empty.
#[derive(Clone, Debug, Default)]
pub struct Conjuncts {
    /// The conjuncts. `false` is the set of `false` alone.
    set: OrdSet<Arc<Formula>>,
    /// Of the constraints on each term with each relation, the one kept.
    tight: OrdMap<Tight, Arc<Formula>>,
    /// The conjuncts that mention each name, alone or in a product.
    users: Uses<Arc<Formula>>,
}

impl PartialEq for Conjuncts {
    fn eq(&self, other: &Conjuncts) -> bool {
        self.set == other.set
    }
}

/// The names `f` mentions, alone or in a product.
pub fn names(f: &Formula) -> BTreeSet<Arc<str>> {
    let mut out = BTreeSet::new();
    for a in f.atoms() {
        match a {
            Atom::Sym(n) => {
                out.insert(n);
            }
            Atom::Product(x, y) => {
                out.insert(x);
                out.insert(y);
            }
            Atom::Aux(_) => {}
        }
    }
    out
}

impl Conjuncts {
    /// Whether the conjunction is `true`.
    pub fn is_top(&self) -> bool {
        self.set.is_empty()
    }

    /// The conjuncts, in the order of formulas.
    pub fn set(&self) -> &OrdSet<Arc<Formula>> {
        &self.set
    }

    /// The conjuncts that mention `name`.
    pub fn mentioning(&self, name: &str) -> impl Iterator<Item = &Arc<Formula>> {
        self.users.of(name)
    }

    /// The names some conjunct mentions.
    pub fn names(&self) -> impl Iterator<Item = &Arc<str>> {
        self.users.names()
    }

    /// The conjunction as one formula, as [`Formula::and`] gives it.
    pub fn formula(&self) -> Formula {
        let mut gs: Vec<Formula> = self.set.iter().map(|g| (**g).clone()).collect();
        if gs.len() == 1 {
            gs.pop().expect("one")
        } else {
            Formula::And(gs)
        }
    }

    /// Each constraint, conjunct by conjunct.
    pub fn cons(&self) -> Vec<&Con> {
        self.set.iter().flat_map(|g| g.cons()).collect()
    }

    /// The conjunction with `f`: a conjunction's parts are added each, `true` is dropped and
    /// `false` absorbs, and of two constraints on one term with one relation the tighter
    /// alone is kept, as [`Formula::and`] does.
    pub fn and(&mut self, f: Formula) {
        match f {
            Formula::And(gs) => gs.into_iter().for_each(|g| self.and_one(g)),
            g => self.and_one(g),
        }
    }

    fn and_one(&mut self, g: Formula) {
        if self.set.iter().next().is_some_and(|f| is_false(f)) {
            return;
        }
        match &g {
            Formula::Or(gs) if gs.is_empty() => {
                *self = Conjuncts::default();
                self.set.insert(Arc::new(g));
                return;
            }
            Formula::And(_) => return self.and(g),
            Formula::Con(c) => {
                let key = (c.lin.terms.clone(), c.rel);
                if let Some(old) = self.tight.get(&key) {
                    let Formula::Con(o) = &**old else {
                        unreachable!("a constraint")
                    };
                    if c.rel == Rel::Ge && c.lin.constant < o.lin.constant {
                        let old = old.clone();
                        self.remove(&old);
                    } else if c.rel == Rel::Eq && c.lin.constant != o.lin.constant {
                        self.and_one(Formula::bottom());
                        return;
                    } else {
                        return;
                    }
                }
            }
            _ => {}
        }
        let g = Arc::new(g);
        if self.set.contains(&g) {
            return;
        }
        for n in names(&g) {
            self.users.add(&n, &g);
        }
        if let Formula::Con(c) = &*g {
            self.tight.insert((c.lin.terms.clone(), c.rel), g.clone());
        }
        self.set.insert(g);
    }

    /// Removes the conjunct `g`.
    pub fn remove(&mut self, g: &Arc<Formula>) {
        if self.set.remove(g).is_none() {
            return;
        }
        for n in names(g) {
            self.users.remove(&n, g);
        }
        if let Formula::Con(c) = &**g {
            let key = (c.lin.terms.clone(), c.rel);
            if self.tight.get(&key) == Some(g) {
                self.tight.remove(&key);
            }
        }
    }

    /// The conjunction with every conjunct that mentions `name` replaced by
    /// [`Formula::forget`] of it, which says nothing of `name`: in time near the conjuncts
    /// that mention it.
    pub fn forget(&mut self, name: &Arc<str>) {
        let gs: Vec<Arc<Formula>> = self.mentioning(name).cloned().collect();
        for g in &gs {
            self.remove(g);
        }
        for g in gs {
            self.and(g.forget(name));
        }
    }
}

/// The conjuncts of `rels` linked to `seeds` by chains of conjuncts that share a name, only
/// conjuncts `follow` keeps taken, and the names they mention with the seeds: a search from
/// the seeds with a visited set, in time near the conjuncts found.
pub fn reach(
    rels: &[&Conjuncts],
    seeds: impl IntoIterator<Item = Arc<str>>,
    follow: impl Fn(&Formula) -> bool,
) -> (BTreeSet<Arc<Formula>>, BTreeSet<Arc<str>>) {
    let mut found: BTreeSet<Arc<Formula>> = BTreeSet::new();
    let mut seen: BTreeSet<Arc<str>> = BTreeSet::new();
    let mut work: Vec<Arc<str>> = Vec::new();
    for n in seeds {
        if seen.insert(n.clone()) {
            work.push(n);
        }
    }
    while let Some(n) = work.pop() {
        for g in rels.iter().flat_map(|r| r.users.of(&n)) {
            if !follow(g) || found.contains(g) {
                continue;
            }
            found.insert(g.clone());
            for m in names(g) {
                if seen.insert(m.clone()) {
                    work.push(m);
                }
            }
        }
    }
    (found, seen)
}

/// Whether `f` is `false`.
fn is_false(f: &Formula) -> bool {
    matches!(f, Formula::Or(gs) if gs.is_empty())
}

impl fmt::Display for Conjuncts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.formula())
    }
}
