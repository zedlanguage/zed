//! Emptiness and subtyping (step L1.23, DESIGN.md sec:type_language): `a <: b` iff `a & !b`
//! is empty, decided by a memoized coinductive check.
//!
//! A type is empty when every part is. The scalar and struct parts are exact, so their
//! emptiness is read off. The tuple part of each length, a Boolean combination of tuple types
//! (module `bdd`), is decided on a box, one type per component, starting from the whole
//! product: each tuple type is known to hold the box, known to miss it, or open on it; the
//! part is evaluated in three-valued logic on what is known; a tuple type in every value of
//! the part narrows the box to it, and one in no value takes itself out of the one component
//! where it does not hold the box. When narrowing stops, a component whose pieces cut by the
//! open tuple types are pairwise equal or disjoint is split into those pieces, and each piece
//! decided; otherwise each piece on which narrowing alone proves the part empty is taken out
//! of the box; otherwise, once on each branch, when the part holds nothing outside the open
//! tuple types, the box is split into its meet with each of them. A box none of these steps
//! settles counts as inhabited. The morphism part is decided the same way, by the variance
//! law: contravariant in the guarantee, covariant in the permission and the value type.
//!
//! So `is_empty` is sound, never empty for an inhabited type, and its time is polynomial in
//! the types written; it is not complete, since emptiness of Boolean combinations of tuple
//! types is coNP-hard. A part that only a split of the box in more than one component at once
//! proves empty counts as inhabited: a subtyping check then fails, and the error names the
//! types, so the program states the case split itself (DESIGN.md L1.23).
//!
//! The check is coinductive: a type met again while its own emptiness is being decided is
//! assumed empty. Values are finite, so a type whose every value would contain a smaller value
//! of the same type is empty, which is the answer the assumption gives; contractive, regular
//! and monotone definitions (module `rec`) make the set of types met finite. A result, empty
//! or inhabited, that rests on an assumption later found false is dropped, and only such a
//! result, so no result is decided again unless an assumption it read changed: a tuple type
//! wrongly assumed disjoint from the box leaves a clause, so a wrong assumption can make a
//! type count as inhabited too. Results are kept for the thread, until
//! `Type::forget_emptiness`.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use super::bdd::Part;
use super::{Morphism, Parts, Row, Type};

thread_local! {
    static MEMO: RefCell<BTreeMap<Type, bool>> = const { RefCell::new(BTreeMap::new()) };
}

impl Type {
    /// Drops the kept emptiness results. A unit's checker calls it first: a type equal to a
    /// kept one but built apart from it is compared with it in full, so a result kept from
    /// another unit costs the size of the type at each lookup.
    pub fn forget_emptiness() {
        MEMO.with(|m| m.borrow_mut().clear());
    }

    /// Whether no value is in `self`.
    pub fn is_empty(&self) -> bool {
        if let Some(b) = MEMO.with(|m| m.borrow().get(self).copied()) {
            return b;
        }
        let mut s = Search::default();
        let b = s.empty(self);
        MEMO.with(|m| m.borrow_mut().extend(s.done));
        b
    }

    /// Whether every value of `self` is in `other`: `self <: other`.
    pub fn subtype(&self, other: &Type) -> bool {
        (self - other).is_empty()
    }

    /// Whether `self` and `other` denote one set of values.
    pub fn equiv(&self, other: &Type) -> bool {
        self.subtype(other) && other.subtype(self)
    }
}

/// One query's state: the types being decided, assumed empty, each with its depth among them;
/// those decided; the types decided on assumptions still being made, in the order they were
/// decided, each with the depths of those assumptions; and the depths of the assumptions the
/// current decision has used.
#[derive(Default)]
struct Search {
    busy: BTreeMap<Type, usize>,
    done: BTreeMap<Type, bool>,
    pending: Vec<Type>,
    rests: BTreeMap<Type, BTreeSet<usize>>,
    reads: BTreeSet<usize>,
}

impl Search {
    fn empty(&mut self, t: &Type) -> bool {
        if let Some(b) = MEMO.with(|m| m.borrow().get(t).copied()) {
            return b;
        }
        if let Some(b) = self.done.get(t) {
            if let Some(r) = self.rests.get(t) {
                self.reads.extend(r);
            }
            return *b;
        }
        if let Some(d) = self.busy.get(t) {
            self.reads.insert(*d);
            return true;
        }
        let depth = self.busy.len();
        self.busy.insert(t.clone(), depth);
        let mark = self.pending.len();
        let outer = std::mem::take(&mut self.reads);
        let b = self.parts(t.p());
        let mut rests = std::mem::replace(&mut self.reads, outer);
        rests.remove(&depth);
        self.busy.remove(t);
        // Only results decided since `t` was assumed empty can rest on that. A wrong
        // assumption can make a result wrong either way: an assumed disjointness drops a tuple
        // type from a clause, which can leave the clause inhabited. So when `t` is inhabited,
        // each result that rests on it is dropped; when it is empty, each rests instead on
        // what `t` rests on, and is confirmed when that is nothing.
        let since: Vec<Type> = self.pending.drain(mark..).collect();
        for e in since {
            let r = self.rests.get_mut(&e).expect("a pending result has its assumptions");
            if r.remove(&depth) {
                if !b {
                    self.done.remove(&e);
                    self.rests.remove(&e);
                    continue;
                }
                r.extend(&rests);
            }
            if r.is_empty() {
                self.rests.remove(&e);
            } else {
                self.pending.push(e);
            }
        }
        if !rests.is_empty() {
            self.reads.extend(&rests);
            self.pending.push(t.clone());
            self.rests.insert(t.clone(), rests);
        }
        self.done.insert(t.clone(), b);
        b
    }

    fn parts(&mut self, p: &Parts) -> bool {
        let lits = [&p.ints, &p.rats, &p.floats, &p.strings];
        p.bools == 0
            && lits.iter().all(|l| !l.cofinite && l.values.is_empty())
            && !p.atoms.cofinite
            && p.atoms
                .names
                .values()
                .all(|a| !a.bare && self.empty(&a.payload))
            && !p.structs
            && !p.tuples.rest
            && p.tuples
                .lens
                .iter()
                .all(|(len, b)| self.tuples(vec![Type::top(); *len], b.clone(), true))
            && self.morphisms(
                Morphism {
                    guarantee: Type::empty(),
                    permission: Type::top(),
                    value: Type::top(),
                },
                p.morphisms.clone(),
                true,
            )
    }

    /// Where each tuple type of `f` stands on the box `r`: `Some(false)` if they are disjoint,
    /// `Some(true)` if it holds the box, `None` if it is open on it.
    fn tuple_atoms(&mut self, r: &[Type], f: &Part<Row>) -> BTreeMap<Row, Option<bool>> {
        let mut atoms = Vec::new();
        f.atoms(&mut |a| {
            atoms.push(a.clone());
            true
        });
        atoms
            .into_iter()
            .map(|a| {
                let s = if r.iter().zip(&a).any(|(x, y)| self.empty(&(x & y))) {
                    Some(false)
                } else if r.iter().zip(&a).all(|(x, y)| self.empty(&(x - y))) {
                    Some(true)
                } else {
                    None
                };
                (a, s)
            })
            .collect()
    }

    /// Narrows the box `r` and the part `f` to what `f` forces on it: a tuple type in every
    /// value of `f` meets `r`, and a tuple type in none is taken out of `r` when it holds `r`
    /// in every component but one. True when `f` is proved empty on `r`.
    fn narrow_tuples(&mut self, r: &mut [Type], f: &mut Part<Row>) -> bool {
        loop {
            if r.iter().any(|t| self.empty(t)) {
                return true;
            }
            let st = self.tuple_atoms(r, f);
            *f = f.restrict(&|a| st.get(a).copied().flatten()).settle();
            match f.is_leaf() {
                Some(b) => return !b,
                None => {}
            }
            let (taken, refused) = f.forced();
            let mut changed = !taken.is_empty();
            for a in &taken {
                for (x, y) in r.iter_mut().zip(a) {
                    *x = &*x & y;
                }
            }
            for a in &refused {
                let open: Vec<usize> = (0..r.len())
                    .filter(|&j| !self.empty(&(&r[j] - &a[j])))
                    .collect();
                if let [j] = open[..] {
                    r[j] = &r[j] - &a[j];
                    changed = true;
                }
            }
            if !changed {
                return false;
            }
        }
    }

    /// Whether no tuple in the box `r` is in `f`: `f` is narrowed by what it forces; then a
    /// component whose pieces cut by the open tuple types are pairwise equal or disjoint is
    /// split into them; else each such piece on which narrowing alone proves `f` empty is
    /// taken out; else, once on each branch, when `f` holds nothing outside the open tuple
    /// types, each of them is decided on its own. What is left counts as inhabited. A split
    /// into disjoint pieces sends each open tuple type to one piece, and a component split is
    /// never split again below, so the nodes are polynomial in the tuple types.
    fn tuples(&mut self, mut r: Vec<Type>, mut f: Part<Row>, may_cover: bool) -> bool {
        loop {
            if self.narrow_tuples(&mut r, &mut f) {
                return true;
            }
            if f.is_leaf().is_some() {
                return false;
            }
            let mut open = Vec::new();
            f.atoms(&mut |a| {
                open.push(a.clone());
                true
            });
            for j in 0..r.len() {
                let mut cells: Vec<Type> = Vec::new();
                let mut union = Type::empty();
                let ok = open.iter().all(|a| {
                    let c = &a[j] & &r[j];
                    if self.empty(&(&r[j] - &c)) {
                        return false;
                    }
                    if cells.contains(&c) {
                        return true;
                    }
                    if !self.empty(&(&c & &union)) {
                        return false;
                    }
                    union = &union | &c;
                    cells.push(c);
                    true
                });
                if !ok {
                    continue;
                }
                let rest = &r[j] - &union;
                if !self.empty(&rest) {
                    cells.push(rest);
                }
                return cells.into_iter().all(|c| {
                    let mut q = r.clone();
                    q[j] = c;
                    self.tuples(q, f.clone(), may_cover)
                });
            }
            let mut narrowed = false;
            for j in 0..r.len() {
                let mut tried: Vec<Type> = Vec::new();
                for a in &open {
                    for c in [&a[j] & &r[j], &r[j] - &a[j]] {
                        if tried.contains(&c) || self.empty(&c) || self.empty(&(&r[j] - &c)) {
                            continue;
                        }
                        tried.push(c.clone());
                        let mut q = r.clone();
                        q[j] = c.clone();
                        if self.narrow_tuples(&mut q, &mut f.clone()) {
                            r[j] = &r[j] - &c;
                            narrowed = true;
                        }
                    }
                }
            }
            if narrowed {
                continue;
            }
            if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                return open.iter().all(|a| {
                    let q = r.iter().zip(a).map(|(x, y)| x & y).collect();
                    self.tuples(q, f.clone(), false)
                });
            }
            return false;
        }
    }

    /// Whether `m` admits no morphism: no domain lies between the bounds, or a key is promised
    /// and no value can be its.
    fn no_morphism(&mut self, m: &Morphism) -> bool {
        !self.empty(&(&m.guarantee - &m.permission))
            || (!self.empty(&m.guarantee) && self.empty(&m.value))
    }

    /// Whether every morphism `m` admits is in `n`, by the variance law. With no value, the
    /// empty morphism is the only one, and its domain is the guarantee.
    fn within(&mut self, m: &Morphism, n: &Morphism) -> bool {
        let no_value = self.empty(&m.value);
        self.empty(&(&n.guarantee - &m.guarantee))
            && (no_value || self.empty(&(&m.permission - &n.permission)))
            && (no_value || self.empty(&m.permission) || self.empty(&(&m.value - &n.value)))
    }

    /// Whether no morphism `r` admits is in `f`, decided as for tuples: `r` meets the morphism
    /// types in every value of `f`, and, once on each branch, when `f` holds nothing outside
    /// the open morphism types, each is decided on its own. Morphism types are closed under
    /// meet but not under difference, so a type in no value of `f` narrows nothing.
    fn morphisms(&mut self, mut r: Morphism, mut f: Part<Morphism>, may_cover: bool) -> bool {
        loop {
            if self.no_morphism(&r) {
                return true;
            }
            let mut atoms = Vec::new();
            f.atoms(&mut |a| {
                atoms.push(a.clone());
                true
            });
            let st: BTreeMap<Morphism, Option<bool>> = atoms
                .into_iter()
                .map(|a| {
                    let s = if self.no_morphism(&meet(&r, &a)) {
                        Some(false)
                    } else if self.within(&r, &a) {
                        Some(true)
                    } else {
                        None
                    };
                    (a, s)
                })
                .collect();
            f = f.restrict(&|a| st.get(a).copied().flatten()).settle();
            if let Some(b) = f.is_leaf() {
                return !b;
            }
            let (taken, _) = f.forced();
            if !taken.is_empty() {
                r = taken.iter().fold(r, |r, a| meet(&r, a));
                continue;
            }
            if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                let mut open = Vec::new();
                f.atoms(&mut |a| {
                    open.push(a.clone());
                    true
                });
                return open
                    .iter()
                    .all(|a| self.morphisms(meet(&r, a), f.clone(), false));
            }
            return false;
        }
    }
}

/// The morphisms both `a` and `b` admit.
fn meet(a: &Morphism, b: &Morphism) -> Morphism {
    Morphism {
        guarantee: &a.guarantee | &b.guarantee,
        permission: &a.permission & &b.permission,
        value: &a.value & &b.value,
    }
}
