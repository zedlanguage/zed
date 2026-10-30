//! Emptiness and subtyping (step L1.23, DESIGN.md sec:type_language): `a <: b` iff `a & !b`
//! is empty, decided by a memoized coinductive check.
//!
//! A type is empty when every part is. The scalar and struct parts are exact, so their
//! emptiness is read off. A tuple clause is empty when the meet of its positive tuple types is
//! covered by its negated ones, which is decided by splitting the meet on each negated type's
//! components in turn. A morphism clause is empty when its positive types admit no morphism,
//! or one negated type contains every morphism they admit, which the variance law decides:
//! contravariant in the guarantee, covariant in the permission and the value type. A union of
//! negated morphism types is taken one type at a time, so a clause whose positive part is
//! covered by several negated types together, and by none alone, counts as inhabited: the
//! check is sound but not complete there.
//!
//! The check is coinductive: a type met again while its own emptiness is being decided is
//! assumed empty. Values are finite, so a type whose every value would contain a smaller value
//! of the same type is empty, which is the answer the assumption gives; contractive, regular
//! and monotone definitions (module `rec`) make the set of types met finite. A result that
//! rests on an assumption later found false is dropped. Results are kept for the thread.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use super::{Clause, Morphism, Parts, Type};

thread_local! {
    static MEMO: RefCell<BTreeMap<Type, bool>> = const { RefCell::new(BTreeMap::new()) };
}

impl Type {
    /// Whether no value is in `self`.
    pub fn is_empty(&self) -> bool {
        if let Some(b) = MEMO.with(|m| m.borrow().get(self).copied()) {
            return b;
        }
        let mut s = Search::default();
        let b = s.empty(self);
        MEMO.with(|m| {
            let mut m = m.borrow_mut();
            m.extend(s.done.into_iter().map(|(t, (b, _))| (t, b)));
        });
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

/// One query's state: the types being decided, assumed empty, and those decided, each with
/// the order it was decided in.
#[derive(Default)]
struct Search {
    busy: BTreeSet<Type>,
    done: BTreeMap<Type, (bool, usize)>,
    count: usize,
}

impl Search {
    fn empty(&mut self, t: &Type) -> bool {
        if let Some(b) = MEMO.with(|m| m.borrow().get(t).copied()) {
            return b;
        }
        if let Some((b, _)) = self.done.get(t) {
            return *b;
        }
        if self.busy.contains(t) {
            return true;
        }
        self.busy.insert(t.clone());
        let mark = self.count;
        let b = self.parts(t.p());
        self.busy.remove(t);
        if !b {
            // Every emptiness decided since `t` was assumed empty may rest on that.
            self.done.retain(|_, (e, at)| !*e || *at < mark);
        }
        self.done.insert(t.clone(), (b, self.count));
        self.count += 1;
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
            && p.tuples.0.iter().all(|c| self.tuples(c))
            && p.morphisms.0.iter().all(|c| self.morphisms(c))
    }

    /// A clause with no positive tuple type holds every tuple of a length no negated type has.
    fn tuples(&mut self, c: &Clause<Vec<Type>>) -> bool {
        let mut pos = c.pos.iter();
        let Some(first) = pos.next() else {
            return false;
        };
        let meet = pos.fold(first.clone(), |m, p| {
            m.iter().zip(p).map(|(a, b)| a & b).collect()
        });
        let neg: Vec<&Vec<Type>> = c.neg.iter().collect();
        self.product(meet, &neg)
    }

    /// Whether the tuples with components in `p` are all in some type of `neg`. Outside the
    /// first negated type means outside it in some component.
    fn product(&mut self, p: Vec<Type>, neg: &[&Vec<Type>]) -> bool {
        if p.iter().any(|t| self.empty(t)) {
            return true;
        }
        let Some((n, rest)) = neg.split_first() else {
            return false;
        };
        (0..p.len()).all(|j| {
            let mut q = p.clone();
            q[j] = &p[j] - &n[j];
            self.product(q, rest)
        })
    }

    fn morphisms(&mut self, c: &Clause<Morphism>) -> bool {
        let meet = c.pos.iter().fold(
            Morphism {
                guarantee: Type::empty(),
                permission: Type::top(),
                value: Type::top(),
            },
            |m, p| Morphism {
                guarantee: &m.guarantee | &p.guarantee,
                permission: &m.permission & &p.permission,
                value: &m.value & &p.value,
            },
        );
        let Morphism {
            guarantee: l,
            permission: u,
            value: v,
        } = &meet;
        // No domain lies between the bounds, or a key is promised and no value can be its.
        if !self.empty(&(l - u)) || (!self.empty(l) && self.empty(v)) {
            return true;
        }
        // With no value, the empty morphism is the only one, and its domain is the guarantee.
        let no_value = self.empty(v);
        c.neg.iter().any(|n| {
            self.empty(&(&n.guarantee - l))
                && (no_value || self.empty(&(u - &n.permission)))
                && (no_value || self.empty(u) || self.empty(&(v - &n.value)))
        })
    }
}
