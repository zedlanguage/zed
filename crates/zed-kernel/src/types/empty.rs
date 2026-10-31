//! Emptiness and subtyping (step L1.23, DESIGN.md sec:type_language): `a <: b` iff `a & !b`
//! is empty, decided by a memoized coinductive check.
//!
//! A type is empty when every part is. The scalar and struct parts are exact, so their
//! emptiness is read off. A tuple clause is empty when the meet of its positive tuple types is
//! covered by its negated ones, which is decided by splitting the meet into disjoint pieces
//! outside each negated type in turn, passing over a negated type disjoint from the piece. A
//! morphism clause is empty when its positive types admit no morphism,
//! or one negated type contains every morphism they admit, which the variance law decides:
//! contravariant in the guarantee, covariant in the permission and the value type. A union of
//! negated morphism types is taken one type at a time, so a clause whose positive part is
//! covered by several negated types together, and by none alone, counts as inhabited: the
//! check is sound but not complete there.
//!
//! A tuple or morphism part kept as an expression (module `bdd`) is decided by its paths, as a
//! diagram is. Apart from the union of negated morphism types above, `is_empty` is exact: no
//! count of nodes, paths or splits stops it. Emptiness of Boolean combinations of tuple types
//! is coNP-hard, so its time can be exponential in the tuple types written; its memory is one
//! path and one split at a time.
//!
//! The check is coinductive: a type met again while its own emptiness is being decided is
//! assumed empty. Values are finite, so a type whose every value would contain a smaller value
//! of the same type is empty, which is the answer the assumption gives; contractive, regular
//! and monotone definitions (module `rec`) make the set of types met finite. A result that
//! rests on an assumption later found false is dropped. Results are kept for the thread.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use super::{Morphism, Parts, Type};

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

/// One query's state: the types being decided, assumed empty, and those decided; and the
/// types decided empty, in the order they were decided.
#[derive(Default)]
struct Search {
    busy: BTreeSet<Type>,
    done: BTreeMap<Type, bool>,
    empties: Vec<Type>,
}

impl Search {
    fn empty(&mut self, t: &Type) -> bool {
        if let Some(b) = MEMO.with(|m| m.borrow().get(t).copied()) {
            return b;
        }
        if let Some(b) = self.done.get(t) {
            return *b;
        }
        if self.busy.contains(t) {
            return true;
        }
        self.busy.insert(t.clone());
        let mark = self.empties.len();
        let b = self.parts(t.p());
        self.busy.remove(t);
        if b {
            self.empties.push(t.clone());
        } else {
            // Every emptiness decided since `t` was assumed empty may rest on that.
            for e in self.empties.drain(mark..) {
                self.done.remove(&e);
            }
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
                .all(|(len, b)| b.paths(&mut |pos, neg| self.tuples(*len, pos, neg)))
            && p.morphisms.paths(&mut |pos, neg| self.morphisms(pos, neg))
    }

    /// The tuples of length `len` in every type of `pos` and in none of `neg`.
    fn tuples(&mut self, len: usize, pos: &[&Vec<Type>], neg: &[&Vec<Type>]) -> bool {
        let meet = pos.iter().fold(vec![Type::top(); len], |m, p| {
            m.iter().zip(p.iter()).map(|(a, b)| a & b).collect()
        });
        self.product(meet, neg)
    }

    /// Whether the tuples with components in `p` are all in some type of `neg`. A negated
    /// type disjoint from `p` in some component is passed over. Outside a negated type means
    /// outside it first in component `j`, so the pieces are disjoint: the components before `j`
    /// inside it, component `j` outside it, and the rest as in `p`.
    fn product(&mut self, p: Vec<Type>, neg: &[&Vec<Type>]) -> bool {
        if p.iter().any(|t| self.empty(t)) {
            return true;
        }
        let mut rest = neg;
        let n = loop {
            let Some((n, r)) = rest.split_first() else {
                return false;
            };
            rest = r;
            if !p.iter().zip(n.iter()).any(|(a, b)| self.empty(&(a & b))) {
                break n;
            }
        };
        (0..p.len()).all(|j| {
            let mut q = p.clone();
            for i in 0..j {
                q[i] = &p[i] & &n[i];
            }
            q[j] = &p[j] - &n[j];
            self.product(q, rest)
        })
    }

    fn morphisms(&mut self, pos: &[&Morphism], neg: &[&Morphism]) -> bool {
        let meet = pos.iter().fold(
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
        neg.iter().any(|n| {
            self.empty(&(&n.guarantee - l))
                && (no_value || self.empty(&(u - &n.permission)))
                && (no_value || self.empty(u) || self.empty(&(v - &n.value)))
        })
    }
}
