//! The reduced product (DESIGN.md sec:domains and sec:constraints; step L1.39).
//!
//! A name in scope holds a [`Product`]: the cell of step L1.24, the name's type and its
//! binding time. A [`Scope`] holds one product per name, the linear relation among them
//! (step L1.38) and the written constraints, each a kernel term that holds in the scope.
//! [`Scope::reduce`] passes information between the domains until nothing changes:
//!
//! - the interval and the congruence narrow each other, and a single value fixes both;
//! - the projection of the linear relation onto a name meets its interval;
//! - a finite set and the interval narrow each other;
//! - the type loses `int` when the interval or the congruence is empty, keeps only the literals
//!   of a finite interval or a finite set, and gives its literals back to the finite set and
//!   the interval;
//! - enumeration: a name of type within `int` whose interval holds at most
//!   [`ENUMERATION_BUDGET`] members keeps only the members at which each written constraint on
//!   it holds, the constraint's other names static and each evaluation within
//!   [`ENUMERATION_FUEL`]. A constraint whose evaluation runs out of fuel removes nothing.
//!
//! A product is empty when its type is, and a scope with an empty product is bottom: the arm
//! it describes is unreachable. [`Scope::assume`] narrows a scope by a test and its outcome:
//! `!`, `&&` and `||` (an `if` with a boolean arm) are taken apart, a false `&&` and a true
//! `||` joining the scopes of their cases, and each atom narrows by the preimage of its
//! outcome, by its linear relation, by the congruence `x mod c == r`, and by an equality with
//! a literal, whose negation excludes the literal by complement where the element is exact
//! (types, intervals, finite sets). [`arms`] walks a body and gives the scope of each `if` arm.
//!
//! A binding time is [`Time::Build`] for a value known when the program is built and
//! [`Time::Run`] for one known only when it runs; a meet takes the earlier and a join the
//! later.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use zed_kernel::budgets::{ENUMERATION_BUDGET, ENUMERATION_FUEL};
use zed_kernel::provenance::{FactAddress, NodeAddress};
use zed_kernel::types::{Type, Universe};
use zed_kernel::{Evaluator, KernelError, Prim, Stack, Term, Value, World, on_stack};

use super::affine::Bounds;
use super::cell::{Cell, Entry, Premise, Premises};
use super::interval::{End, IntervalSet, PIECE_LIMIT};
use super::lattice::{Congruence, FINITE_SET_LIMIT, FiniteSet, Lattice};
use super::preimage::{Demand, Domains, preimage, relations};
use super::presburger::{self, Atom, Formula};
use super::revision::{self, Op, reduce_congruence};
use crate::stage;

/// The most rounds of [`Scope::reduce`]; each round that changes nothing ends it.
pub const REDUCTION_ROUNDS: usize = 16;

/// When a value is known.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Time {
    /// No value: the bottom.
    Never,
    /// When the program is built.
    Build,
    /// When the program runs: the top.
    Run,
}

impl Lattice for Time {
    fn bottom() -> Self {
        Time::Never
    }
    fn top() -> Self {
        Time::Run
    }
    fn join(&self, other: &Self) -> Self {
        *self.max(other)
    }
    fn meet(&self, other: &Self) -> Self {
        *self.min(other)
    }
    fn widen(&self, next: &Self) -> Self {
        self.join(next)
    }
}

impl fmt::Display for Time {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Time::Never => "never",
            Time::Build => "build",
            Time::Run => "run",
        })
    }
}

/// The base types whose part a widening of a type takes whole once it grows.
fn bases() -> [Type; 5] {
    [
        Type::bool(),
        Type::int(),
        Type::rat(),
        Type::f64(),
        Type::string(),
    ]
}

impl Lattice for Type {
    fn bottom() -> Self {
        Type::empty()
    }
    fn top() -> Self {
        Type::top()
    }
    fn join(&self, other: &Self) -> Self {
        self | other
    }
    fn meet(&self, other: &Self) -> Self {
        self & other
    }
    /// The join, and the whole of each base type, and of the rest of each universe, in which
    /// `next` has a value `self` has not. Each such part is taken at most once, so every
    /// chain of widenings is finite.
    fn widen(&self, next: &Self) -> Self {
        let mut out = self | next;
        let mut all_bases = Type::empty();
        for b in bases() {
            if !(next & &b).subtype(self) {
                out = &out | &b;
            }
            all_bases = &all_bases | &b;
        }
        for u in [
            Universe::Scalar,
            Universe::Tuple,
            Universe::Struct,
            Universe::Morphism,
        ] {
            let rest = Type::universe(u) - &all_bases;
            if !(next & &rest).subtype(self) {
                out = &out | &rest;
            }
        }
        out
    }
    fn leq(&self, other: &Self) -> bool {
        self.subtype(other)
    }
}

/// The element of the reduced product for one name.
#[derive(Clone, PartialEq, Debug)]
pub struct Product {
    /// The domains of step L1.24.
    pub cell: Cell,
    /// The type.
    pub ty: Entry<Type>,
    /// The binding time.
    pub time: Entry<Time>,
}

impl Product {
    /// No information: any value, known when the program runs.
    pub fn top() -> Product {
        Product {
            cell: Cell::top(),
            ty: Entry::new(Type::top()),
            time: Entry::new(Time::Run),
        }
    }

    /// No value.
    pub fn bottom() -> Product {
        let mut p = Product::top();
        p.cell.ints.element = Bounds::ints(IntervalSet::empty());
        p.cell.congruence.element = Congruence::Bottom;
        p.cell.finite.element = FiniteSet::Set(BTreeSet::new());
        p.ty.element = Type::empty();
        p.time.element = Time::Never;
        p
    }

    /// Any value of `ty`, known when the program runs.
    pub fn of_type(ty: Type) -> Product {
        let mut p = Product::top();
        p.ty.element = ty;
        p.reduce_domains();
        p
    }

    /// The value `v`, known when the program is built.
    pub fn literal(v: &Value) -> Product {
        Product {
            cell: Cell::literal(v),
            ty: Entry::new(Type::lit(v).unwrap_or_else(Type::top)),
            time: Entry::new(Time::Build),
        }
    }

    /// Whether no value has this element.
    pub fn is_empty(&self) -> bool {
        self.ty.element.is_empty()
    }

    /// The integers of the interval domain.
    pub fn ints(&self) -> &IntervalSet {
        self.cell.ints.element.concrete()
    }

    /// The one value, when the finite set holds exactly one.
    pub fn value(&self) -> Option<&Value> {
        match &self.cell.finite.element {
            FiniteSet::Set(s) if s.len() == 1 => s.iter().next(),
            _ => None,
        }
    }

    /// Whether `v` is a value of this element: of its type, in its finite set, and an integer
    /// in its interval and its congruence.
    pub fn contains(&self, v: &Value) -> bool {
        let ints = match v {
            Value::Int(n) => self.ints().contains(*n) && self.cell.congruence.element.contains(*n),
            _ => true,
        };
        let finite = match &self.cell.finite.element {
            FiniteSet::Top => true,
            FiniteSet::Set(s) => s.contains(v),
        };
        ints && finite && self.ty.element.contains(v)
    }

    /// The premises of every entry.
    pub fn premises(&self) -> Premises {
        let mut out = self.cell.premises();
        out.extend(&self.ty.premises);
        out.extend(&self.time.premises);
        out
    }

    /// Joins `other` into `self`; whether anything changed.
    pub fn join(&mut self, other: &Product) -> bool {
        [
            self.cell.join(&other.cell),
            self.ty.join(&other.ty),
            self.time.join(&other.time),
        ]
        .contains(&true)
    }

    /// Widens `self` by `other` at the component head `head`; whether anything changed.
    pub fn widen(&mut self, other: &Product, head: &FactAddress) -> bool {
        [
            self.cell.widen(&other.cell, head),
            self.ty.widen(&other.ty, head),
            self.time.widen(&other.time, head),
        ]
        .contains(&true)
    }

    /// Meets the interval domain with `x`.
    fn meet_ints(&mut self, x: &IntervalSet, premises: &Premises) {
        self.cell.ints.meet(&Bounds::ints(x.clone()), premises);
    }

    /// The reductions between this product's own domains, once each.
    fn reduce_domains(&mut self) {
        let prem = self.premises();
        let int = Type::int();
        let (x, c) = reduce_congruence(self.ints(), &self.cell.congruence.element);
        self.meet_ints(&x, &prem);
        self.cell.congruence.meet(&c, &prem);
        // A finite set against the interval: an integer member outside it goes.
        if let FiniteSet::Set(vs) = &self.cell.finite.element {
            let x = self.ints().clone();
            let kept: BTreeSet<Value> = vs
                .iter()
                .filter(|v| !matches!(v, Value::Int(n) if !x.contains(*n)))
                .cloned()
                .collect();
            if vs.iter().all(|v| matches!(v, Value::Int(_))) {
                let ints = IntervalSet::from_pieces(
                    kept.iter()
                        .filter_map(|v| match v {
                            Value::Int(n) => Some((End::Fin(*n), End::Fin(*n))),
                            _ => None,
                        })
                        .collect(),
                );
                self.meet_ints(&ints, &prem);
            }
            self.cell.finite.meet(&FiniteSet::Set(kept), &prem);
        }
        // The type from the other domains.
        if self.ints().is_empty() || self.cell.congruence.element == Congruence::Bottom {
            self.ty.meet(&!&int, &prem);
        } else if let Some(vs) = members(self.ints(), FINITE_SET_LIMIT as u64) {
            let lits = vs
                .iter()
                .filter_map(|&n| Type::lit(&Value::Int(n)))
                .fold(Type::empty(), |a, b| &a | &b);
            self.ty.meet(&(&!&int | &lits), &prem);
        }
        if let FiniteSet::Set(vs) = &self.cell.finite.element {
            let lits: Option<Vec<Type>> = vs.iter().map(Type::lit).collect();
            if let Some(lits) = lits {
                let t = lits.iter().fold(Type::empty(), |a, b| &a | b);
                self.ty.meet(&t, &prem);
            }
        }
        // The other domains from the type.
        if let Some(vs) = self.ty.element.values(FINITE_SET_LIMIT) {
            self.cell.finite.meet(&FiniteSet::of(vs), &prem);
        }
        if let Some(vs) = (&self.ty.element & &int).values(FINITE_SET_LIMIT)
            && !vs.is_empty()
            && self.ty.element.subtype(&int)
        {
            let ints = IntervalSet::from_pieces(
                vs.iter()
                    .filter_map(|v| match v {
                        Value::Int(n) => Some((End::Fin(*n), End::Fin(*n))),
                        _ => None,
                    })
                    .collect(),
            );
            self.meet_ints(&ints, &prem);
        }
    }
}

impl fmt::Display for Product {
    /// The cell's lines, then the type and the binding time when they are not the top.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.cell)?;
        if self.ty.element != Type::top() {
            writeln!(f, "type {}", self.ty.element)?;
        }
        if self.time.element != Time::Run {
            writeln!(f, "time {}", self.time.element)?;
        }
        Ok(())
    }
}

/// Each member of `x` when it is finite with at most `cap` of them.
fn members(x: &IntervalSet, cap: u64) -> Option<Vec<i64>> {
    let (End::Fin(lo), End::Fin(hi)) = x.bounds()? else {
        return None;
    };
    if (hi as i128 - lo as i128) >= cap as i128 {
        return None;
    }
    Some((lo..=hi).filter(|&v| x.contains(v)).collect())
}

/// The names in scope with their products, the linear relation among them, and the written
/// constraints that hold.
#[derive(Clone, PartialEq, Debug)]
pub struct Scope {
    /// One product per name.
    pub names: BTreeMap<Arc<str>, Product>,
    /// The relation the integer names meet, with no auxiliary variable.
    pub relation: Formula,
    /// The written constraints that hold, a test and its negations by printed text, each
    /// with its free names; at most [`presburger::ATOMS`] of them.
    pub written: BTreeMap<String, (Term, Vec<Arc<str>>)>,
    /// Whether no state reaches this scope.
    pub bottom: bool,
    /// The written constraints already enumerated, each as its text with the values of its
    /// static names. A second enumeration removes nothing more: the members a constraint holds
    /// at do not depend on the interval, which already lies within them.
    pub enumerated: BTreeSet<Enumerated>,
}

/// A written constraint's text with the values of its static names.
pub type Enumerated = (String, Vec<(Arc<str>, Value)>);

/// What [`Scope::unbind`] needs to undo a [`Scope::bind`].
#[derive(Debug)]
pub enum Unbind {
    /// The name was not in scope and nothing else changed: remove it.
    Fresh(Arc<str>),
    /// The scope as it was before.
    Saved(Box<Scope>),
}

impl Scope {
    /// The scope of `names`, reduced.
    pub fn new(names: impl IntoIterator<Item = (Arc<str>, Product)>) -> Scope {
        let mut s = Scope {
            names: names.into_iter().collect(),
            relation: Formula::top(),
            written: BTreeMap::new(),
            bottom: false,
            enumerated: BTreeSet::new(),
        };
        s.reduce();
        s
    }

    /// The scope of a `let` body that binds `x` to `p`, in place. A name already in scope is
    /// forgotten first: the relation is weakened to say nothing of it and the written
    /// constraints on it go, since they hold of the value it shadows. Nothing else in the
    /// scope then mentions `x`, so `p`'s own reductions are the whole reduction, and the
    /// scope is not copied unless `x` shadows a name or `p` is empty.
    pub fn bind(&mut self, x: &Arc<str>, mut p: Product) -> Unbind {
        for _ in 0..REDUCTION_ROUNDS {
            let before = p.clone();
            p.reduce_domains();
            if p == before {
                break;
            }
        }
        if !self.bottom && !p.is_empty() && !self.names.contains_key(x) {
            self.names.insert(x.clone(), p);
            return Unbind::Fresh(x.clone());
        }
        let saved = Unbind::Saved(Box::new(self.clone()));
        if self.bottom {
            return saved;
        }
        self.relation = self.relation.forget(x);
        self.written.retain(|_, (_, free)| !free.contains(x));
        self.names.insert(x.clone(), p);
        if self.names[x].is_empty() {
            self.bottom = true;
            for p in self.names.values_mut() {
                *p = Product::bottom();
            }
        }
        saved
    }

    /// Undoes the [`Scope::bind`] that returned `u`.
    pub fn unbind(&mut self, u: Unbind) {
        match u {
            Unbind::Fresh(x) => {
                self.names.remove(&x);
            }
            Unbind::Saved(s) => *self = *s,
        }
    }

    /// Records `t` as a written constraint that holds, unless the scope already holds
    /// [`presburger::ATOMS`] of them: dropping a constraint only weakens the scope.
    pub fn write(&mut self, t: Term) {
        let key = t.to_string();
        if self.written.len() < presburger::ATOMS || self.written.contains_key(&key) {
            let free = stage::free(&t).into_iter().collect();
            self.written.insert(key, (t, free));
        }
    }

    /// The static names among `names`, and their values.
    fn statics_of<'a>(
        &self,
        names: impl IntoIterator<Item = &'a Arc<str>>,
    ) -> BTreeMap<Arc<str>, Value> {
        names
            .into_iter()
            .filter_map(|n| {
                let v = self.names.get(n)?.value()?;
                Some((n.clone(), v.clone()))
            })
            .collect()
    }

    /// The product of `name`; the top for a name not in scope.
    pub fn get(&self, name: &str) -> Product {
        self.names.get(name).cloned().unwrap_or_else(Product::top)
    }

    /// The names with one value each, and their values.
    pub fn statics(&self) -> BTreeMap<Arc<str>, Value> {
        self.names
            .iter()
            .filter_map(|(n, p)| p.value().map(|v| (n.clone(), v.clone())))
            .collect()
    }

    /// Whether the state `env`, a value for each of some names, is in this scope: each value
    /// in its name's product and the integers meeting the relation. A name `env` does not
    /// give is not checked; the relation is checked only when `env` gives each of its names.
    pub fn contains(&self, env: &BTreeMap<Arc<str>, Value>) -> bool {
        if self.bottom {
            return false;
        }
        if !env.iter().all(|(n, v)| self.get(n).contains(v)) {
            return false;
        }
        let mut point = BTreeMap::new();
        for a in self.relation.atoms() {
            match &a {
                Atom::Sym(n) => match env.get(n) {
                    Some(Value::Int(v)) => {
                        point.insert(a.clone(), *v as i128);
                    }
                    _ => return true,
                },
                _ => return true,
            }
        }
        self.relation.holds(&point).unwrap_or(true)
    }

    /// The least scope above both.
    pub fn join(&self, other: &Scope) -> Scope {
        if self.bottom {
            return other.clone();
        }
        if other.bottom {
            return self.clone();
        }
        let mut names = self.names.clone();
        for (n, p) in names.iter_mut() {
            p.join(&other.get(n));
        }
        for n in other.names.keys() {
            names.entry(n.clone()).or_insert_with(Product::top);
        }
        Scope {
            names,
            relation: Formula::either(&self.relation, &other.relation).bounded(),
            written: self
                .written
                .iter()
                .filter(|(k, _)| other.written.contains_key(*k))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
            bottom: false,
            enumerated: self
                .enumerated
                .intersection(&other.enumerated)
                .cloned()
                .collect(),
        }
    }

    /// This scope where `test` gave `outcome`, reduced.
    pub fn assume(&self, test: &Term, outcome: bool, premises: &Premises) -> Scope {
        let mut s = self.clone();
        s.narrow(test, outcome, premises);
        s.reduce();
        s
    }

    fn narrow(&mut self, test: &Term, outcome: bool, prem: &Premises) {
        if self.bottom {
            return;
        }
        match test {
            Term::Lit(Value::Bool(b)) => {
                if *b != outcome {
                    self.bottom = true;
                }
            }
            Term::Prim(Prim::Not, a) if a.len() == 1 => self.narrow(&a[0], !outcome, prem),
            Term::Prim(p @ (Prim::And | Prim::Or), a) if a.len() == 2 => {
                // Both sides hold when the connective's outcome forces them; otherwise the
                // cases join.
                let forced = (*p == Prim::And) == outcome;
                if forced {
                    self.narrow(&a[0], outcome, prem);
                    self.narrow(&a[1], outcome, prem);
                } else {
                    let mut l = self.clone();
                    l.narrow(&a[0], outcome, prem);
                    l.reduce();
                    let mut r = self.clone();
                    r.narrow(&a[0], !outcome, prem);
                    r.narrow(&a[1], outcome, prem);
                    r.reduce();
                    *self = l.join(&r);
                }
            }
            Term::If(c, a, b) if is_bool_lit(a) || is_bool_lit(b) || (is_test(a) && is_test(b)) => {
                let mut t = self.clone();
                t.narrow(c, true, prem);
                t.reduce();
                t.narrow(a, outcome, prem);
                t.reduce();
                let mut f = self.clone();
                f.narrow(c, false, prem);
                f.reduce();
                f.narrow(b, outcome, prem);
                f.reduce();
                *self = t.join(&f);
            }
            _ => self.atom(test, outcome, prem),
        }
    }

    /// Narrows by one atomic test.
    fn atom(&mut self, test: &Term, outcome: bool, prem: &Premises) {
        let statics = self.statics_of(&stage::free(test));
        let t = substitute(test, &statics);
        // A bare name of bool type.
        if let Term::Var(x) = &t
            && let Some(p) = self.names.get_mut(x)
        {
            let v = Value::Bool(outcome);
            let lit = Type::lit(&v).expect("a bool literal type");
            p.ty.meet(&lit, prem);
            p.cell.finite.meet(&FiniteSet::of([v]), prem);
        }
        // An equality with a literal, and the congruence of `x mod c == r`.
        if let Term::Prim(op @ (Prim::Eq | Prim::Ne), a) = &t
            && a.len() == 2
        {
            let equal = (*op == Prim::Eq) == outcome;
            for (l, r) in [(&a[0], &a[1]), (&a[1], &a[0])] {
                match (l, r) {
                    (Term::Var(x), Term::Lit(v)) => {
                        if let Some(p) = self.names.get_mut(x) {
                            equality(p, v, equal, prem);
                        }
                    }
                    (Term::Prim(Prim::Mod, m), Term::Lit(Value::Int(r))) if equal => {
                        if let [Term::Var(x), Term::Lit(Value::Int(c))] = &m[..]
                            && *c != 0
                            && let Some(p) = self.names.get_mut(x)
                        {
                            let k = c.unsigned_abs();
                            if *r < 0 || r.unsigned_abs() >= k {
                                p.ty.meet(&!&Type::int(), prem);
                            } else {
                                p.cell.congruence.meet(&Congruence::new(k, *r), prem);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        let int = Type::int();
        let free = stage::free(&t);
        let inputs: Vec<Arc<str>> = free
            .iter()
            .filter(|n| {
                self.names
                    .get(*n)
                    .is_some_and(|p| p.ty.element.subtype(&int))
            })
            .cloned()
            .collect();
        // The preimage of the outcome.
        let mut exact = false;
        if !inputs.is_empty() {
            let doms: Domains = inputs
                .iter()
                .map(|n| (n.clone(), self.get(n).ints().clone()))
                .collect();
            let pre = preimage(&t, &doms, &Demand::Bool(outcome));
            exact = pre.exact;
            for (n, d) in &pre.domains {
                if let Some(p) = self.names.get_mut(n) {
                    p.meet_ints(d, prem);
                }
            }
        }
        // The linear relation, when the test needs no auxiliary variable and says more than
        // the intervals: a test of one name whose preimage is exact is the interval itself.
        if !inputs.is_empty()
            && inputs.len() == free.len()
            && (inputs.len() > 1 || !exact)
            && let Some(rs) = relations(&[&t], &inputs, false)
            && let Some(r) = rs.into_iter().next()
            && r.defs.is_empty()
        {
            let body = if outcome {
                r.body
            } else {
                Formula::negate(r.body)
            };
            self.relation = Formula::and(vec![self.relation.clone(), body]).bounded();
        }
        // The written constraint.
        let kept = if outcome {
            test.clone()
        } else {
            Term::Prim(Prim::Not, vec![test.clone()])
        };
        self.write(kept);
    }

    /// Passes information between the domains of every product, the relation and the written
    /// constraints until nothing changes or [`REDUCTION_ROUNDS`] have run.
    pub fn reduce(&mut self) {
        for _ in 0..REDUCTION_ROUNDS {
            if self.bottom || self.names.values().any(Product::is_empty) {
                break;
            }
            let before = self.names.clone();
            self.project();
            for p in self.names.values_mut() {
                p.reduce_domains();
            }
            self.enumerate();
            if self.names == before {
                break;
            }
        }
        if self.bottom || self.names.values().any(Product::is_empty) {
            self.bottom = true;
            for p in self.names.values_mut() {
                *p = Product::bottom();
            }
        }
    }

    /// The projection of the relation, within every interval, onto each name it mentions.
    fn project(&mut self) {
        if self.relation == Formula::top() {
            return;
        }
        let mentioned = self.relation.atoms();
        let within: Result<Vec<Formula>, presburger::Over> = mentioned
            .iter()
            .filter_map(|a| match a {
                Atom::Sym(n) => Some(presburger::member(a, self.get(n).ints())),
                _ => None,
            })
            .collect();
        let Ok(mut parts) = within else {
            return;
        };
        parts.push(self.relation.clone());
        let whole = Formula::and(parts);
        let syms: Vec<Atom> = mentioned
            .into_iter()
            .filter(|a| matches!(a, Atom::Sym(_)))
            .collect();
        let Ok(each) = presburger::project_each(&whole, &syms) else {
            return;
        };
        for (a, x) in syms.iter().zip(each) {
            if let Atom::Sym(n) = a
                && let Ok(x) = x
                && let Some(p) = self.names.get_mut(n)
            {
                let prem = p.premises();
                p.meet_ints(&x, &prem);
            }
        }
    }

    /// Enumeration: the written constraints on each small integer name, and those on static
    /// names only. Each constraint is enumerated once for its static names, and every
    /// evaluation of one call shares one thread.
    fn enumerate(&mut self) {
        let pending: Vec<(Term, Vec<Arc<str>>, Enumerated)> = self
            .written
            .iter()
            .filter_map(|(text, (c, free))| {
                if !free.iter().all(|n| self.names.contains_key(n)) {
                    return None;
                }
                let statics = self.statics_of(free);
                let open: Vec<Arc<str>> = free
                    .iter()
                    .filter(|n| !statics.contains_key(*n))
                    .cloned()
                    .collect();
                let key = (text.clone(), statics.clone().into_iter().collect());
                (open.len() <= 1 && !self.enumerated.contains(&key))
                    .then(|| (substitute(c, &statics), open, key))
            })
            .collect();
        if pending.is_empty() {
            return;
        }
        on_stack(|stack| self.enumerate_on(stack, pending));
    }

    fn enumerate_on(&mut self, stack: &Stack, pending: Vec<(Term, Vec<Arc<str>>, Enumerated)>) {
        let int = Type::int();
        for (c, open, key) in pending {
            let at = |extra: Option<(&Arc<str>, i64)>| {
                let t = match extra {
                    Some((n, v)) => Term::Let(
                        n.clone(),
                        Arc::new(Term::Lit(Value::Int(v))),
                        Arc::new(c.clone()),
                    ),
                    None => c.clone(),
                };
                Evaluator::new(World::new())
                    .with_fuel(ENUMERATION_FUEL)
                    .run_on(stack, &t)
            };
            match &open[..] {
                [] => {
                    if let Ok(v) = at(None)
                        && v != Value::Bool(true)
                    {
                        self.bottom = true;
                        return;
                    }
                }
                [n] => {
                    let Some(p) = self.names.get(n) else {
                        continue;
                    };
                    if !p.ty.element.subtype(&int) {
                        continue;
                    }
                    let Some(vs) = members(p.ints(), ENUMERATION_BUDGET) else {
                        continue;
                    };
                    let mut kept = Vec::new();
                    let mut out_of_fuel = false;
                    for v in &vs {
                        match at(Some((n, *v))) {
                            Ok(Value::Bool(true)) => kept.push(*v),
                            Err(KernelError::OutOfFuel) => {
                                out_of_fuel = true;
                                break;
                            }
                            _ => {}
                        }
                    }
                    if !out_of_fuel && kept.len() < vs.len() {
                        let x = IntervalSet::from_pieces(
                            kept.iter().map(|&v| (End::Fin(v), End::Fin(v))).collect(),
                        )
                        .cap(PIECE_LIMIT);
                        let p = self.names.get_mut(n).expect("a name in scope");
                        let prem = p.premises();
                        p.meet_ints(&x, &prem);
                    }
                }
                _ => continue,
            }
            self.enumerated.insert(key);
        }
    }
}

impl fmt::Display for Scope {
    /// `unreachable`, or each name not at the top with its product's lines indented, then the
    /// relation when there is one.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.bottom {
            return writeln!(f, "unreachable");
        }
        for (n, p) in &self.names {
            let s = p.to_string();
            if s.is_empty() {
                continue;
            }
            writeln!(f, "{n}:")?;
            for l in s.lines() {
                writeln!(f, "  {l}")?;
            }
        }
        if self.relation != Formula::top() {
            writeln!(f, "relation {}", self.relation)?;
        }
        Ok(())
    }
}

/// Whether `t` is a boolean literal.
fn is_bool_lit(t: &Term) -> bool {
    matches!(t, Term::Lit(Value::Bool(_)))
}

/// Whether `t` is a comparison, a connective or a boolean literal.
fn is_test(t: &Term) -> bool {
    matches!(
        t,
        Term::Lit(Value::Bool(_))
            | Term::Prim(
                Prim::Eq
                    | Prim::Ne
                    | Prim::Lt
                    | Prim::Le
                    | Prim::Gt
                    | Prim::Ge
                    | Prim::And
                    | Prim::Or
                    | Prim::Not,
                _
            )
    )
}

/// The product of a literal equality's outcome on `p`: the literal itself, or every value but
/// it, excluded by complement in the type, the interval and the finite set.
fn equality(p: &mut Product, v: &Value, equal: bool, prem: &Premises) {
    if equal {
        let lit = Product::literal(v);
        p.ty.meet(&lit.ty.element, prem);
        p.cell.finite.meet(&lit.cell.finite.element, prem);
        if let Value::Int(n) = v {
            p.meet_ints(&IntervalSet::single(*n), prem);
            p.cell.congruence.meet(&Congruence::single(*n), prem);
        }
        return;
    }
    if let Some(lit) = Type::lit(v) {
        p.ty.meet(&!&lit, prem);
    }
    if let Value::Int(n) = v {
        let x = IntervalSet::single(*n).complement_in(p.ints());
        p.meet_ints(&x, prem);
    }
    if let FiniteSet::Set(vs) = &p.cell.finite.element {
        let mut vs = vs.clone();
        vs.remove(v);
        p.cell.finite.meet(&FiniteSet::Set(vs), prem);
    }
}

/// `t` with each of `env`'s names bound to its value.
fn substitute(t: &Term, env: &BTreeMap<Arc<str>, Value>) -> Term {
    let free = stage::free(t);
    env.iter()
        .filter(|(n, _)| free.contains(*n))
        .fold(t.clone(), |b, (n, v)| {
            Term::Let(n.clone(), Arc::new(Term::Lit(v.clone())), Arc::new(b))
        })
}

/// The element of `e`'s value in `scope`: a literal, a value computed from static names, the
/// revision table's forward transfer over integers, or the join of an `if`'s reachable arms.
/// `scope` is as it was on return.
pub fn forward(e: &Term, scope: &mut Scope) -> Product {
    on_stack(|_| forward_in(e, scope))
}

fn forward_in(e: &Term, scope: &mut Scope) -> Product {
    if scope.bottom {
        return Product::bottom();
    }
    let none = Premises::new();
    match e {
        Term::Lit(v) => return Product::literal(v),
        Term::Var(x) => return scope.get(x),
        Term::Let(x, v, b) => {
            let p = forward_in(v, scope);
            let u = scope.bind(x, p);
            let out = forward_in(b, scope);
            scope.unbind(u);
            return out;
        }
        Term::If(c, a, b) => {
            let mut t = scope.assume(c, true, &none);
            let mut f = scope.assume(c, false, &none);
            let mut p = forward_in(a, &mut t);
            p.join(&forward_in(b, &mut f));
            return p;
        }
        Term::Prim(op, args) => return forward_prim(*op, args, scope),
        _ => {}
    }
    // `forward` does not recurse below this node, so its free names are found once.
    let free = stage::free(e);
    let time = free
        .iter()
        .map(|n| scope.get(n).time.element)
        .fold(Time::Build, |a, b| a.join(&b));
    let statics = scope.statics_of(&free);
    if !matches!(e, Term::Lam(..))
        && free.iter().all(|n| statics.contains_key(n))
        && let Some(p) = run_static(&substitute(e, &statics))
    {
        return p;
    }
    let mut p = Product::top();
    p.time.element = time;
    p
}

/// The element of a value computed at build time, if `t` evaluates to data within
/// [`ENUMERATION_FUEL`].
fn run_static(t: &Term) -> Option<Product> {
    let mut ev = Evaluator::new(World::new()).with_fuel(ENUMERATION_FUEL);
    match ev.run(t) {
        Ok(v) if !matches!(v, Value::Family(_)) => Some(Product::literal(&v)),
        _ => None,
    }
}

/// [`forward`] of a primitive: its value when every argument has one, else the revision
/// table's transfer over integers. Each argument is visited once.
fn forward_prim(op: Prim, args: &[Term], scope: &mut Scope) -> Product {
    let xs: Vec<Product> = args.iter().map(|a| forward_in(a, scope)).collect();
    if let Some(vs) = xs.iter().map(Product::value).collect::<Option<Vec<_>>>() {
        let t = Term::Prim(op, vs.into_iter().map(|v| Term::Lit(v.clone())).collect());
        if let Some(p) = run_static(&t) {
            return p;
        }
    }
    let mut p = Product::top();
    p.time.element = xs
        .iter()
        .map(|x| x.time.element)
        .fold(Time::Build, |a, b| a.join(&b));
    if let Some(op) = int_op(op)
        && !xs.is_empty()
        && xs.len() <= 2
        && xs.iter().all(|x| x.ty.element.subtype(&Type::int()))
    {
        let y = xs
            .get(1)
            .map_or_else(IntervalSet::top, |x| x.ints().clone());
        p.ty.element = Type::int();
        p.cell.ints.element = Bounds::ints(revision::forward(op, xs[0].ints(), &y));
        p.reduce_domains();
    }
    p
}

/// The revision table's operator for an integer primitive.
fn int_op(p: Prim) -> Option<Op> {
    Some(match p {
        Prim::Add => Op::Add,
        Prim::Sub => Op::Sub,
        Prim::Mul => Op::Mul,
        Prim::IntDiv => Op::Div,
        Prim::Mod => Op::Mod,
        Prim::Neg => Op::Neg,
        Prim::Abs => Op::Abs,
        Prim::Min => Op::Min,
        Prim::Max => Op::Max,
        _ => return None,
    })
}

/// One arm of an `if`: its test, the outcome that takes it, and the scope in it.
#[derive(Clone, Debug)]
pub struct Arm {
    /// The test, as the kernel prints it.
    pub guard: String,
    /// The outcome of the test that takes this arm.
    pub outcome: bool,
    /// The scope in the arm; bottom when no state reaches it.
    pub scope: Scope,
}

impl Arm {
    /// Whether some state may reach the arm.
    pub fn reachable(&self) -> bool {
        !self.scope.bottom
    }
}

/// Each `if` arm of `term` with its scope, `term`'s free names in `scope`, in the order the
/// arms are written. The walk enters `let` bindings, `if` arms and primitive and call
/// arguments; it does not enter a function body or a construct that binds names by pattern.
/// The premise of each test is its position in the walk.
pub fn arms(term: &Term, scope: &Scope) -> Vec<Arm> {
    // One evaluation thread serves every evaluation of the walk.
    on_stack(|_| {
        let mut out = Vec::new();
        let mut count = 0;
        walk(term, &mut scope.clone(), &mut out, &mut count);
        out
    })
}

fn walk(t: &Term, scope: &mut Scope, out: &mut Vec<Arm>, count: &mut u32) {
    match t {
        Term::Let(x, e, b) => {
            walk(e, scope, out, count);
            let p = forward(e, scope);
            let u = scope.bind(x, p);
            walk(b, scope, out, count);
            scope.unbind(u);
        }
        Term::If(c, a, b) => {
            let at = FactAddress {
                node: NodeAddress(vec![*count]),
                keypath: Vec::new(),
            };
            *count += 1;
            let prem = Premises::one(Premise::Constraint(at));
            for (o, arm) in [(true, a), (false, b)] {
                let mut s = scope.assume(c, o, &prem);
                out.push(Arm {
                    guard: c.to_string(),
                    outcome: o,
                    scope: s.clone(),
                });
                walk(arm, &mut s, out, count);
            }
        }
        Term::Prim(_, args) => {
            for a in args {
                walk(a, scope, out, count);
            }
        }
        Term::App(f, args) => {
            walk(f, scope, out, count);
            for a in args {
                walk(a, scope, out, count);
            }
        }
        _ => {}
    }
}
