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
//! - enumeration: a name of type within `int` whose finite set lists its integers keeps only the members at which each written constraint on it holds, the
//!   constraint's other names static and its form shown to end ([`stage::ends`]); a
//!   constraint whose form does not show it ends removes nothing. A range is left to the
//!   interval, congruence and relation reasoning (docs/thresholds.md, replacement 8). In a
//!   scope under `@exact` ([`Scope::exact`]) the scope is bottom exactly when no point of its
//!   bounded integer names' intervals and classes meets their written constraints. The
//!   constraints are taken in groups that share names, each group searched for one point
//!   ([`witness`]); the point is kept, and the group is searched again only when a name's
//!   interval or class no longer holds it. Nothing lists the points, so the scope stays the
//!   size of the source, and a question about the exact set is a test assumed in the scope:
//!   whether `p == 4` can hold is whether the scope assuming it is bottom.
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

use zed_kernel::provenance::{FactAddress, NodeAddress, Vector};
use zed_kernel::types::{Type, Universe};
use zed_kernel::{Evaluator, Prim, Stack, Term, Value, World, on_stack};

use super::affine::Bounds;
use super::cell::{Cell, Entry, Premise, Premises};
use super::interval::{End, IntervalSet};
use super::lattice::{Congruence, FiniteSet, Landmarks, Lattice};
use super::preimage::{Classes, Demand, Domains, Point, preimage, relations, witness};
use super::presburger::{self, Atom, Con, Formula, Lin};
use super::revision::{self, Op, reduce_congruence};
use crate::stage;

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
    fn widen(&self, next: &Self, _: &Landmarks) -> Self {
        self.join(next)
    }
    fn narrow(&self, next: &Self, _: &Landmarks) -> Self {
        *next
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

/// The parts a widening takes whole and a narrowing leaves whole: each base type, and the rest
/// of each universe. They cover every value.
fn parts() -> Vec<Type> {
    let all_bases = bases().iter().fold(Type::empty(), |a, b| &a | b);
    let mut out = bases().to_vec();
    for u in [
        Universe::Scalar,
        Universe::Tuple,
        Universe::Struct,
        Universe::Morphism,
    ] {
        out.push(Type::universe(u) - &all_bases);
    }
    out
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
    fn widen(&self, next: &Self, _: &Landmarks) -> Self {
        let mut out = self | next;
        for p in parts() {
            if !(next & &p).subtype(self) {
                out = &out | &p;
            }
        }
        out
    }
    /// `next` in each part that `self` holds whole, and `self` in the others: each part leaves
    /// the whole at most once and is then fixed, so every chain of narrowings is finite.
    fn narrow(&self, next: &Self, _: &Landmarks) -> Self {
        parts().iter().fold(Type::empty(), |out, p| {
            let whole = p.subtype(self);
            &out | &(if whole { next & p } else { self & p })
        })
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
    /// Whether every domain of `self` is below the same domain of `other`: the order in which
    /// the reduction only descends.
    pub fn leq(&self, other: &Product) -> bool {
        let (a, b) = (&self.cell, &other.cell);
        a.ints.element.leq(&b.ints.element)
            && a.congruence.element.leq(&b.congruence.element)
            && a.finite.element.leq(&b.finite.element)
            && a.float.element.leq(&b.float.element)
            && a.length.element.leq(&b.length.element)
            && self.ty.element.leq(&other.ty.element)
            && self.time.element.leq(&other.time.element)
    }

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
    pub fn widen(&mut self, other: &Product, head: &FactAddress, marks: &Landmarks) -> bool {
        [
            self.cell.widen(&other.cell, head, marks),
            self.ty.widen(&other.ty, head, marks),
            self.time.widen(&other.time, head, marks),
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
        } else {
            // The type's integers narrowed to the interval, listed only when the list is no
            // longer than what is listed from: the type's own integer literals, or an interval
            // with no more members than its two endpoints a piece.
            let x = self.ints().clone();
            let vs: Option<Vec<Value>> = match (&self.ty.element & &int).listed() {
                Some(vs) => Some(
                    vs.into_iter()
                        .filter(|v| !matches!(v, Value::Int(n) if !x.contains(*n)))
                        .collect(),
                ),
                None => {
                    let most = 2 * x.pieces().len() as i128;
                    let size = x.pieces().iter().try_fold(0i128, |n, p| match p {
                        (End::Fin(a), End::Fin(b)) => Some(n + (*b as i128 - *a as i128) + 1),
                        _ => None,
                    });
                    size.filter(|&n| n <= most).map(|_| {
                        x.pieces()
                            .iter()
                            .flat_map(|p| match *p {
                                (End::Fin(a), End::Fin(b)) => a..=b,
                                _ => unreachable!("every piece is finite"),
                            })
                            .map(Value::Int)
                            .collect()
                    })
                }
            };
            if let Some(vs) = vs {
                let lits = Type::union_all(vs.iter().filter_map(Type::lit));
                self.ty.meet(&(&!&int | &lits), &prem);
            }
        }
        if let FiniteSet::Set(vs) = &self.cell.finite.element {
            let lits: Option<Vec<Type>> = vs.iter().map(Type::lit).collect();
            if let Some(lits) = lits {
                let t = Type::union_all(lits);
                self.ty.meet(&t, &prem);
            }
        }
        // The other domains from the type.
        if let Some(vs) = self.ty.element.listed() {
            self.cell.finite.meet(&FiniteSet::of(vs), &prem);
        }
        if let Some(vs) = (&self.ty.element & &int).listed()
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

/// The integers of `p` when its finite set lists them: every member an integer. The finite
/// set holds the literals the source lists, and an interval's members only where they are no
/// more than its endpoints, so the list is no longer than what it is read from.
fn listed(p: &Product) -> Option<Vec<i64>> {
    let FiniteSet::Set(vs) = &p.cell.finite.element else {
        return None;
    };
    vs.iter()
        .map(|v| match v {
            Value::Int(n) => Some(*n),
            _ => None,
        })
        .collect()
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
    /// with its free names.
    pub written: BTreeMap<String, (Term, Vec<Arc<str>>)>,
    /// Whether no state reaches this scope.
    pub bottom: bool,
    /// The written constraints already enumerated, each as its text with the values of its
    /// static names. A second enumeration removes nothing more: the members a constraint holds
    /// at do not depend on the interval, which already lies within them.
    pub enumerated: BTreeSet<Enumerated>,
    /// The top-level parts of the relation already projected: its constraints together, and
    /// each other conjunct with them, each with the intervals and classes of the names it
    /// mentions at that projection, which are all a projection reads of them. A part is
    /// projected again only when one of these has changed since
    /// (docs/thresholds.md, replacement 4).
    pub projected: std::collections::HashMap<Formula, Projected>,
    /// Whether the scope is under `@exact`.
    pub exact: bool,
    /// Under `@exact`, each group of written constraints that share names, by their texts with
    /// the static values substituted, with a point that meets them all.
    pub exactly: BTreeMap<Vec<String>, Point>,
}

/// The intervals and classes of a part's names when it was last projected.
pub type Projected = Vec<(Arc<str>, IntervalSet, Congruence)>;

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
        Scope::of(names, false)
    }

    /// The scope of `names` in a declaration annotated `@exact`, reduced: its written
    /// constraints narrow their names exactly (DESIGN.md sec:constraints).
    pub fn exact(names: impl IntoIterator<Item = (Arc<str>, Product)>) -> Scope {
        Scope::of(names, true)
    }

    fn of(names: impl IntoIterator<Item = (Arc<str>, Product)>, exact: bool) -> Scope {
        let mut s = Scope {
            names: names.into_iter().collect(),
            relation: Formula::top(),
            written: BTreeMap::new(),
            bottom: false,
            enumerated: BTreeSet::new(),
            projected: std::collections::HashMap::new(),
            exact,
            exactly: BTreeMap::new(),
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
        loop {
            let before = p.clone();
            p.reduce_domains();
            debug_assert!(p.leq(&before), "a reduction rose: {before:?} to {p:?}");
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

    /// Records `t` as a written constraint that holds.
    pub fn write(&mut self, t: Term) {
        let free = stage::free(&t).into_iter().collect();
        self.written.insert(t.to_string(), (t, free));
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
            relation: Formula::either(&self.relation, &other.relation),
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
            // A part projected on both sides is projected within the join: each side's
            // intervals lie within its projection, and the join's within their union.
            projected: self
                .projected
                .iter()
                .filter(|(k, _)| other.projected.contains_key(*k))
                .map(|(k, v)| {
                    let at = v
                        .iter()
                        .map(|(n, _, _)| {
                            let p = names.get(n).cloned().unwrap_or_else(Product::top);
                            (n.clone(), p.ints().clone(), p.cell.congruence.element)
                        })
                        .collect();
                    (k.clone(), at)
                })
                .collect(),
            exact: self.exact,
            // A point of either side is a point of the join; it is checked again when read.
            exactly: other
                .exactly
                .iter()
                .chain(&self.exactly)
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
            names,
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
            self.relation = Formula::and(vec![self.relation.clone(), body]);
        }
        // The written constraint, unless it is a test of one integer name whose preimage is
        // exact: the name's interval then holds exactly the values that meet it, and
        // enumeration would remove none of them.
        if !(exact && inputs.len() == 1 && free.len() == 1) {
            let kept = if outcome {
                test.clone()
            } else {
                Term::Prim(Prim::Not, vec![test.clone()])
            };
            self.write(kept);
        }
    }

    /// Passes information between the domains of every product, the relation and the written
    /// constraints until nothing changes. This ends with no bound on the rounds
    /// (docs/thresholds.md, replacement 3). Every pass only narrows. The relation is projected
    /// again only when another reduction has changed a product since its last projection, and
    /// the others change only finitely often: a class narrows only to one value or none, a
    /// finite set or a type's literals only lose members, enumeration runs once per
    /// constraint, and an interval is narrowed only by these and by the class, whose
    /// rounding moves no endpoint the projection gave, since the projection reads every
    /// congruence and so its hulls end at members of each class.
    pub fn reduce(&mut self) {
        let mut projected: Option<BTreeMap<Arc<str>, Product>> = None;
        loop {
            if self.bottom || self.names.values().any(Product::is_empty) {
                break;
            }
            let before = self.names.clone();
            if projected.as_ref() != Some(&self.names) {
                self.project();
                projected = Some(self.names.clone());
            }
            for p in self.names.values_mut() {
                p.reduce_domains();
            }
            self.enumerate();
            debug_assert!(
                self.names.iter().all(|(n, p)| p.leq(&before[n])),
                "a reduction rose"
            );
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

    /// The projection of the relation, within every interval, onto each name it mentions:
    /// of its top-level constraints together, and of each other top-level conjunct with them,
    /// each part only when it is new or a product of a name it mentions has changed since its
    /// last projection. The parts pass information through the products alone, so a change
    /// spreads to the parts that mention the names it narrowed and to no others, and a test
    /// that narrows nothing costs its own parts alone.
    fn project(&mut self) {
        if self.relation == Formula::top() {
            self.projected.clear();
            return;
        }
        let conjuncts: Vec<Formula> = match &self.relation {
            Formula::And(gs) => gs.clone(),
            g => vec![g.clone()],
        };
        let (cons, others): (Vec<Formula>, Vec<Formula>) = conjuncts
            .into_iter()
            .partition(|g| matches!(g, Formula::Con(_)));
        let base = Formula::and(cons);
        let mut parts = others;
        if base != Formula::top() {
            parts.push(base.clone());
        }
        let snapshot = |s: &Scope, f: &Formula| -> Projected {
            f.atoms()
                .iter()
                .filter_map(|a| match a {
                    Atom::Sym(n) => {
                        let p = s.get(n);
                        Some((n.clone(), p.ints().clone(), p.cell.congruence.element))
                    }
                    _ => None,
                })
                .collect()
        };
        let due: Vec<Formula> = parts
            .iter()
            .filter(|g| {
                let whole = Formula::and(vec![(*g).clone(), base.clone()]);
                self.projected.get(*g) != Some(&snapshot(self, &whole))
            })
            .cloned()
            .collect();
        self.projected.retain(|g, _| parts.contains(g));
        for g in &due {
            self.project_part(&Formula::and(vec![g.clone(), base.clone()]));
        }
        for g in due {
            let whole = Formula::and(vec![g.clone(), base.clone()]);
            let at = snapshot(self, &whole);
            self.projected.insert(g, at);
        }
    }

    /// Meets each name `part` mentions with its projection, within every interval.
    fn project_part(&mut self, part: &Formula) {
        let mentioned = part.atoms();
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
        // Each name's congruence, `x == m * k + r` with `k` free, so that the projection
        // already lies in the class: otherwise the class moves an endpoint, the relation moves
        // another name's to match, and the two pass a bound back and forth without end.
        for a in &mentioned {
            if let Atom::Sym(n) = a
                && let Congruence::Class { modulus, residue } = self.get(n).cell.congruence.element
                && modulus > 1
            {
                let k = Lin::atom(Atom::Sym(format!("{n} mod").into()));
                let Ok(Ok(rhs)) = k
                    .times(modulus.into())
                    .map(|m| m.plus(&Lin::constant(residue.into())))
                else {
                    return;
                };
                let Ok(c) = Con::eq(&Lin::atom(a.clone()), &rhs) else {
                    return;
                };
                parts.push(Formula::Con(c));
            }
        }
        parts.push(part.clone());
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
        if self.exact {
            self.enumerate_exactly();
        }
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
                let c = substitute(c, &statics);
                (open.len() <= 1 && !self.enumerated.contains(&key) && stage::ends(&c))
                    .then_some((c, open, key))
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
                Evaluator::new(World::new()).run_on(stack, &t)
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
                    let Some(vs) = listed(p) else {
                        continue;
                    };
                    let kept: Vec<i64> = vs
                        .iter()
                        .copied()
                        .filter(|v| matches!(at(Some((n, *v))), Ok(Value::Bool(true))))
                        .collect();
                    if kept.len() < vs.len() {
                        let x = IntervalSet::from_pieces(
                            kept.iter().map(|&v| (End::Fin(v), End::Fin(v))).collect(),
                        );
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

impl Scope {
    /// Under `@exact`: each written constraint whose free names are all in scope, with its
    /// static names substituted and its other names all integers, meets each of those with the
    /// projection of the points at which it holds; one with no such name is evaluated. A
    /// constraint is projected again only when an interval or class of its open names has
    /// changed since its last projection. Each projection only narrows, and each name's
    /// interval and class change only finitely often, so the rounds of [`Scope::reduce`] end.
    fn enumerate_exactly(&mut self) {
        let int = Type::int();
        let bounded = |p: &Product| matches!(p.ints().bounds(), Some((End::Fin(_), End::Fin(_))));
        // Each written constraint over open integer names, all bounded, with its statics
        // substituted; then the groups of those that share an open name.
        let mut groups: Vec<(Vec<Term>, BTreeSet<Arc<str>>)> = Vec::new();
        for (c, free) in self.written.values() {
            if !free.iter().all(|n| self.names.contains_key(n)) {
                continue;
            }
            let statics = self.statics_of(free);
            let open: BTreeSet<Arc<str>> = free
                .iter()
                .filter(|n| !statics.contains_key(*n))
                .cloned()
                .collect();
            if open.is_empty()
                || !open.iter().all(|n| {
                    let p = self.get(n);
                    p.ty.element.subtype(&int) && bounded(&p)
                })
            {
                continue;
            }
            let mut group = (vec![substitute(c, &statics)], open);
            groups.retain(|(cs, ns)| {
                if ns.is_disjoint(&group.1) {
                    return true;
                }
                group.0.extend(cs.iter().cloned());
                group.1.extend(ns.iter().cloned());
                false
            });
            groups.push(group);
        }
        for (cs, open) in groups {
            let mut key: Vec<String> = cs.iter().map(|c| c.to_string()).collect();
            key.sort();
            let holds = |w: &Point| {
                open.iter().all(|n| {
                    w.get(n)
                        .is_some_and(|&v| self.get(n).contains(&Value::Int(v)))
                })
            };
            if self.exactly.get(&key).is_some_and(holds) {
                continue;
            }
            let all = cs
                .into_iter()
                .reduce(|a, b| Term::Prim(Prim::And, vec![a, b]))
                .expect("a group has a constraint");
            let dom: Domains = open
                .iter()
                .map(|n| (n.clone(), self.get(n).ints().clone()))
                .collect();
            let classes: Classes = open
                .iter()
                .map(|n| (n.clone(), self.get(n).cell.congruence.element))
                .collect();
            match witness(&all, &dom, &classes, &Demand::Bool(true)) {
                Some(Some(w)) => {
                    self.exactly.insert(key, w);
                }
                Some(None) => {
                    self.bottom = true;
                    return;
                }
                None => {}
            }
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

/// The element of a value computed at build time, if `t`'s form shows it ends
/// ([`stage::ends`]) and it evaluates to data.
fn run_static(t: &Term) -> Option<Product> {
    if !stage::ends(t) {
        return None;
    }
    let mut ev = Evaluator::new(World::new());
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
                node: NodeAddress(Vector::unit(*count)),
                keypath: Vector::new(),
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
