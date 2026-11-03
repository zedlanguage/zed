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

use imbl::ordmap::DiffItem;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use zed_kernel::provenance::{FactAddress, NodeAddress, Position, Vector};
use zed_kernel::types::{Type, Universe};
use zed_kernel::{Evaluator, Prim, Term, Value, World, on_stack};

use super::affine::Bounds;
use super::cell::{Cell, Entry, Premise, Premises};
use super::conjuncts::{self, BlockId, Conjuncts, Uses};
use super::hull::Hull;
use super::int::Int;
use super::interval::{End, IntervalSet};
use super::lattice::{Congruence, FiniteSet, Landmarks, Lattice};
use super::preimage::{Classes, Demand, Domains, Point, preimage, relations, witness};
use super::presburger::{self, Atom, Con, Formula, Lin, Rel};
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
    ///
    /// Complexity tradeoff: a type that grows within a base type (more literals, more tuple
    /// shapes) jumps to the whole base type, so a loop's type keeps none of the members it
    /// gained. Why: types do not satisfy the ascending chain condition (`#a | #b | …` grows
    /// forever), so the fixpoint needs a widening; keeping members would need a landmark set
    /// of types and a test per member. Trigger: a widening at which `next` has a value in a
    /// base type part that `self` lacks. Test:
    /// `l01_39_reduced_product::controls::a_type_widens_to_its_whole_base_type`. No
    /// COMPLEXITY.md row. A complete solution would compute the loop's least fixpoint over
    /// types, which is undecidable in general. A more precise widening, still not complete,
    /// would stop first at the loop's written type literals (type landmarks, as intervals do
    /// with integer landmarks), at a cost of one subtype test per landmark.
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
    ///
    /// Complexity tradeoff: in a part that `self` does not hold whole, a smaller `next` is not
    /// taken, so `1 | 2` narrowed by `1` stays `1 | 2`. Why: types have infinite descending
    /// chains (`int`, `int` without `0`, without `0` and `1`, …), so taking the meet at each
    /// step need not end; with this rule each part changes at most once. Trigger: a part of
    /// `self` that is neither empty nor the whole base type or universe part. Test:
    /// `l01_39_reduced_product::controls::a_type_widens_to_its_whole_base_type` (its narrowing
    /// cases). No COMPLEXITY.md row. A complete solution would compute the greatest fixpoint
    /// below the widened type, which needs the loop's effect on its values solved exactly:
    /// undecidable in general.
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
    fn meet_ints(&mut self, x: IntervalSet, premises: &Premises) {
        self.cell.ints.meet(&Bounds::ints(x), premises);
    }

    /// The reductions between this product's own domains, once each.
    fn reduce_domains(&mut self) {
        let prem = self.premises();
        let int = Type::int();
        let (x, c) = reduce_congruence(self.ints(), &self.cell.congruence.element);
        self.meet_ints(x, &prem);
        self.cell.congruence.meet(&c, &prem);
        // A finite set against the interval: an integer member outside it goes.
        if let FiniteSet::Set(vs) = &self.cell.finite.element {
            let x = self.ints();
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
                self.meet_ints(ints, &prem);
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
            //
            // Complexity tradeoff: an interval with more members than that is not listed, so
            // the type keeps all of `int` there and loses what listing would carry into it.
            // Why: listing an interval costs time and space in its members, which can be
            // exponential in the bits written. Trigger: a finite interval set whose members
            // exceed twice its pieces, a measure relative to the written endpoints and not a
            // constant. Test:
            // `l01_39_reduced_product::controls::a_listed_set_is_enumerated_and_a_range_is_not`.
            // No COMPLEXITY.md row. A complete solution would let the type language hold
            // integer ranges, so that the interval enters the type without listing.
            let x = self.ints();
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
            self.meet_ints(ints, &prem);
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
/// constraints that hold. Each part is held in persistent maps, so that a case of a nest
/// copies the scope in O(1), and the join of two cases and the reduction of a scope cost the
/// parts that differ, found by the maps' difference, and not the whole scope.
#[derive(Clone, PartialEq, Debug)]
pub struct Scope {
    /// One product per name, in a persistent map, so that a case of a nest copies it in O(1) and
    /// two scopes that share most of it are compared and joined in the names that differ.
    pub names: imbl::OrdMap<Arc<str>, Product>,
    /// The relation the integer names meet, with no auxiliary variable.
    pub relation: Conjuncts,
    /// The written constraints that hold, a test and its negations by printed text, each
    /// with its free names.
    pub written: imbl::OrdMap<String, (Term, Vec<Arc<str>>)>,
    /// The texts of the written constraints on each name.
    written_by: Uses<String>,
    /// Whether no state reaches this scope.
    pub bottom: bool,
    /// The written constraints already enumerated, each as its text with the values of its
    /// static names. A second enumeration removes nothing more: the members a constraint holds
    /// at do not depend on the interval, which already lies within them.
    pub enumerated: imbl::OrdSet<Enumerated>,
    /// The top-level parts of the relation already projected: its constraints together, and
    /// each other conjunct with them, each with the intervals and classes of the names it
    /// mentions at that projection, which are all a projection reads of them. A part is
    /// projected again only when one of these has changed since
    /// (docs/thresholds.md, replacement 4).
    pub projected: imbl::OrdMap<PartKey, Projected>,
    /// Whether the scope is under `@exact`.
    pub exact: bool,
    /// Under `@exact`, each group of written constraints that share names, by their texts with
    /// the static values substituted, with a point that meets them all.
    pub exactly: imbl::OrdMap<Vec<String>, Point>,
    /// The causes for which the integer solver left a question undecided while this scope was
    /// narrowed or projected; each one leaves the scope sound but wider than it could be.
    ///
    /// Complexity tradeoff: a refused question (`presburger::Refusal`, whose costs and
    /// triggers are documented where each is raised) leaves the relation's narrowing out, so
    /// the scope is wider. Only the join of two scopes reads this set, to unite it, so the
    /// widening is silent: no warning names it (a flaw, docs/reviews/tradeoffs.md). Test: no
    /// test yet.
    /// COMPLEXITY.md row S18 for the solver. A complete solution would decide every question
    /// (see `presburger`), or at least report this set as a warning at the scope.
    pub refusals: imbl::OrdSet<presburger::Refusal>,
    /// Each name a `let` of the walk bound, with the order of its binding and, for a function,
    /// its lambda: a test that calls a function is closed over it before its preimage is taken
    /// ([`Scope::close`]). Shared between the scopes of a walk's arms, not copied.
    bindings: imbl::OrdMap<Arc<str>, Binding>,
    /// The order the next binding gets.
    clock: u64,
    /// The names as the last reduction left them, each product then at its own fixed point:
    /// a reduction reduces only the names that differ from these.
    reduced: Reduced,
    /// The scope as the last projection and the last enumeration found it.
    seen: Seen,
}

/// A name's `let` binding in a [`Scope`].
#[derive(Clone, PartialEq, Debug)]
struct Binding {
    /// The order of the binding: a binding made later has a larger one.
    order: u64,
    /// The lambda the name is bound to, when it is one.
    function: Option<Arc<Term>>,
}

/// The names as a reduction left them: a cache, equal in every scope, so that two scopes are
/// equal when their names, relation and constraints are.
#[derive(Clone, Default)]
struct Reduced(imbl::OrdMap<Arc<str>, Product>);

impl PartialEq for Reduced {
    fn eq(&self, _: &Reduced) -> bool {
        true
    }
}

impl fmt::Debug for Reduced {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("..")
    }
}

/// The names and conjuncts as the last projection found them, and the names, written
/// constraints and enumerated ones as the last enumeration found them: a cache, equal in every
/// scope. A projection then looks only at the trees of blocks that mention a name or hold a
/// conjunct that has changed since, and an enumeration only at the written constraints that
/// are new or mention such a name, so that a test costs what it changes.
#[derive(Clone, Default)]
struct Seen {
    projection: Option<Projection>,
    enumeration: Option<Enumeration>,
}

/// The names and conjuncts a projection found.
type Projection = (imbl::OrdMap<Arc<str>, Product>, Conjuncts);

/// The names, written constraints and enumerated ones an enumeration found.
type Enumeration = (
    imbl::OrdMap<Arc<str>, Product>,
    imbl::OrdMap<String, (Term, Vec<Arc<str>>)>,
    imbl::OrdSet<Enumerated>,
);

impl PartialEq for Seen {
    fn eq(&self, _: &Seen) -> bool {
        true
    }
}

impl fmt::Debug for Seen {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("..")
    }
}

/// The intervals and classes of a part's names when it was last projected.
pub type Projected = Vec<(Arc<str>, IntervalSet, Congruence)>;

/// The names of `now` that are not in `then` or differ from it there, with their products.
fn changed<'a>(
    then: &'a imbl::OrdMap<Arc<str>, Product>,
    now: &'a imbl::OrdMap<Arc<str>, Product>,
) -> impl Iterator<Item = (&'a Arc<str>, &'a Product)> {
    then.diff(now).filter_map(|d| match d {
        DiffItem::Add(n, p) | DiffItem::Update { new: (n, p), .. } => Some((n, p)),
        DiffItem::Remove(..) => None,
    })
}

/// The names a formula mentions.
fn syms(f: &Formula) -> Vec<Arc<str>> {
    f.atoms()
        .into_iter()
        .filter_map(|a| match a {
            Atom::Sym(n) => Some(n),
            _ => None,
        })
        .collect()
}

/// What a part of the relation is projected for: its conjunct, and the equalities among the
/// constraints it is projected with, sorted; `None` in their place for a tree of blocks
/// projected as a whole. A part is projected again when an equality joins or leaves them; a
/// new inequality alone does not make it due (a known limit of precision, COMPLEXITY.md), so
/// that a part costs its conjunct and not the constraints.
pub type PartKey = (Formula, Option<Arc<[Con]>>);

/// Each of `conjuncts` that is not a constraint, with the constraints, and the constraints
/// alone when there are any; each part with its key, the conjunct it is projected for, or the
/// constraints for theirs.
fn split<'a>(conjuncts: impl Iterator<Item = &'a Formula>) -> Vec<(PartKey, Formula)> {
    let (cons, others): (Vec<&Formula>, Vec<&Formula>) =
        conjuncts.partition(|g| matches!(g, Formula::Con(_)));
    let mut eqs: Vec<Con> = cons
        .iter()
        .filter_map(|g| match g {
            Formula::Con(c) if c.rel == Rel::Eq => Some(c.clone()),
            _ => None,
        })
        .collect();
    eqs.sort_unstable();
    let eqs: Option<Arc<[Con]>> = Some(eqs.into());
    let base = Formula::and(cons.into_iter().cloned().collect());
    let mut parts: Vec<(PartKey, Formula)> = others
        .into_iter()
        .map(|g| {
            (
                (g.clone(), eqs.clone()),
                Formula::and(vec![g.clone(), base.clone()]),
            )
        })
        .collect();
    if base != Formula::top() {
        parts.push(((base.clone(), eqs), base));
    }
    parts
}

/// Top-level conjuncts of a relation projected together: a block of [`Conjuncts::blocks`].
struct Block {
    /// What is projected: each conjunct that is not a constraint, with the constraints, and
    /// the constraints alone, each with the conjunct it is projected for ([`split`]). A new
    /// conjunct then costs its own part, not the block's.
    parts: Vec<(PartKey, Formula)>,
    /// The names they mention.
    names: Vec<Arc<str>>,
}

impl Block {
    /// Block `b` of `relation`.
    fn of(relation: &Conjuncts, b: BlockId) -> Block {
        let names: BTreeSet<Arc<str>> =
            relation.blocks().members(b).flat_map(|g| syms(g)).collect();
        Block {
            parts: split(relation.blocks().members(b).map(|g| &**g)),
            names: names.into_iter().collect(),
        }
    }
}

/// The blocks a projection looks at.
enum Due {
    /// Every block.
    All,
    /// These blocks.
    Blocks(BTreeSet<BlockId>),
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
            relation: Conjuncts::default(),
            written: imbl::OrdMap::new(),
            written_by: Uses::default(),
            bottom: false,
            enumerated: imbl::OrdSet::new(),
            projected: imbl::OrdMap::new(),
            exact,
            exactly: imbl::OrdMap::new(),
            refusals: imbl::OrdSet::new(),
            bindings: imbl::OrdMap::new(),
            clock: 0,
            reduced: Reduced::default(),
            seen: Seen::default(),
        };
        s.reduce();
        s
    }

    /// The scope of a `let` body that binds `x` to `p`, in place. A name already in scope is
    /// forgotten first: the relation is weakened to say nothing of it and the written
    /// constraints on it go, since they hold of the value it shadows. Nothing else in the
    /// scope then mentions `x`, so `p`'s own reductions are the whole reduction, and the
    /// scope is not copied unless `x` shadows a name or `p` is empty. `e` is the bound term,
    /// kept when it is a lambda, so that a test calling `x` is read through the call.
    pub fn bind(&mut self, x: &Arc<str>, mut p: Product, e: &Arc<Term>) -> Unbind {
        loop {
            let before = p.clone();
            p.reduce_domains();
            debug_assert!(p.leq(&before), "a reduction rose: {before:?} to {p:?}");
            if p == before {
                break;
            }
        }
        let binding = Binding {
            order: self.clock,
            function: matches!(**e, Term::Lam(..)).then(|| e.clone()),
        };
        self.clock += 1;
        if !self.bottom && !p.is_empty() && !self.names.contains_key(x) {
            self.names.insert(x.clone(), p);
            self.bindings.insert(x.clone(), binding);
            return Unbind::Fresh(x.clone());
        }
        let saved = Unbind::Saved(Box::new(self.clone()));
        if self.bottom {
            return saved;
        }
        self.relation.forget(x);
        let gone: Vec<String> = self.written_by.of(x).cloned().collect();
        for k in &gone {
            self.unwrite(k);
        }
        self.bindings.insert(x.clone(), binding);
        self.names.insert(x.clone(), p);
        if self.names[x].is_empty() {
            self.bottom = true;
            self.names = self
                .names
                .keys()
                .map(|n| (n.clone(), Product::bottom()))
                .collect();
        }
        saved
    }

    /// Undoes the [`Scope::bind`] that returned `u`.
    pub fn unbind(&mut self, u: Unbind) {
        match u {
            Unbind::Fresh(x) => {
                self.names.remove(&x);
                self.bindings.remove(&x);
            }
            Unbind::Saved(s) => *self = *s,
        }
    }

    /// Records `t` as a written constraint that holds.
    pub fn write(&mut self, t: Term) {
        let k = t.to_string();
        self.unwrite(&k);
        let free: Vec<Arc<str>> = stage::free(&t).into_iter().collect();
        for n in &free {
            self.written_by.add(n, &k);
        }
        self.written.insert(k, (t, free));
    }

    /// Forgets the written constraint of text `k`.
    fn unwrite(&mut self, k: &str) {
        if let Some((_, free)) = self.written.remove(k) {
            let k = k.to_string();
            for n in &free {
                self.written_by.remove(n, &k);
            }
        }
    }

    /// Forgets every projection made, so that the next reduction projects the whole relation
    /// again: for the tests that compare a scope with one projected afresh.
    #[doc(hidden)]
    pub fn forget_projections(&mut self) {
        self.projected = imbl::OrdMap::new();
        self.seen.projection = None;
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

    /// `test` under the functions in scope it calls, and those they call in turn, each a `let`
    /// in the order of its binding, so that the preimage reads through the calls (DESIGN.md
    /// step L1.25); `None` when it calls none. A function that reads a name bound at or after
    /// its own binding, itself included, would read another binding here, so it is left
    /// unbound and the transfer stops at its call. The cost is the functions reached and
    /// their terms' sizes, each visited once.
    fn close(&self, test: &Term) -> Option<Term> {
        let mut seen: BTreeSet<Arc<str>> = BTreeSet::new();
        let mut todo: Vec<Arc<str>> = stage::free(test).into_iter().collect();
        let mut reached: Vec<(u64, &Arc<str>, &Arc<Term>)> = Vec::new();
        while let Some(n) = todo.pop() {
            if !seen.insert(n.clone()) {
                continue;
            }
            let Some((name, b)) = self.bindings.get_key_value(&n) else {
                continue;
            };
            let Some(f) = &b.function else { continue };
            let reads = stage::free(f);
            let later = |m: &Arc<str>| self.bindings.get(m).is_some_and(|c| c.order >= b.order);
            if reads.iter().any(later) {
                continue;
            }
            reached.push((b.order, name, f));
            todo.extend(reads);
        }
        if reached.is_empty() {
            return None;
        }
        reached.sort_unstable_by_key(|r| r.0);
        Some(
            reached
                .into_iter()
                .rev()
                .fold(test.clone(), |body, (_, n, f)| {
                    Term::Let(n.clone(), f.clone(), Arc::new(body))
                }),
        )
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
        let relation = self.relation.formula();
        let mut point = BTreeMap::new();
        for a in relation.atoms() {
            match &a {
                Atom::Sym(n) => match env.get(n) {
                    Some(Value::Int(v)) => {
                        point.insert(a.clone(), Int::from(i128::from(*v)));
                    }
                    _ => return true,
                },
                _ => return true,
            }
        }
        relation.holds(&point)
    }

    /// The least scope above both. Each part of the scope is found from the parts the two
    /// sides do not share, by the persistent maps' difference: a join of two cases of one
    /// scope costs what the cases changed, not the scope.
    pub fn join(&self, other: &Scope) -> Scope {
        if self.bottom {
            return other.clone();
        }
        if other.bottom {
            return self.clone();
        }
        // A name both sides share unchanged is its own join; the others are found by the
        // persistent maps' difference, which skips what they share.
        let mut names = self.names.clone();
        let mut seeds: BTreeSet<Arc<str>> = BTreeSet::new();
        for d in self.names.diff(&other.names) {
            match d {
                DiffItem::Update {
                    old: (n, p),
                    new: (_, q),
                } => {
                    let mut j = p.clone();
                    j.join(q);
                    names.insert(n.clone(), j);
                    seeds.insert(n.clone());
                }
                DiffItem::Add(n, _) | DiffItem::Remove(n, _) => {
                    names.insert(n.clone(), Product::top());
                    seeds.insert(n.clone());
                }
            }
        }
        // The conjuncts of each side the other does not hold; those they share are the join's.
        let (mut mine, mut theirs) = (Vec::new(), Vec::new());
        for d in self.relation.set().diff(other.relation.set()) {
            match d {
                imbl::ordset::DiffItem::Remove(g) => mine.push(g.clone()),
                imbl::ordset::DiffItem::Add(g) => theirs.push(g.clone()),
            }
        }
        for g in mine.iter().chain(&theirs) {
            seeds.extend(conjuncts::names(g));
        }
        // The equalities of two or more atoms that hold on both sides (Karr's join), which the
        // disjunction of the relations holds but no projection of one of its parts finds. Each
        // side implies them, so each side's rest holds where they do as it holds with their
        // pivots replaced; the disjunction then mentions no pivot, and a join of sides that fix
        // `k` names leaves a disjunction of one name and `k - 1` equalities of two. Each side's
        // hull is taken over the names linked by equalities to a name or a conjunct the sides
        // do not share: the rest of the two hulls is one, which their join keeps as it is and
        // the shared conjuncts already state.
        let is_eq = |g: &Formula| matches!(g, Formula::Con(c) if c.rel == Rel::Eq);
        let (eqs, near) = conjuncts::reach(&[&self.relation, &other.relation], seeds, is_eq);
        let hull = self.hull(&eqs, &near).join(&other.hull(&eqs, &near));
        let reduce = |c: &Con| hull.reduce(c);
        let kept: Vec<Formula> = hull
            .rows()
            .filter(|t| t.terms.len() > 1)
            .map(|t| {
                Formula::Con(Con {
                    lin: t.clone(),
                    rel: Rel::Eq,
                })
            })
            .collect();
        // Each side states the bounds of the names the other's relation mentions and its own
        // does not, which its products hold and its relation leaves out: otherwise a side of
        // relation `true` makes the disjunction `true`, and the join depends on how the cases
        // are grouped.
        let (a, b) = (self.stated(&mine, &theirs), other.stated(&theirs, &mine));
        let mut relation = self.relation.clone();
        let mut added = vec![Formula::either(&a, &b, &reduce)];
        added.extend(kept);
        relation.swap(&mine, Formula::and(added));
        // The written and enumerated constraints both sides hold.
        let (mut written, mut written_by) = (self.written.clone(), self.written_by.clone());
        for d in self.written.diff(&other.written) {
            if let DiffItem::Remove(k, (_, free)) = d {
                written.remove(k);
                for n in free {
                    written_by.remove(n, k);
                }
            }
        }
        let mut enumerated = self.enumerated.clone();
        for d in self.enumerated.diff(&other.enumerated) {
            if let imbl::ordset::DiffItem::Remove(e) = d {
                enumerated.remove(e);
            }
        }
        // A part projected on both sides is projected within the join: each side's
        // intervals lie within its projection, and the join's within their union.
        let mut projected = self.projected.clone();
        for d in self.projected.diff(&other.projected) {
            match d {
                DiffItem::Remove(k, _) => {
                    projected.remove(k);
                }
                DiffItem::Update { old: (k, v), .. } => {
                    let at = v
                        .iter()
                        .map(|(n, _, _)| {
                            let p = names.get(n).cloned().unwrap_or_else(Product::top);
                            (n.clone(), p.ints().clone(), p.cell.congruence.element)
                        })
                        .collect();
                    projected.insert(k.clone(), at);
                }
                DiffItem::Add(..) => {}
            }
        }
        // A point of either side is a point of the join; it is checked again when read.
        let mut exactly = self.exactly.clone();
        for d in self.exactly.diff(&other.exactly) {
            if let DiffItem::Add(k, v) = d {
                exactly.insert(k.clone(), v.clone());
            }
        }
        let mut refusals = self.refusals.clone();
        for d in self.refusals.diff(&other.refusals) {
            if let imbl::ordset::DiffItem::Add(r) = d {
                refusals.insert(*r);
            }
        }
        Scope {
            relation,
            written,
            written_by,
            bottom: false,
            enumerated,
            projected,
            exact: self.exact,
            exactly,
            refusals,
            // Both sides narrow one scope, which bound the names; neither binds one the other
            // does not.
            bindings: self.bindings.clone(),
            clock: self.clock.max(other.clock),
            names,
            // This side's reduced names and what it last projected and enumerated: the join
            // differs from them in what it changed.
            reduced: self.reduced.clone(),
            seen: self.seen.clone(),
        }
    }

    /// `mine`, the conjuncts of the relation the other side does not hold, with the finite
    /// bounds of each name `theirs` mentions and the relation does not.
    fn stated(&self, mine: &[Arc<Formula>], theirs: &[Arc<Formula>]) -> Formula {
        let mut out: Vec<Formula> = Vec::new();
        let mut seen: BTreeSet<Arc<str>> = BTreeSet::new();
        for n in theirs.iter().flat_map(|g| syms(g)) {
            let x = Atom::Sym(n.clone());
            if !seen.insert(n.clone())
                || self.relation.mentioning(&n).any(|g| g.atoms().contains(&x))
            {
                continue;
            }
            let Some((lo, hi)) = self.names.get(&n).and_then(|p| p.ints().bounds()) else {
                continue;
            };
            let x = Lin::atom(x);
            if let End::Fin(v) = lo {
                out.push(Formula::Con(Con::ge(&x, &Lin::constant(v))));
            }
            if let End::Fin(v) = hi {
                out.push(Formula::Con(Con::ge(&Lin::constant(v), &x)));
            }
        }
        out.extend(mine.iter().map(|g| (**g).clone()));
        Formula::and(out)
    }

    /// The affine hull of the scope's points over `near`: the equalities among `eqs` the
    /// relation holds, and each name of `near` of one integer value.
    fn hull(&self, eqs: &BTreeSet<Arc<Formula>>, near: &BTreeSet<Arc<str>>) -> Hull {
        let mut terms: Vec<Lin> = eqs
            .iter()
            .filter(|g| self.relation.set().contains(*g))
            .filter_map(|g| match &**g {
                Formula::Con(c) => Some(c.lin.clone()),
                _ => None,
            })
            .collect();
        for n in near {
            if let Some(Value::Int(v)) = self.names.get(n).and_then(Product::value) {
                terms.push(Lin::atom(Atom::Sym(n.clone())).minus(&Lin::constant(*v)));
            }
        }
        Hull::of(&terms)
    }

    /// This scope where `test` gave `outcome`, reduced.
    pub fn assume(&self, test: &Term, outcome: bool, premises: &Premises) -> Scope {
        let mut s = self.clone();
        s.narrow(test, outcome, premises);
        s.reduce();
        s
    }

    /// Narrows by `test` giving `outcome`. The test is read as a [`Tree`]; when it has cases,
    /// the linear relation of the whole test, taken before any narrowing, is kept with the
    /// join of the cases, which keeps only what the cases share.
    fn narrow(&mut self, test: &Term, outcome: bool, prem: &Premises) {
        if self.bottom {
            return;
        }
        let (tree, pol) = Tree::of(test);
        self.narrow_linear(&tree, 0, outcome == pol, prem);
    }

    /// Narrows by node `n` of `tree` giving `value`, keeping the linear relation of the node's
    /// test when it has cases ([`Scope::narrow`]). A nest the value forces whose test has no
    /// such relation, as when one side holds a `mod`, is narrowed side by side, each side
    /// keeping its own: so `a && b` narrows as `a` then `b` do. This is done at the root alone,
    /// where a side of a forced nest is not a forced nest, which would be one node with it
    /// ([`Tree::of`]); so the terms taken are the root's and its sides', twice the test's size.
    fn narrow_linear(&mut self, tree: &Tree, n: usize, value: bool, prem: &Premises) {
        if self.bottom {
            return;
        }
        let body = match &tree.nodes[n].kind {
            Kind::Nest(..) | Kind::If(_) => self.relation_of(&tree.term_at(n), value),
            Kind::Lit(_) | Kind::Atom => None,
        };
        let Some(body) = body else {
            match &tree.nodes[n].kind {
                Kind::Nest(and, sides) if *and == value && n == 0 => {
                    for &(k, p) in sides {
                        self.narrow_linear(tree, k, value == p, prem);
                    }
                }
                _ => self.narrow_node(tree, n, value, prem),
            }
            return;
        };
        let before = self.relation.clone();
        self.narrow_node(tree, n, value, prem);
        // The relation the narrowing gives is implied by the one before, the test's and the
        // products: each case adds the relations of its tests and bounds its products hold.
        // So the test's relation replaces it, but for the equalities of two atoms or more the
        // join of the cases states at the top (Karr's join), which a projection of the test's
        // relation onto each name does not find.
        if !self.bottom {
            let narrowed = std::mem::replace(&mut self.relation, before);
            let eqs: Vec<Formula> = self
                .relation
                .set()
                .diff(narrowed.set())
                .filter_map(|d| match d {
                    imbl::ordset::DiffItem::Add(g) => match &**g {
                        Formula::Con(c) if c.rel == Rel::Eq && c.lin.terms.len() > 1 => {
                            Some((**g).clone())
                        }
                        _ => None,
                    },
                    imbl::ordset::DiffItem::Remove(_) => None,
                })
                .collect();
            self.relation.and(body);
            for g in eqs {
                self.relation.and(g);
            }
        }
    }

    /// The linear relation of `test` giving `outcome`, with the static names' values, when the
    /// test mentions two integer names or more and nothing else, and needs no auxiliary
    /// variable.
    fn relation_of(&self, test: &Term, outcome: bool) -> Option<Formula> {
        let t = substitute(test, &self.statics_of(&stage::free(test)));
        let free = stage::free(&t);
        let int = Type::int();
        let inputs: Vec<Arc<str>> = free
            .iter()
            .filter(|n| {
                self.names
                    .get(*n)
                    .is_some_and(|p| p.ty.element.subtype(&int))
            })
            .cloned()
            .collect();
        if inputs.len() < 2 || inputs.len() != free.len() {
            return None;
        }
        let r = relations(&[&t], &inputs, false)?.into_iter().next()?;
        if !r.defs.is_empty() {
            return None;
        }
        Some(if outcome {
            r.body
        } else {
            Formula::negate(r.body)
        })
    }

    /// Narrows by node `n` of `tree` giving `value`. A nest the value forces narrows by each
    /// side; any other nest or `if` is split into its cases, which are joined.
    fn narrow_node(&mut self, tree: &Tree, n: usize, value: bool, prem: &Premises) {
        if self.bottom {
            return;
        }
        let node = &tree.nodes[n];
        match &node.kind {
            Kind::Lit(b) => {
                if *b != value {
                    self.bottom = true;
                }
            }
            Kind::Atom => self.atom(node.term, value, prem),
            Kind::Nest(and, sides) if *and == value => {
                for &(k, p) in sides {
                    self.narrow_node(tree, k, value == p, prem);
                }
            }
            Kind::Nest(..) | Kind::If(_) => match self.cases(tree, n, value, prem) {
                Some(s) => *self = s,
                None => self.bottom = true,
            },
        }
    }

    /// The join of the cases of node `n` giving `value`, or `None` when every case is bottom.
    /// A nest the value does not force has a case per side, each starting from this scope
    /// with the sides before it excluded from the names' products ([`Scope::exclude`]); an
    /// `if` has the case of each arm. A nest the value forces narrows by each side but the one
    /// of the most nodes that has cases, whose cases are the nest's: so a chain of nests is
    /// one list of cases, joined in pairs ([`join_cases`]), and only a side of at most half a
    /// nest's nodes is narrowed by a call within this one.
    fn cases(&self, tree: &Tree, n: usize, value: bool, prem: &Premises) -> Option<Scope> {
        let mut out = Vec::new();
        let mut work = vec![(self.clone(), n, value)];
        while let Some((mut s, n, v)) = work.pop() {
            if s.bottom {
                continue;
            }
            match &tree.nodes[n].kind {
                Kind::Nest(and, sides) if *and != v => {
                    for &(k, p) in sides {
                        work.push((s.clone(), k, v == p));
                        s.exclude(tree, k, v != p, prem);
                        if s.bottom {
                            break;
                        }
                    }
                }
                Kind::Nest(_, sides) => {
                    let heavy = sides
                        .iter()
                        .filter(|(k, _)| tree.splits(*k))
                        .max_by_key(|(k, _)| (tree.nodes[*k].size, std::cmp::Reverse(*k)))
                        .copied();
                    for &(k, p) in sides {
                        if Some((k, p)) != heavy {
                            s.narrow_node(tree, k, v == p, prem);
                        }
                    }
                    s.reduce();
                    match heavy {
                        Some((k, p)) => work.push((s, k, v == p)),
                        None => out.push(s),
                    }
                }
                Kind::If([c, a, b]) => {
                    let mut t = s.clone();
                    t.narrow_node(tree, c.0, c.1, prem);
                    t.reduce();
                    work.push((t, a.0, v == a.1));
                    s.narrow_node(tree, c.0, !c.1, prem);
                    s.reduce();
                    work.push((s, b.0, v == b.1));
                }
                Kind::Lit(_) | Kind::Atom => {
                    s.narrow_node(tree, n, v, prem);
                    s.reduce();
                    out.push(s);
                }
            }
        }
        out.retain(|s| !s.bottom);
        (!out.is_empty()).then(|| join_cases(out))
    }

    /// Narrows the names' products, and nothing else, by node `n` giving `value`: what a later
    /// case of a nest knows of the sides before it. The relation and the written constraints
    /// are left as they are, so a case costs its own side and not the sides before it.
    fn exclude(&mut self, tree: &Tree, n: usize, value: bool, prem: &Premises) {
        let node = &tree.nodes[n];
        match &node.kind {
            Kind::Lit(b) => {
                if *b != value {
                    self.bottom = true;
                }
            }
            Kind::Atom => {
                let t = substitute(node.term, &self.statics_of(&stage::free(node.term)));
                self.atom_names(&t, value, true, prem);
            }
            Kind::Nest(and, sides) if *and == value => {
                for &(k, p) in sides {
                    self.exclude(tree, k, value == p, prem);
                }
            }
            Kind::Nest(..) | Kind::If(_) => {}
        }
    }

    /// Narrows by one atomic test.
    fn atom(&mut self, test: &Term, outcome: bool, prem: &Premises) {
        let closed = self.close(test);
        let test = closed.as_ref().unwrap_or(test);
        // An integer name keeps its place: its interval holds its one value, and the
        // preimage reads the name where substituting it would leave terms it cannot cancel.
        let int = Type::int();
        let statics = self.statics_of(stage::free(test).iter().filter(|n| {
            !self
                .names
                .get(*n)
                .is_some_and(|p| p.ty.element.subtype(&int))
        }));
        let t = substitute(test, &statics);
        let (exact, inputs, free) = self.atom_names(&t, outcome, false, prem);
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
            self.relation.and(body);
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

    /// Narrows the names' products by the atomic test `t`, its static names substituted,
    /// giving `outcome`: a bare name of bool type, an equality with a literal, the congruence
    /// of `x mod c == r`, and the preimage of the outcome. Gives whether the preimage is exact,
    /// the test's integer names, and its free names. With `convex`, as for what a later case
    /// knows of the cases before it, each name keeps a convex hull: the complement of a value
    /// is not taken, and a preimage gives only its hull, so that a case of a nest of `k` sides
    /// holds no more pieces than one side gives.
    fn atom_names(
        &mut self,
        t: &Term,
        outcome: bool,
        convex: bool,
        prem: &Premises,
    ) -> (bool, Vec<Arc<str>>, BTreeSet<Arc<str>>) {
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
                    (Term::Var(x), Term::Lit(v)) if equal || !convex => {
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
        let free = stage::free(t);
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
            let pre = preimage(t, &doms, &Demand::Bool(outcome));
            exact = pre.exact;
            if let Some(r) = pre.refusal {
                self.refusals.insert(r);
            }
            for (n, d) in &pre.domains {
                if let Some(p) = self.names.get_mut(n) {
                    if convex {
                        p.meet_ints(d.hull(), prem);
                    } else {
                        p.meet_ints(d.clone(), prem);
                    }
                }
            }
        }
        (exact, inputs, free)
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
        self.reduce_with(false);
    }

    /// [`Scope::reduce`] with every tree of blocks projected as a whole, for the test that
    /// projecting by blocks keeps what this keeps.
    #[doc(hidden)]
    pub fn reduce_whole(&mut self) {
        self.reduce_with(true);
    }

    fn reduce_with(&mut self, whole: bool) {
        let mut force = whole;
        // The names as last reduced. A product's own reduction depends on it alone, so one
        // that has not changed since is at its fixed point, and only the names that differ
        // from these are reduced again or can have become empty: a reduction costs the names
        // that changed, found by the persistent maps' difference.
        let mut last = std::mem::take(&mut self.reduced.0);
        let empty = |names: &imbl::OrdMap<Arc<str>, Product>, last: &imbl::OrdMap<_, _>| {
            changed(last, names).any(|(_, p)| p.is_empty())
        };
        loop {
            if self.bottom || self.relation.is_bottom() || empty(&self.names, &last) {
                self.bottom = true;
                break;
            }
            let before = self.names.clone();
            // The names and conjuncts as projected are those before the projection, so that a
            // projection that moves a bound is followed by another, until none moves one.
            if let Some(due) = self.due(whole, force) {
                force = false;
                self.seen.projection = Some((self.names.clone(), self.relation.clone()));
                self.project(due, whole);
            }
            let dirty: Vec<Arc<str>> = changed(&last, &self.names)
                .map(|(n, _)| n.clone())
                .collect();
            for n in &dirty {
                if let Some(p) = self.names.get_mut(n) {
                    p.reduce_domains();
                }
            }
            last = self.names.clone();
            if dirty
                .iter()
                .any(|n| self.names.get(n).is_some_and(Product::is_empty))
            {
                self.bottom = true;
                break;
            }
            self.enumerate();
            debug_assert!(
                before.diff(&self.names).all(|d| matches!(
                    d,
                    DiffItem::Update { old: (_, a), new: (_, b) } if b.leq(a)
                )),
                "a reduction rose"
            );
            if self.names == before {
                break;
            }
        }
        if self.bottom || empty(&self.names, &last) {
            self.bottom = true;
            self.names = self
                .names
                .keys()
                .map(|n| (n.clone(), Product::bottom()))
                .collect();
        } else {
            self.reduced.0 = last;
        }
    }

    /// The blocks a projection looks at, with `whole` or when no projection was made every
    /// block ([`Due::All`]); `None` when nothing has changed. Otherwise the blocks of each
    /// conjunct added since the last projection, of each conjunct that shared a block with
    /// one removed since, and of each conjunct that mentions a name changed since, found by
    /// the persistent maps' difference. A conjunct removed has its parts' projections
    /// forgotten, so that it is projected again if it comes back.
    fn due(&mut self, whole: bool, force: bool) -> Option<Due> {
        let Some((names, old)) = &self.seen.projection else {
            return Some(Due::All);
        };
        if force {
            return Some(Due::All);
        }
        let mut out: BTreeSet<BlockId> = BTreeSet::new();
        let mut any = false;
        let blocks = self.relation.blocks();
        for d in names.diff(&self.names) {
            let (DiffItem::Add(n, _)
            | DiffItem::Remove(n, _)
            | DiffItem::Update { new: (n, _), .. }) = d;
            any = true;
            out.extend(self.relation.mentioning(n).filter_map(|g| blocks.of(g)));
        }
        let mut gone: Vec<Arc<Formula>> = Vec::new();
        for d in old.set().diff(self.relation.set()) {
            any = true;
            match d {
                imbl::ordset::DiffItem::Add(g) => out.extend(blocks.of(g)),
                imbl::ordset::DiffItem::Remove(g) => {
                    let was = old.blocks().of(g);
                    let mates = was.into_iter().flat_map(|b| old.blocks().members(b));
                    out.extend(mates.filter_map(|h| blocks.of(h)));
                    gone.push(g.clone());
                }
            }
        }
        for g in gone {
            let keys: Vec<PartKey> = self
                .projected
                .range((Formula::clone(&g), None)..)
                .map(|(k, _)| k)
                .take_while(|k| k.0 == *g)
                .cloned()
                .collect();
            for k in &keys {
                self.projected.remove(k);
            }
        }
        if !any {
            return None;
        }
        if whole {
            return Some(Due::All);
        }
        Some(Due::Blocks(out))
    }

    /// The projection of the relation, within every interval, onto each name it mentions, by
    /// blocks ([`Conjuncts::blocks`]): the top-level conjuncts that share an atom other than a
    /// name, or a cycle through names, form one block, so two blocks share at most one name
    /// and the blocks and the names they share form a forest (docs/thresholds.md,
    /// replacement 4). The blocks `due` names are projected from a worklist, in the order of
    /// their least conjuncts, and a block whose projection moves a name's interval or class
    /// puts each other block that mentions the name on the worklist: a bound passes along the
    /// tree, and a test that narrows nothing costs its own blocks alone. Each block is projected
    /// to its own fixed point ([`Scope::project_block`]). A bound comes back to a block only
    /// through the name it left by, since two blocks share one name and the tree has no cycle;
    /// when it does (an echo, below), the tree is projected as a whole once. With
    /// `whole`, every tree of blocks is projected as a whole: its constraints together, and
    /// each other conjunct with them.
    fn project(&mut self, due: Due, whole: bool) {
        if self.relation.is_top() {
            self.projected = imbl::OrdMap::new();
            return;
        }
        if whole {
            let blocks = self.relation.blocks();
            let mut trees: BTreeMap<BlockId, Vec<&Formula>> = BTreeMap::new();
            for g in self.relation.set() {
                if let Some(b) = blocks.of(g) {
                    trees.entry(blocks.tree(b)).or_default().push(&**g);
                }
            }
            let parts: Vec<(PartKey, Formula)> = trees
                .into_values()
                .flat_map(|tree| split(tree.into_iter()))
                .collect();
            for (key, g) in parts {
                let names = syms(&g);
                self.project_due(&key, &g, &names);
            }
            return;
        }
        // A projection narrows the names and neither reads nor changes the relation, which is
        // taken out while the worklist reads its blocks and put back after.
        let relation = std::mem::take(&mut self.relation);
        let blocks = relation.blocks();
        let due: Vec<BlockId> = match due {
            Due::All => blocks.all().collect(),
            Due::Blocks(bs) => bs.into_iter().collect(),
        };
        let mut order: Vec<(&Arc<Formula>, BlockId)> = due
            .into_iter()
            .filter_map(|b| Some((blocks.members(b).next()?, b)))
            .collect();
        order.sort_unstable();
        let mut work: std::collections::VecDeque<BlockId> =
            order.into_iter().map(|(_, b)| b).collect();
        let mut queued: BTreeSet<BlockId> = work.iter().copied().collect();
        // The names whose move put each block on the worklist.
        let mut cause: BTreeMap<BlockId, BTreeSet<Arc<str>>> = BTreeMap::new();
        // The trees projected as a whole after an echo, whose blocks are not projected again.
        let mut whole_trees: BTreeSet<BlockId> = BTreeSet::new();
        while let Some(b) = work.pop_front() {
            queued.remove(&b);
            let from = cause.remove(&b).unwrap_or_default();
            if whole_trees.contains(&blocks.tree(b)) {
                continue;
            }
            let block = Block::of(&relation, b);
            let before = self.snapshot(&block.names);
            self.project_block(&block);
            let mut echo = false;
            for (n, old) in block.names.iter().zip(&before) {
                let p = self.get(n);
                if (p.ints(), p.cell.congruence.element) == (&old.1, old.2) {
                    continue;
                }
                if p.ints().is_empty() {
                    self.relation = relation;
                    return;
                }
                echo |= from.contains(n);
                for g in relation.mentioning(n) {
                    if let Some(c) = blocks.of(g)
                        && c != b
                    {
                        cause.entry(c).or_default().insert(n.clone());
                        if queued.insert(c) {
                            work.push_back(c);
                        }
                    }
                }
            }
            // A block's projection drops what holds of its names' integers beyond their
            // intervals, such as a parity, so two blocks may pass a bound back and forth by one
            // value at a time. When a block moves the name whose move put it on the worklist,
            // its tree's conjuncts are projected together once, which gives the fixed point the
            // steps tend to, and the tree's other blocks on the worklist are dropped, as in a
            // block ([`Scope::project_block`]); the blocks of other trees go on.
            // In a tree a bound comes back to a block only through the name it left by, so
            // passing a bound along the tree without such an echo costs each block once.
            if echo {
                let (tree, _) = conjuncts::reach(&[&relation], block.names, |_| true);
                self.project_part(&Formula::and(tree.iter().map(|g| (**g).clone()).collect()));
                whole_trees.insert(blocks.tree(b));
            }
        }
        self.relation = relation;
    }

    /// Projects the parts of `b` that are due, then marks every part of `b` projected. A
    /// part is due when it is new or its names' intervals or classes have changed since its
    /// last projection, and a projection that moves a name's bound makes due again the other
    /// parts that mention the name, so a bound passes along a chain of parts. When one name's
    /// bound moves a second time, the parts may pass it back and forth by steps as small as
    /// one value; the block's conjuncts are then projected together once, which gives the
    /// fixed point the steps tend to, and the worklist stops. That is an event of the
    /// projection, not a count of steps or a size.
    fn project_block(&mut self, b: &Block) {
        let at = self.snapshot(&b.names);
        let mut work: std::collections::VecDeque<usize> = b
            .parts
            .iter()
            .enumerate()
            .filter(|(_, (key, _))| self.projected.get(key) != Some(&at))
            .map(|(i, _)| i)
            .collect();
        if work.is_empty() {
            return;
        }
        let names: Vec<Vec<Arc<str>>> = b.parts.iter().map(|(_, g)| syms(g)).collect();
        let mut users: BTreeMap<&Arc<str>, Vec<usize>> = BTreeMap::new();
        for (i, ns) in names.iter().enumerate() {
            for n in ns {
                users.entry(n).or_default().push(i);
            }
        }
        let mut queued = vec![false; b.parts.len()];
        for &i in &work {
            queued[i] = true;
        }
        let mut moved: BTreeSet<&Arc<str>> = BTreeSet::new();
        while let Some(i) = work.pop_front() {
            queued[i] = false;
            let before = self.snapshot(&names[i]);
            self.project_part(&b.parts[i].1);
            let mut again = false;
            let mut empty = false;
            for (n, old) in names[i].iter().zip(&before) {
                let p = self.get(n);
                if (p.ints(), p.cell.congruence.element) == (&old.1, old.2) {
                    continue;
                }
                empty |= p.ints().is_empty();
                again |= !moved.insert(n);
                for &j in &users[n] {
                    if j != i && !queued[j] {
                        queued[j] = true;
                        work.push_back(j);
                    }
                }
            }
            if empty {
                break;
            }
            if again {
                let all = Formula::and(b.parts.iter().map(|(_, g)| g.clone()).collect());
                self.project_part(&all);
                break;
            }
        }
        let at = self.snapshot(&b.names);
        for (key, _) in &b.parts {
            self.projected.insert(key.clone(), at.clone());
        }
    }

    /// Projects `part`, which mentions `names`, when `key` is new or one of their intervals
    /// or classes has changed since its last projection. A part keyed by its conjunct alone
    /// is not projected again when only the constraints it is projected with have grown.
    fn project_due(&mut self, key: &PartKey, part: &Formula, names: &[Arc<str>]) {
        if self.projected.get(key) == Some(&self.snapshot(names)) {
            return;
        }
        self.project_part(part);
        let at = self.snapshot(names);
        self.projected.insert(key.clone(), at);
    }

    /// The interval and class of each of `names`.
    fn snapshot(&self, names: &[Arc<str>]) -> Projected {
        names
            .iter()
            .map(|n| {
                let p = self.get(n);
                (n.clone(), p.ints().clone(), p.cell.congruence.element)
            })
            .collect()
    }

    /// Meets each name `part` mentions with its projection, within every interval.
    fn project_part(&mut self, part: &Formula) {
        let mentioned = part.atoms();
        let mut parts: Vec<Formula> = mentioned
            .iter()
            .filter_map(|a| match a {
                Atom::Sym(n) => Some(presburger::member(a, self.get(n).ints())),
                _ => None,
            })
            .collect();
        // Each name's congruence, `x == m * k + r` with `k` free, so that the projection
        // already lies in the class: otherwise the class moves an endpoint, the relation moves
        // another name's to match, and the two pass a bound back and forth without end.
        for a in &mentioned {
            if let Atom::Sym(n) = a
                && let Congruence::Class { modulus, residue } = self.get(n).cell.congruence.element
                && modulus > 1
            {
                let k = Lin::atom(Atom::Sym(format!("{n} mod").into()));
                let rhs = k
                    .times(Int::from(modulus as i128))
                    .plus(&Lin::constant(residue));
                parts.push(Formula::Con(Con::eq(&Lin::atom(a.clone()), &rhs)));
            }
        }
        parts.push(part.clone());
        let whole = Formula::and(parts);
        let syms: Vec<Atom> = mentioned
            .into_iter()
            .filter(|a| matches!(a, Atom::Sym(_)))
            .collect();
        let each = match presburger::project_each(&whole, &syms) {
            Ok((each, skipped)) => {
                self.refusals.extend(skipped);
                each
            }
            Err(r) => {
                self.refusals.insert(r);
                return;
            }
        };
        for (a, x) in syms.iter().zip(each) {
            let x = match x {
                Ok(x) => x,
                Err(r) => {
                    self.refusals.insert(r);
                    continue;
                }
            };
            if let Atom::Sym(n) = a
                && let Some(p) = self.names.get_mut(n)
            {
                let prem = p.premises();
                p.meet_ints(x, &prem);
            }
        }
    }

    /// Enumeration: the written constraints on each small integer name, and those on static
    /// names only. Each constraint is enumerated once for its static names. Only the written
    /// constraints that are new, mention a name that has changed, or have left the enumerated
    /// ones since the last enumeration are looked at, found by the persistent maps'
    /// difference: whether a constraint is due depends on these alone.
    ///
    /// Complexity tradeoff: a constraint is enumerated only when at most one of its names is
    /// open, its form shows that it ends (`stage::ends`), and the name's members are listed
    /// ([`listed`]); any other constraint narrows nothing here. Why: enumerating k open names
    /// costs the product of their members, exponential in k, and a constraint whose ending is
    /// not shown may not end at all (deciding that is the halting problem). Trigger: two or
    /// more open names, a constraint that calls itself or loops, or a range not listed. Tests:
    /// `l01_39_reduced_product::controls::enumeration_keeps_the_members_a_written_constraint_holds_at`,
    /// `l01_39_reduced_product::controls::a_listed_set_is_enumerated_and_a_range_is_not`. No
    /// COMPLEXITY.md row. A complete solution would enumerate the product of the open names
    /// (`@exact` does, by branch and prune), at a cost exponential in the open names, and a
    /// termination proof stronger than the form of the term (size-change termination,
    /// PSPACE-complete in the call graph).
    fn enumerate(&mut self) {
        if self.exact {
            self.enumerate_exactly();
        }
        let now = (
            self.names.clone(),
            self.written.clone(),
            self.enumerated.clone(),
        );
        let texts: BTreeSet<String> = match self.seen.enumeration.replace(now) {
            None => self.written.keys().cloned().collect(),
            Some((names, written, enumerated)) => {
                let mut out = BTreeSet::new();
                for d in written.diff(&self.written) {
                    if let DiffItem::Add(k, _) | DiffItem::Update { new: (k, _), .. } = d {
                        out.insert(k.clone());
                    }
                }
                for d in names.diff(&self.names) {
                    let (DiffItem::Add(n, _)
                    | DiffItem::Remove(n, _)
                    | DiffItem::Update { new: (n, _), .. }) = d;
                    out.extend(self.written_by.of(n).cloned());
                }
                for d in enumerated.diff(&self.enumerated) {
                    if let imbl::ordset::DiffItem::Remove((k, _)) = d
                        && self.written.contains_key(k)
                    {
                        out.insert(k.clone());
                    }
                }
                out
            }
        };
        let pending: Vec<(Term, Vec<Arc<str>>, Enumerated)> = texts
            .into_iter()
            .filter_map(|text| {
                let (c, free) = self.written.get(&text)?;
                if !free.iter().all(|n| self.names.contains_key(n)) {
                    return None;
                }
                let statics = self.statics_of(free);
                let open: Vec<Arc<str>> = free
                    .iter()
                    .filter(|n| !statics.contains_key(*n))
                    .cloned()
                    .collect();
                let key = (text, statics.clone().into_iter().collect());
                (open.len() <= 1 && !self.enumerated.contains(&key))
                    .then(|| substitute(c, &statics))
                    .filter(stage::ends)
                    .map(|c| (c, open, key))
            })
            .collect();
        if pending.is_empty() {
            return;
        }
        on_stack(|| self.enumerate_on(pending));
    }

    fn enumerate_on(&mut self, pending: Vec<(Term, Vec<Arc<str>>, Enumerated)>) {
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
                Evaluator::new(World::new()).run(&t)
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
                        p.meet_ints(x, &prem);
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
        if !self.relation.is_top() {
            writeln!(f, "relation {}", self.relation)?;
        }
        Ok(())
    }
}

/// A test read as a tree of connectives, built once per narrowing. `!` is a polarity on the
/// edge to a node, `true` for the node's test and `false` for its negation; a nest of one
/// connective is one node however it is nested, after De Morgan's laws; and an `if` with a
/// boolean arm is the connective it stands for. The sides of a nest are in an order that does
/// not depend on the order they are written in, so neither does the narrowing.
struct Tree<'a> {
    /// The nodes, the root first, each before the nodes below it.
    nodes: Vec<Node<'a>>,
}

/// A node of a [`Tree`].
struct Node<'a> {
    /// The test.
    term: &'a Term,
    kind: Kind,
    /// A hash of the node, equal for two tests that differ only in the order of the sides of
    /// their nests.
    key: u64,
    /// The number of nodes in the tree below it, itself included.
    size: usize,
    /// Where the node stands among the sides of a nest ([`rank`]).
    rank: u8,
}

/// What a [`Node`] is.
enum Kind {
    /// A boolean literal.
    Lit(bool),
    /// A test that is not taken apart.
    Atom,
    /// A nest of `&&` (`true`) or `||` (`false`): its sides, each with its polarity, in the
    /// order of their keys and polarities, those equal kept once.
    Nest(bool, Vec<(usize, bool)>),
    /// `if c { a } else { b }` with tests as arms: `c`, `a` and `b`, each with its polarity.
    If([(usize, bool); 3]),
}

/// Where a node stands among the sides of a nest, before its key: a later case knows the
/// sides before it through the names' products alone ([`Scope::exclude`]), so the sides
/// those products hold exactly come first. A literal, then a comparison of a name with a
/// literal, then any other comparison, then any other test, then a nest or an `if`.
fn rank(n: &Node) -> u8 {
    match (&n.kind, n.term) {
        (Kind::Lit(_), _) => 0,
        (Kind::Atom, Term::Prim(p, a)) if is_comparison(*p) && a.len() == 2 => {
            match (&a[0], &a[1]) {
                (Term::Var(_), Term::Lit(_)) | (Term::Lit(_), Term::Var(_)) => 1,
                _ => 2,
            }
        }
        (Kind::Atom, _) => 3,
        (Kind::Nest(..) | Kind::If(_), _) => 4,
    }
}

/// Whether `p` compares two values.
fn is_comparison(p: Prim) -> bool {
    matches!(
        p,
        Prim::Eq | Prim::Ne | Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge
    )
}

/// `t` without its outer `!`s, and whether their number is even.
fn strip(mut t: &Term) -> (&Term, bool) {
    let mut pol = true;
    while let Term::Prim(Prim::Not, a) = t
        && a.len() == 1
    {
        t = &a[0];
        pol = !pol;
    }
    (t, pol)
}

/// The connective `t` is, `&&` (`true`) or `||` (`false`), with its two sides and their
/// polarities: `if c { true } else { b }` is `c || b`, `if c { false } else { b }` is
/// `!c && b`, `if c { a } else { true }` is `!c || a`, and `if c { a } else { false }` is
/// `c && a`.
fn connective(t: &Term) -> Option<(bool, [(&Term, bool); 2])> {
    match t {
        Term::Prim(p @ (Prim::And | Prim::Or), a) if a.len() == 2 => {
            Some((*p == Prim::And, [(&a[0], true), (&a[1], true)]))
        }
        Term::If(c, a, b) => match (&**a, &**b) {
            (Term::Lit(Value::Bool(v)), _) => Some((!v, [(&**c, *v), (&**b, true)])),
            (_, Term::Lit(Value::Bool(v))) => Some((!v, [(&**c, !v), (&**a, true)])),
            _ => None,
        },
        _ => None,
    }
}

impl<'a> Tree<'a> {
    /// The tree of `test`, and the polarity of its root.
    fn of(test: &'a Term) -> (Tree<'a>, bool) {
        let leaf = |term| Node {
            term,
            kind: Kind::Atom,
            key: 0,
            size: 1,
            rank: 0,
        };
        let (root, pol) = strip(test);
        let mut nodes = vec![leaf(root)];
        let mut work = vec![0];
        while let Some(i) = work.pop() {
            let t = nodes[i].term;
            let mut add = |nodes: &mut Vec<Node<'a>>, (u, q): (&'a Term, bool)| {
                nodes.push(leaf(u));
                work.push(nodes.len() - 1);
                (nodes.len() - 1, q)
            };
            nodes[i].kind = if let Term::Lit(Value::Bool(b)) = t {
                Kind::Lit(*b)
            } else if let Some((and, pair)) = connective(t) {
                // The sides of the nest: a side that is the same connective, after De
                // Morgan's laws, is taken apart in turn.
                let mut sides = Vec::new();
                let mut flat = pair.to_vec();
                while let Some((u, q)) = flat.pop() {
                    let (u, s) = strip(u);
                    let q = q == s;
                    match connective(u) {
                        Some((and2, pair2)) if (and2 == q) == and => {
                            flat.extend(pair2.into_iter().map(|(x, px)| (x, px == q)));
                        }
                        _ => sides.push(add(&mut nodes, (u, q))),
                    }
                }
                Kind::Nest(and, sides)
            } else if let Term::If(c, a, b) = t
                && is_test(a)
                && is_test(b)
            {
                Kind::If([c, a, b].map(|x| add(&mut nodes, strip(x))))
            } else {
                Kind::Atom
            };
        }
        // Keys and sizes, each node after the nodes below it.
        for i in (0..nodes.len()).rev() {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            let mut kind = std::mem::replace(&mut nodes[i].kind, Kind::Atom);
            let mut size = 1;
            match &mut kind {
                Kind::Lit(b) => (0u8, *b).hash(&mut h),
                Kind::Atom => (1u8, nodes[i].term.to_string()).hash(&mut h),
                Kind::Nest(and, sides) => {
                    sides.sort_by_key(|&(k, p)| (nodes[k].rank, nodes[k].key, p));
                    sides.dedup_by(|x, y| {
                        x.1 == y.1
                            && nodes[x.0].key == nodes[y.0].key
                            && nodes[x.0].term == nodes[y.0].term
                    });
                    (2u8, *and).hash(&mut h);
                    for &(k, p) in sides.iter() {
                        (nodes[k].key, p).hash(&mut h);
                        size += nodes[k].size;
                    }
                }
                Kind::If(arms) => {
                    3u8.hash(&mut h);
                    for &(k, p) in arms.iter() {
                        (nodes[k].key, p).hash(&mut h);
                        size += nodes[k].size;
                    }
                }
            }
            nodes[i].kind = kind;
            nodes[i].key = h.finish();
            nodes[i].size = size;
            nodes[i].rank = rank(&nodes[i]);
        }
        (Tree { nodes }, pol)
    }

    /// The test of node `n` with each nest written as `&&` or `||` over its sides, nested in a
    /// balanced way, and each `if` with a boolean arm as its connective: a term the size of the
    /// node's subtree, and of depth logarithmic in the length of each nest.
    fn term_at(&self, n: usize) -> Term {
        fn signed(t: Term, pol: bool) -> Term {
            if pol {
                t
            } else {
                Term::Prim(Prim::Not, vec![t])
            }
        }
        // The nodes below `n`, each once: a node is a side or an arm of one node.
        let mut below = vec![n];
        let mut at = 0;
        while let Some(&i) = below.get(at) {
            match &self.nodes[i].kind {
                Kind::Nest(_, sides) => below.extend(sides.iter().map(|s| s.0)),
                Kind::If(arms) => below.extend(arms.iter().map(|s| s.0)),
                Kind::Lit(_) | Kind::Atom => {}
            }
            at += 1;
        }
        // Each node after the nodes below it, which come after it in the tree.
        below.sort_unstable();
        let mut terms: BTreeMap<usize, Term> = BTreeMap::new();
        for &i in below.iter().rev() {
            let node = &self.nodes[i];
            let mut take = |(k, p): (usize, bool)| {
                signed(terms.remove(&k).expect("a node below is built first"), p)
            };
            let t = match &node.kind {
                Kind::Lit(_) | Kind::Atom => node.term.clone(),
                Kind::Nest(and, sides) => {
                    let p = if *and { Prim::And } else { Prim::Or };
                    let mut level: Vec<Term> = sides.iter().map(|&s| take(s)).collect();
                    while level.len() > 1 {
                        let mut it = std::mem::take(&mut level).into_iter();
                        while let Some(l) = it.next() {
                            level.push(match it.next() {
                                Some(r) => Term::Prim(p, vec![l, r]),
                                None => l,
                            });
                        }
                    }
                    level.pop().expect("a nest has a side")
                }
                Kind::If([c, a, b]) => {
                    let [c, a, b] = [*c, *a, *b].map(|s| Arc::new(take(s)));
                    Term::If(c, a, b)
                }
            };
            terms.insert(i, t);
        }
        terms.remove(&n).expect("the node is built")
    }

    /// Whether node `n` is split into cases under some value: a nest or an `if`.
    fn splits(&self, n: usize) -> bool {
        matches!(self.nodes[n].kind, Kind::Nest(..) | Kind::If(_))
    }
}

/// The join of `cases`, each reduced, in pairs, so that no case is copied through more than
/// `log k` joins of `k` cases. A join that is joined again is reduced first; the last is left
/// as it is.
fn join_cases(mut cases: Vec<Scope>) -> Scope {
    while cases.len() > 1 {
        let last = cases.len() == 2;
        let mut it = std::mem::take(&mut cases).into_iter();
        while let Some(l) = it.next() {
            cases.push(match it.next() {
                Some(r) => {
                    let mut j = l.join(&r);
                    if !last {
                        j.reduce();
                    }
                    j
                }
                None => l,
            });
        }
    }
    cases.pop().expect("a test has a case")
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
            p.meet_ints(IntervalSet::single(*n), prem);
            p.cell.congruence.meet(&Congruence::single(*n), prem);
        }
        return;
    }
    if let Some(lit) = Type::lit(v) {
        p.ty.meet(&!&lit, prem);
    }
    if let Value::Int(n) = v {
        let x = IntervalSet::single(*n).complement_in(p.ints());
        p.meet_ints(x, prem);
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
    on_stack(|| forward_in(e, scope))
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
            let u = scope.bind(x, p, v);
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
    on_stack(|| {
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
            let u = scope.bind(x, p, e);
            walk(b, scope, out, count);
            scope.unbind(u);
        }
        Term::If(c, a, b) => {
            let at = FactAddress {
                node: NodeAddress(Vector::unit(Position::root().child(*count))),
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
