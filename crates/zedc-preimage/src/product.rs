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
//!   bounded integer names' intervals and classes meets their written constraints. One point
//!   that meets them is kept; a constraint new since the last reduction, or on a name that
//!   has changed, is searched over its names the point does not give ([`witness`]), and only
//!   when that finds nothing is the group of constraints that share names with it searched
//!   whole (`Scope::enumerate_exactly`). Nothing lists the points, so the scope stays the
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
use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap};
use std::fmt;
use std::sync::Arc;

use zed_kernel::frames::{Deep, Stack};
use zed_kernel::print;
use zed_kernel::provenance::{FactAddress, NodeAddress, Position, Vector};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Prim, Shared, Term, Value, World, on_stack};

use super::preimage::{
    Classes, Demand, Domains, LetIn, LetPa, Lets, follow_own, let_preimage, let_summary, preimage,
    relations, witness,
};
use zedc_int::int::Int;
use zedc_lattice::affine::Bounds;
use zedc_lattice::cell::{Cell, Entry, Premise, Premises};
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::landmarks::Landmarks;
use zedc_lattice::lattice::{Congruence, FiniteSet, Lattice};
use zedc_lattice::revision::{self, Op, reduce_congruence};
use zedc_presburger::conjuncts::{self, BlockId, Conjuncts, Edge, Uses};
use zedc_presburger::hull::Hull;
use zedc_presburger::presburger::{self, Atom, Con, Formula, Lin, Rel};
use zedc_stage::defs::written_name;
use zedc_stage::stage;

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
            Value::Int(n) => {
                self.ints().contains(*n) && self.cell.congruence.element.contains(&Num::from(*n))
            }
            Value::Big(n) => {
                let n = Num::from(&**n);
                self.ints().contains_end(&End::Fin(n.clone()))
                    && self.cell.congruence.element.contains(&n)
            }
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
                            Value::Int(n) => Some((End::of(*n), End::of(*n))),
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
            // COMPLEXITY.md row C5. A complete solution would let the type language hold
            // integer ranges, so that the interval enters the type without listing.
            let x = self.ints();
            let vs: Option<Vec<Value>> = match self.ty.element.ints_listed() {
                Some(vs) => Some(
                    vs.into_iter()
                        .filter(|v| !matches!(v, Value::Int(n) if !x.contains(*n)))
                        .collect(),
                ),
                None => {
                    let most = Num::from(2 * x.pieces().len() as i128);
                    let size = x.pieces().iter().try_fold(Num::ZERO, |n, p| match p {
                        (End::Fin(a), End::Fin(b)) => Some(&(&n + &(b - a)) + &Num::ONE),
                        _ => None,
                    });
                    size.filter(|n| *n <= most).map(|_| {
                        let mut out = Vec::new();
                        for p in x.pieces() {
                            let (End::Fin(a), End::Fin(b)) = p else {
                                unreachable!("every piece is finite")
                            };
                            let mut v = a.clone();
                            while v <= *b {
                                out.push(Value::from(&v));
                                v = &v + &Num::ONE;
                            }
                        }
                        out
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
        // A finite set already held is kept where the type holds each member, so the type's
        // values are not listed: the cost is one membership test per member. With no finite
        // set, the type's values become it, and every one is listed, since the set holds them
        // all (COMPLEXITY.md row S34).
        if self.ty.element.finite() {
            let ty = &self.ty.element;
            let kept = match &self.cell.finite.element {
                FiniteSet::Set(vs) => FiniteSet::of(vs.iter().filter(|v| ty.contains(v)).cloned()),
                FiniteSet::Top => {
                    FiniteSet::of(ty.each_value().expect("a finite type lists its values"))
                }
            };
            self.cell.finite.meet(&kept, &prem);
        }
        if let Some(vs) = self.ty.element.ints_listed()
            && !vs.is_empty()
            && self.ty.element.subtype(&int)
        {
            let ints = IntervalSet::from_pieces(
                vs.iter()
                    .filter_map(|v| match v {
                        Value::Int(n) => Some((End::of(*n), End::of(*n))),
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
    /// Under `@exact`, a point that meets the written constraints the last enumeration took: a
    /// value for each open name of each group of them whose search found a point, and none for
    /// the names of a group whose search gave no answer (`Scope::enumerate_exactly`).
    pub exactly: imbl::OrdMap<Arc<str>, Num>,
    /// Each question the integer solver left undecided while this scope was narrowed or
    /// projected, with the constraint it was asked of and how the scope came to ask it; each
    /// one leaves the scope sound but wider than it could be. [`Scope::warnings`] reports them.
    ///
    /// Complexity tradeoff: a refused question (`presburger::Refusal`, whose costs and
    /// triggers are documented where each is raised) leaves the relation's narrowing out, so
    /// the scope is wider, and a warning names each one ([`Scope::warnings`]). Why: deciding
    /// every question needs a complete Presburger procedure, exponential in the worst case.
    /// Trigger: a test or a part of the relation whose question is refused. Tests:
    /// `l01_39_reduced_product::refused::a_refused_test_gives_one_warning_at_its_test`,
    /// `…::a_refused_test_through_a_helper_names_the_test_and_its_outcome`,
    /// `…::a_refused_projection_onto_each_name_gives_one_warning_for_each`,
    /// `…::two_refused_arms_joined_give_both_warnings_in_one_order`,
    /// `…::warnings_of_many_refused_tests_scale`. COMPLEXITY.md rows S18 (the solver) and S28
    /// (this report). A complete solution would decide every question (see `presburger`).
    pub refusals: imbl::OrdSet<Refused>,
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
    /// A point of the difference constraints of the trees of blocks whose bounds come from
    /// shortest paths ([`Scope::shortest`]), kept as their conjuncts come.
    potential: Potential,
    /// Whether a move of a hub leaves its stars' leaves to be settled when read
    /// ([`Scope::lazy`]).
    lazy: bool,
}

/// A name's `let` binding in a [`Scope`].
#[derive(Clone, PartialEq, Debug)]
struct Binding {
    /// The order of the binding: a binding made later has a larger one.
    order: u64,
    /// The lambda the name is bound to, when it is one.
    function: Option<Shared>,
    /// The summary of the integer the name is bound to, over its inputs ([`Scope::summary`]).
    summary: Summary,
}

/// The summary of the value of a `let` ([`LetPa`]), with the order of the binding of each input
/// it reads and that input's integers when it was made: it holds while each input is that
/// binding and its integers lie within these ([`Scope::holds`]). A cache, equal in every
/// binding, as [`Reduced`] is.
#[derive(Clone, Default)]
struct Summary(Option<(LetPa, Vec<Input>)>);

/// An input of a [`Summary`]: its name, the order of its binding, and its integers when the
/// summary was made.
type Input = (Arc<str>, Option<u64>, IntervalSet);

impl PartialEq for Summary {
    fn eq(&self, _: &Summary) -> bool {
        true
    }
}

impl fmt::Debug for Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("..")
    }
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

/// A value of names at which every difference constraint among them holds: under it no edge
/// has a negative reduced weight, so a Dijkstra search finds the bounds of a tree of blocks
/// projected by shortest paths ([`Scope::shortest`]). It holds at every edge of the relation
/// as of its last projection, except the edges of names it lacks: each edge added is put in
/// it at the next projection, whichever way its tree is projected ([`Scope::repair`]), and a
/// projection of every block ([`Due::All`]) empties it. A cache, equal in every scope, and
/// checked at every edge it is read at.
#[derive(Clone, Default)]
struct Potential(imbl::OrdMap<Arc<str>, Int>);

impl PartialEq for Potential {
    fn eq(&self, _: &Potential) -> bool {
        true
    }
}

impl fmt::Debug for Potential {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("..")
    }
}

/// What has changed since the last projection, for the trees of blocks projected by shortest
/// paths ([`Scope::shortest`]).
#[derive(Default)]
struct Seeds {
    /// The names whose products changed, those of the conjuncts added, those of the stars
    /// that went or changed with their conjuncts, and those of each conjunct removed from a
    /// tree not of difference constraints and bounds alone, with those of its block.
    names: BTreeSet<Arc<str>>,
    /// The conjuncts added, and those of the stars that went or changed, which may now be in
    /// the forest.
    added: BTreeSet<Arc<Formula>>,
    /// The seeds whose tree at the last projection held a conjunct other than a difference
    /// constraint or a bound, or a name with holes or a class: their bounds may be no fixed
    /// point of the difference constraints alone.
    unsure: BTreeSet<Arc<str>>,
}

/// What [`Scope::shortest`] found.
enum Shortest {
    /// The names whose intervals it moved.
    Moved(Vec<Arc<str>>),
    /// No point meets the constraints: a negative cycle, or a name whose least bound passed
    /// its greatest, which it names.
    Bottom(Arc<str>),
}

/// Why [`Scope::shortest`] left a tree to be projected block by block.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Fall {
    /// The potential lacks a name it reads, as after a projection of every block, or an edge
    /// it reads has a negative reduced weight under it: it is found again after
    /// ([`Scope::reseed`]).
    Potential,
    /// A name it reads has holes or a class, or no product.
    Name,
    /// A seed was in a tree of other conjuncts at the last projection ([`Seeds::unsure`]).
    Unsure,
}

/// The edges of tree `t` of the forest at `name`, each with its conjunct and whether it is the
/// conjunct's back edge ([`conjuncts::edges`]); a bound is an edge to or from no name. A
/// conjunct other than a difference constraint or a bound has none: the potential is kept for
/// the edges of every tree ([`Scope::repair`]), and only a tree of edges alone is projected by
/// shortest paths.
fn tree_edges(relation: &Conjuncts, t: BlockId, name: &str) -> Vec<(Arc<Formula>, bool, Edge)> {
    let blocks = relation.blocks();
    let mut out = Vec::new();
    for g in relation.mentioning(name) {
        if !blocks
            .of(g)
            .is_some_and(|b| !blocks.is_apart(b) && blocks.tree(b) == t)
        {
            continue;
        }
        let Some((e, back)) = conjuncts::edges(g) else {
            continue;
        };
        out.push((g.clone(), false, e));
        if let Some(e) = back {
            out.push((g.clone(), true, e));
        }
    }
    out
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
/// that a part costs its conjunct and not the constraints. Third, the leaf of the star whose
/// block the part is projected in, `None` in the forest: a conjunct among the hubs of a star
/// is a part of the star's block and of the hubs' block, each with other constraints and
/// names, and one key for both made each block find the other's snapshot there and project
/// every such part again at each test (item NARROW-lazy-settle).
pub type PartKey = (Formula, Option<Arc<[Con]>>, Option<Arc<str>>);

/// Each of `conjuncts` that is not a constraint, with the constraints, and the constraints
/// alone when there are any; each part with its key, the conjunct it is projected for, or the
/// constraints for theirs, in the star of leaf `leaf` if any.
fn split<'a>(
    conjuncts: impl Iterator<Item = &'a Formula>,
    leaf: Option<&Arc<str>>,
) -> Vec<(PartKey, Formula)> {
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
                (g.clone(), eqs.clone(), leaf.cloned()),
                Formula::and(vec![g.clone(), base.clone()]),
            )
        })
        .collect();
    if base != Formula::top() {
        parts.push(((base.clone(), eqs, leaf.cloned()), base));
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
    /// The leaf, when the block is a star ([`Conjuncts::star`]).
    leaf: Option<Arc<str>>,
}

impl Block {
    /// Block `b` of `relation`, with the conjuncts among its hubs when it is a star of two
    /// hubs or more ([`Conjuncts::core`]).
    fn of(relation: &Conjuncts, b: BlockId) -> Block {
        let gs = relation.core(b);
        let names: BTreeSet<Arc<str>> = gs.iter().flat_map(|g| syms(g)).collect();
        let leaf = names.iter().find(|x| relation.star(x) == Some(b)).cloned();
        Block {
            parts: split(gs.iter().map(|g| &**g), leaf.as_ref()),
            names: names.into_iter().collect(),
            leaf,
        }
    }
}

/// The blocks a projection looks at.
enum Due {
    /// Every block.
    All,
    /// These blocks, with what changed since the last projection.
    Blocks(BTreeSet<BlockId>, Seeds),
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

/// A question the integer solver left undecided while a scope was narrowed or projected: the
/// constraint it was asked of, as printed, how the scope came to ask it, and the cause. The
/// order of the fields is the order of the reports: by constraint, then by how it was asked,
/// then by cause, so that it does not depend on the order the questions were met in.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Refused {
    /// The test or the part of the linear relation the question was asked of.
    pub constraint: Arc<str>,
    /// How the scope came to ask it.
    pub asked: Asked,
    /// Why the solver left it undecided.
    pub cause: presburger::Refusal,
}

/// How a scope came to ask a question of the integer solver.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Asked {
    /// The preimage of a test's outcome, to narrow the test's names.
    Test {
        /// The outcome assumed.
        outcome: bool,
    },
    /// The projection of a part of the linear relation onto each name it mentions.
    Projection,
    /// The same projection, which left out a disjunction whose projection was refused.
    Disjunct,
    /// The same projection onto one name.
    Onto(Arc<str>),
}

/// A warning about a scope: its message, then each step of its derivation in order.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Warning {
    /// What the warning says.
    pub message: String,
    /// Each constraint and step that led to it, in the order the compiler met them.
    pub steps: Vec<String>,
}

impl fmt::Display for Warning {
    /// `warning: <message>`, then each step numbered on its own line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "warning: {}", self.message)?;
        for (i, s) in self.steps.iter().enumerate() {
            write!(f, "\n  [{}] {s}", i + 1)?;
        }
        Ok(())
    }
}

impl Refused {
    /// The warning that reports this refusal, with its derivation.
    fn warning(&self) -> Warning {
        let c = &self.constraint;
        let cause = &self.cause;
        let (given, asked, kept) = match &self.asked {
            Asked::Test { outcome } => (
                format!("the test `{c}` is assumed {outcome}"),
                format!("whether its names can take each value is not decided: {cause}"),
                "the names of the test are not narrowed by it",
            ),
            Asked::Projection => (
                format!("the constraints `{c}` hold in the scope"),
                format!("their projection onto their names is not decided: {cause}"),
                "the names of the constraints are not narrowed by them",
            ),
            Asked::Disjunct => (
                format!("the constraints `{c}` hold in the scope"),
                format!("a disjunction among them is left out of their projection: {cause}"),
                "the names of the constraints are narrowed without that disjunction",
            ),
            Asked::Onto(n) => (
                format!("the constraints `{c}` hold in the scope"),
                format!("their projection onto `{n}` is not decided: {cause}"),
                "that name is not narrowed by them",
            ),
        };
        Warning {
            message: "the scope is wider than its constraints make it".to_string(),
            steps: vec![given, asked, kept.to_string()],
        }
    }
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
            potential: Potential::default(),
            lazy: false,
        };
        s.reduce();
        s
    }

    /// This scope, made lazy: a test that moves a hub of a star ([`Conjuncts::star`]) leaves
    /// the star's leaf as it was, and a read settles a leaf it needs ([`Scope::settled`]), so
    /// that `k` tests on a hub of `k` stars cost `k` narrowings and not `k²` projections.
    /// Every pass that reads names settles them first: a test settles its own names, a join
    /// the leaves its two sides may differ at, and a `bind` of a hub its leaves;
    /// [`Scope::get`], [`Scope::statics`] and [`Scope::contains`] read names as held, so a
    /// caller of these settles first ([`Scope::eager_on`]).
    ///
    /// The invariant: a lazy scope differs from the eager scope of the same tests only at
    /// stale leaves, the leaves whose star was last projected at other intervals or classes
    /// of its names than they now have, or with other conjuncts among its hubs
    /// ([`Conjuncts::core`]), and there settling the leaf, projecting its star with those
    /// conjuncts and reducing as [`Scope::reduce`] does, gives the eager product. No written constraint
    /// holds of a leaf, so its product reaches no other name but through its star, whose
    /// projection onto its hubs is a bound on each alone, through the leaf's greatest or least
    /// member, which a cut of the leaf by the hubs' moves keeps, so no hub moves; and the cut
    /// is a half-line that holds that member, so it empties no leaf, and the scope is bottom
    /// exactly when the eager one is. A star that goes or changes makes its leaf's conjuncts
    /// due at the next projection, which settles the leaf.
    pub fn lazy(mut self) -> Scope {
        self.lazy = true;
        self
    }

    /// The stars of the leaves among `names` that are stale ([`Scope::lazy`]), as the
    /// blocks to project.
    fn stale<'a>(&self, names: impl IntoIterator<Item = &'a Arc<str>>) -> Vec<Block> {
        let mut seen: BTreeSet<BlockId> = BTreeSet::new();
        let mut out = Vec::new();
        for x in names {
            let Some(b) = self.relation.star(x) else {
                continue;
            };
            if !seen.insert(b) {
                continue;
            }
            let block = Block::of(&self.relation, b);
            if block
                .parts
                .iter()
                .any(|(key, g)| self.projected.get(key) != Some(&self.snapshot(&syms(g))))
            {
                out.push(block);
            }
        }
        out
    }

    /// Settles the stale leaves among `names` ([`Scope::lazy`]): projects each one's star,
    /// then reduces, which costs the leaves settled.
    pub fn settle<'a>(&mut self, names: impl IntoIterator<Item = &'a Arc<str>>) {
        if !self.lazy || self.bottom {
            return;
        }
        let blocks = self.stale(names);
        if blocks.is_empty() {
            return;
        }
        for b in &blocks {
            self.project_block(b);
        }
        self.reduce_with(false);
        debug_assert!(!self.bottom, "settling a leaf emptied a scope");
    }

    /// The product of `name` as the eager scope has it: [`Scope::get`] of the scope with the
    /// name settled ([`Scope::lazy`]), on a copy, in O(log n) and the leaf's projection.
    pub fn settled(&self, name: &Arc<str>) -> Product {
        if self.lazy && !self.bottom && !self.stale([name]).is_empty() {
            let mut s = self.clone();
            s.settle([name]);
            return s.get(name);
        }
        self.get(name)
    }

    /// Settles the names `term` reads and makes the scope eager from here, for a pass that
    /// reads it through [`Scope::get`], as [`forward`] does: a later test that moves a hub
    /// then projects its stars again, and a leaf no read settles is never read.
    pub fn eager_on(&mut self, term: &Term) {
        let names = stage::free(term);
        self.settle(&names);
        self.lazy = false;
    }

    /// Settles the names `test` reads, those of the functions it calls among them, before a
    /// narrowing reads them ([`Scope::lazy`]).
    fn settle_test(&mut self, test: &Term) {
        if !self.lazy || self.bottom {
            return;
        }
        let mut names = stage::free(test);
        if let Some(closed) = self.close(test) {
            names.extend(stage::free(&closed));
        }
        self.settle(&names);
    }

    /// The scope of a `let` body that binds `x` to `p`, in place. A name already in scope is
    /// forgotten first: the relation is weakened to say nothing of it and the written
    /// constraints on it go, since they hold of the value it shadows. Nothing else in the
    /// scope then mentions `x`, so `p`'s own reductions are the whole reduction, and the
    /// scope is not copied unless `x` shadows a name or `p` is empty. `e` is the bound term,
    /// kept when it is a lambda, so that a test calling `x` is read through the call.
    pub fn bind(&mut self, x: &Arc<str>, p: Product, e: &Shared) -> Unbind {
        self.bind_with(x, p, e, None)
    }

    /// [`Scope::bind`] with the summary `s` of the bound value ([`let_summary`]), made over the
    /// integers `doms` of the inputs it reads, in place of the summary of `e` this scope would
    /// make: for a caller that summarizes each binding once and binds it in many scopes, as
    /// the checker binds a name in the scope of each test that reads it. The summary holds
    /// here while each input is the binding it now is and its integers lie within those of
    /// `doms` (`Scope::holds`). Where it holds, `p`'s integers are met with the summary's
    /// values over the inputs' integers here ([`LetPa::image`]): with `y = n + 1`, `y` bound
    /// where a test has narrowed `n` to `0..=3` lies in `1..=4`. `O(k)` for `k` inputs, beside
    /// the binding.
    pub fn bind_summarized(
        &mut self,
        x: &Arc<str>,
        p: Product,
        e: &Shared,
        s: &LetPa,
        doms: &Domains,
    ) -> Unbind {
        self.bind_with(x, p, e, Some((s, doms)))
    }

    /// [`Scope::bind`] of `x` to `p` met with `image`, the integers a summary of its value takes
    /// where the inputs it reads are as this scope has them ([`LetPa::image_shifted`]), on the
    /// `premises` of those inputs; the binding keeps no summary of the value. For a caller
    /// that reads the scope once, through no test, and pays for the inputs this scope has,
    /// not for all `k` of the summary ([`Scope::bind_summarized`], `O(k)`).
    pub fn bind_within(
        &mut self,
        x: &Arc<str>,
        mut p: Product,
        e: &Shared,
        image: IntervalSet,
        premises: &Premises,
    ) -> Unbind {
        if self.summarizes(&p) {
            p.meet_ints(image, premises);
        }
        self.bind(x, p, e)
    }

    fn bind_with(
        &mut self,
        x: &Arc<str>,
        mut p: Product,
        e: &Shared,
        given: Option<(&LetPa, &Domains)>,
    ) -> Unbind {
        let summary = match given {
            None => Summary::default(),
            Some((s, doms)) if self.summarizes(&p) => self.held(s.clone(), doms),
            Some(_) => Summary::default(),
        };
        if let Summary(Some((s, inputs))) = &summary
            && self.holds(inputs)
            && let Some(image) = s.image(|v| self.names.get(v).map(Product::ints))
        {
            let mut premises = Premises::new();
            for (v, _, _) in inputs {
                premises.extend(&self.names[v].premises());
            }
            p.meet_ints(image, &premises);
        }
        loop {
            let before = p.clone();
            p.reduce_domains();
            debug_assert!(p.leq(&before), "a reduction rose: {before:?} to {p:?}");
            if p == before {
                break;
            }
        }
        let summary = match given {
            None => self.summarize(e, &p),
            Some(_) => summary,
        };
        let binding = Binding {
            order: self.clock,
            function: matches!(**e, Term::Lam(..)).then(|| e.clone()),
            summary,
        };
        self.clock += 1;
        if !self.bottom && !p.is_empty() && !self.names.contains_key(x) {
            let before = self.names.clone();
            self.names.insert(x.clone(), p);
            self.bindings.insert(x.clone(), binding);
            self.seen_fresh(x, &before);
            return Unbind::Fresh(x.clone());
        }
        let saved = Unbind::Saved(Box::new(self.clone()));
        if self.bottom {
            return saved;
        }
        // The stars that forgetting `x` takes or changes, and their leaves keep what they
        // have: those at `x` as a hub, and those whose hub it leaves with too few conjuncts
        // or with one no star holds. No reduction follows to settle them, so they are settled
        // first, against the relation they were stars of.
        let mut after = self.relation.clone();
        after.forget(x);
        let leaves: Vec<Arc<str>> = self
            .relation
            .stars()
            .diff(after.stars())
            .filter_map(|d| match d {
                DiffItem::Remove(n, _) | DiffItem::Update { old: (n, _), .. } => Some(n.clone()),
                DiffItem::Add(..) => None,
            })
            .filter(|n| n != x)
            .collect();
        if leaves.is_empty() {
            self.relation = after;
        } else {
            // Settling reads the bounds of the names, which may change the stars: the
            // relation is forgotten again from where it then is.
            self.settle(&leaves);
            self.relation.forget(x);
        }
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
                let before = self.names.clone();
                self.names.remove(&x);
                self.bindings.remove(&x);
                self.seen_fresh(&x, &before);
            }
            Unbind::Saved(s) => *self = *s,
        }
    }

    /// Tells the caches of the last reduction, projection and enumeration that the fresh name
    /// `x` came into scope or left it, the names having been `before`. A fresh name is
    /// mentioned by no conjunct and no written constraint, and [`Scope::bind`] reduced its
    /// product to its fixed point, so a reduction would only have synchronized its bounds: the
    /// caches take it as reduced, and the next reduction costs the names that changed since,
    /// not every name bound since the last reduction of this scope. A walk reduces the scope
    /// of each test (a clone), never the scope it binds in, so without this a block of `d`
    /// bindings with a test in each cost `Θ(d²)` (repair of PA-let-block).
    ///
    /// Each cache is rebuilt from the names as they now are, with its own entries where it
    /// differed from `before`: a cache that shares the names' persistent nodes is compared
    /// with them in the entries that differ ([`changed`]), and one that took `x` by its own
    /// insertion would share none of them after a few bindings. The cost is the entries that
    /// differ, each `O(log n)`.
    fn seen_fresh(&mut self, x: &Arc<str>, before: &imbl::OrdMap<Arc<str>, Product>) {
        let now = &self.names;
        let rebase = |cache: &mut imbl::OrdMap<Arc<str>, Product>| {
            if cache.ptr_eq(before) {
                *cache = now.clone();
                return;
            }
            let mut out = now.clone();
            for d in cache.diff(before) {
                match d {
                    DiffItem::Add(n, _) if n != x => _ = out.remove(n),
                    DiffItem::Remove(n, p) | DiffItem::Update { old: (n, p), .. } if n != x => {
                        _ = out.insert(n.clone(), p.clone())
                    }
                    _ => {}
                }
            }
            *cache = out;
        };
        rebase(&mut self.reduced.0);
        if let Some((names, _)) = &mut self.seen.projection {
            rebase(names);
        }
        if let Some((names, _, _)) = &mut self.seen.enumeration {
            rebase(names);
        }
        self.sync_bounds([x]);
    }

    /// The summary of `e`, an integer bound to a name of product `p` ([`let_summary`]), over
    /// the names it reads: those bound by `let`s with a summary that holds are read through it,
    /// and the others are inputs. Costs `e`'s size and its names' domains, not the summaries
    /// of the names it reads.
    // Complexity tradeoff: a value this scope summarizes reads one input; one over several
    // (`x = n + k`) gets no summary here, so a test of `x` in a walk narrows neither `n` nor
    // `k` through it, where the checker's summaries ([`Scope::bind_summarized`]) do. What is
    // given up is that narrowing in `product::walk`. Why: a summary over `k` inputs costs
    // `O(k)` each time it is checked to hold ([`Scope::summary`]), and the walk binds and reads
    // names in the order of the term, with no memo across bindings to bound it, so a chain of
    // `d` sums over `d` inputs would cost `Θ(d²)`. Trigger: a value over two inputs or more,
    // bound by `let` in a term the walk reads. Test:
    // `l01_39a_bit_words::narrowing::a_value_over_two_inputs_narrows_both`, which shows the
    // checker's. COMPLEXITY.md row PA-let-narrow. A complete solution would keep each
    // summary's inputs' orders and domains in a persistent map shared with its parts'.
    fn summarize(&self, e: &Term, p: &Product) -> Summary {
        if !self.summarizes(p) {
            return Summary::default();
        }
        let (inputs, lets) = self.inputs_and_lets(&stage::free(e));
        match let_summary(e, &inputs, lets) {
            Some(s) if s.vars().len() <= 1 => self.held(s, &inputs),
            _ => Summary::default(),
        }
    }

    /// Whether a name of product `p` bound here keeps a summary: an integer in a reachable
    /// scope.
    fn summarizes(&self, p: &Product) -> bool {
        !self.bottom && p.ty.element.subtype(&Type::int())
    }

    /// The summary `s`, made over the integers `doms` of the inputs it reads, as a binding
    /// here keeps it: with the order of each input's binding ([`Scope::summary`]); none when
    /// an input it reads has no integers in `doms`. `O(k log k)` for `k` inputs.
    fn held(&self, s: LetPa, doms: &Domains) -> Summary {
        let inputs: Option<Vec<_>> = s
            .vars()
            .iter()
            .map(|v| {
                let order = self.bindings.get(v).map(|b| b.order);
                Some((v.clone(), order, doms.get(v)?.clone()))
            })
            .collect();
        Summary(inputs.map(|inputs| (s, inputs)))
    }

    /// Whether the summary `s` held with `inputs` ([`Scope::held`]) holds here: each input it
    /// reads is still the binding it was made over, and that input's integers lie within those
    /// it was made over (a scope's integers only narrow while a name is bound, but a name bound
    /// again is another binding). `O(k)` for `k` inputs.
    fn holds(&self, inputs: &[Input]) -> bool {
        inputs.iter().all(|(v, order, dom)| {
            self.names.get(v).is_some_and(|now| {
                self.bindings.get(v).map(|b| b.order) == *order && now.ints().is_subset(dom)
            })
        })
    }

    /// The summary of the integer `x` is bound to, when it has one and it holds
    /// ([`Scope::holds`]).
    fn summary(&self, x: &Arc<str>) -> Option<LetPa> {
        let (s, inputs) = self.bindings.get(x)?.summary.0.as_ref()?;
        self.holds(inputs).then(|| s.clone())
    }

    /// The integer names of `free`, as inputs over their integers, or, when bound by a `let`
    /// with a summary that holds ([`Scope::summary`]), as names read through it, the inputs it
    /// reads then inputs.
    fn inputs_and_lets(&self, free: &BTreeSet<Arc<str>>) -> (Domains, Lets) {
        let int = Type::int();
        let mut inputs = Domains::new();
        let mut lets = Lets::new();
        for n in free {
            let p = self.get(n);
            if !self.names.contains_key(n) || !p.ty.element.subtype(&int) {
                continue;
            }
            match self.summary(n) {
                Some(summary) => {
                    for v in summary.vars() {
                        inputs.insert(v.clone(), self.get(v).ints().clone());
                    }
                    lets.insert(
                        n.clone(),
                        LetIn {
                            summary,
                            ints: p.ints().clone(),
                        },
                    );
                }
                None => _ = inputs.insert(n.clone(), p.ints().clone()),
            }
        }
        (inputs, lets)
    }

    /// Records `t` as a written constraint that holds.
    pub fn write(&mut self, t: Term) {
        let k = t.to_string();
        self.unwrite(&k);
        let free: Vec<Arc<str>> = stage::free(&t).into_iter().collect();
        for n in &free {
            self.written_by.add(n, &k);
            self.relation.pin(n, true);
        }
        self.written.insert(k, (t, free));
    }

    /// Forgets the written constraint of text `k`.
    fn unwrite(&mut self, k: &str) {
        if let Some((_, free)) = self.written.remove(k) {
            let k = k.to_string();
            for n in &free {
                self.written_by.remove(n, &k);
                if self.written_by.count(n) == 0 {
                    self.relation.pin(n, false);
                }
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
        let mut reached: Vec<(u64, &Arc<str>, &Shared)> = Vec::new();
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
                    Term::Let(n.clone(), f.clone(), Shared::new(body))
                }),
        )
    }

    /// The product of `name`; the top for a name not in scope, and the bottom for any name of
    /// a scope no state reaches, whose names [`Scope::assume_case`] leaves as they were.
    pub fn get(&self, name: &str) -> Product {
        if self.bottom {
            return Product::bottom();
        }
        self.names.get(name).cloned().unwrap_or_else(Product::top)
    }

    /// A warning for each question the integer solver left undecided while this scope was
    /// narrowed or projected, joined scopes included, in the order of [`Refused`]: by
    /// constraint, how it was asked, then cause, whatever order they were met in.
    pub fn warnings(&self) -> Vec<Warning> {
        self.refusals.iter().map(Refused::warning).collect()
    }

    /// Keeps `r`, a question the integer solver left undecided while this scope was narrowed or
    /// projected, once, in O(log k) in the k refusals kept. Every refused test and part of the
    /// relation is kept through here.
    pub fn refuse(&mut self, r: Refused) {
        self.refusals.insert(r);
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
    ///
    /// A lazy scope ([`Scope::lazy`]) first settles, on each side, the leaves the two sides may
    /// differ at: each name they hold differently or a written constraint one holds alone
    /// mentions, each leaf of a star at such a name, and
    /// each name of a conjunct one side holds alone. A stale leaf they do not differ at has one
    /// product, hubs, star and settled product on both sides, so it stays stale in the join,
    /// where settling it gives that product. This costs the leaves at the names that differ,
    /// which the names of an eager join would differ at as well.
    pub fn join(&self, other: &Scope) -> Scope {
        if self.bottom {
            return other.clone();
        }
        if other.bottom {
            return self.clone();
        }
        if !self.lazy && !other.lazy {
            return self.join_settled(other);
        }
        let mut differ: BTreeSet<Arc<str>> = BTreeSet::new();
        for d in self.names.diff(&other.names) {
            let (DiffItem::Add(n, _)
            | DiffItem::Remove(n, _)
            | DiffItem::Update { old: (n, _), .. }) = d;
            differ.insert(n.clone());
        }
        for d in self.relation.set().diff(other.relation.set()) {
            let (imbl::ordset::DiffItem::Add(g) | imbl::ordset::DiffItem::Remove(g)) = d;
            differ.extend(conjuncts::names(g));
        }
        // A written constraint one side holds alone pins its names there and not in the join,
        // which may make one of them a star's leaf there ([`Conjuncts::pin`]).
        for d in self.written.diff(&other.written) {
            let (DiffItem::Add(_, (_, free))
            | DiffItem::Remove(_, (_, free))
            | DiffItem::Update {
                old: (_, (_, free)),
                ..
            }) = d;
            differ.extend(free.iter().cloned());
        }
        let mut leaves = differ.clone();
        for side in [&self.relation, &other.relation] {
            for n in &differ {
                leaves.extend(side.hanging(n).flat_map(|g| conjuncts::names(g)));
            }
        }
        let (mut a, mut b) = (self.clone(), other.clone());
        a.settle(&leaves);
        b.settle(&leaves);
        a.join_settled(&b)
    }

    /// [`Scope::join`] of two sides that differ at no stale leaf.
    fn join_settled(&self, other: &Scope) -> Scope {
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
        let (eqs, near) = conjuncts::reach(
            &[&self.relation, &other.relation],
            seeds.iter().cloned(),
            is_eq,
        );
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
        // The joined names as the relation reads them for its stars ([`Scope::sync_bounds`]):
        // only names among the seeds differ from `self`'s.
        for n in &seeds {
            let (below, above) = sides(&names, n);
            relation.bound(n, below, above);
        }
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
                    if written_by.count(n) == 0 {
                        relation.pin(n, false);
                    }
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
        // This side's point, which goes with this side's last enumeration, kept below as the
        // join's: the constraints on a name the join changed are searched again, and the
        // others hold at it as they did on this side. The other side's values are not mixed
        // in, since this side's constraints need not hold at them.
        let exactly = self.exactly.clone();
        let mut refusals = self.refusals.clone();
        for d in self.refusals.diff(&other.refusals) {
            if let imbl::ordset::DiffItem::Add(r) = d {
                refusals.insert(r.clone());
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
            // It goes with this side's last projection, as `seen` does.
            potential: self.potential.clone(),
            lazy: self.lazy || other.lazy,
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
        s.settle_test(test);
        let plain = plain_test(test, &s);
        s.narrow(plain.as_ref().unwrap_or(test), outcome, premises);
        s.reduce();
        s
    }

    /// [`Scope::assume`] for a scope that is read and not shown: one no state reaches keeps its
    /// names as they were, with `bottom` set, and [`Scope::get`] gives the bottom for each, so
    /// that a test that fails costs what it narrows and not the names in scope. A nest of `k`
    /// tests that each fail in one case, on `k` names, is then `O(k)` narrowings and not
    /// `O(k²)` (`Scope::reduce_case`).
    pub fn assume_case(&self, test: &Term, outcome: bool, premises: &Premises) -> Scope {
        let mut s = self.clone();
        s.settle_test(test);
        let plain = plain_test(test, &s);
        s.narrow(plain.as_ref().unwrap_or(test), outcome, premises);
        s.reduce_case();
        s
    }

    /// Narrows by `test`, read by [`plain_test`], giving `outcome`. The test is read as a
    /// [`Tree`]; when it has cases, the linear relation of the whole test, taken before any
    /// narrowing, is kept with the join of the cases, which keeps only what the cases share.
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
                    s.reduce_case();
                    match heavy {
                        Some((k, p)) => work.push((s, k, v == p)),
                        None => out.push(s),
                    }
                }
                Kind::If([c, a, b]) => {
                    let mut t = s.clone();
                    t.narrow_node(tree, c.0, c.1, prem);
                    t.reduce_case();
                    work.push((t, a.0, v == a.1));
                    s.narrow_node(tree, c.0, !c.1, prem);
                    s.reduce_case();
                    work.push((s, b.0, v == b.1));
                }
                Kind::Lit(_) | Kind::Atom => {
                    s.narrow_node(tree, n, v, prem);
                    s.reduce_case();
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
                self.atom_names(&t, node.term, value, true, prem);
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
        let written = test;
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
        let (exact, inputs, free) = self.atom_names(&t, written, outcome, false, prem);
        // Whether the relation holds the test exactly as a bound on a sum of its names, each
        // of coefficient one or minus one, `x - y + c >= 0` or `x - n - m + c >= 0`, so that
        // the written constraint adds nothing.
        let mut unit = false;
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
            unit = !self.exact && conjuncts::unit_sum(&body);
            self.relation.and(body);
        }
        // The written constraint, unless it is a test of one integer name whose preimage is
        // exact: the name's interval then holds exactly the values that meet it, and
        // enumeration would remove none of them; or a test the relation holds as a bound on a
        // sum of its integer names of coefficients one and minus one: enumerating it, with
        // every name but one of one value each, keeps that name's members on one side of a
        // bound, which projecting the sum gives as well. So a lazy scope ([`Scope::lazy`])
        // has the test as a star's conjunct, and a move of one name reads no text of the
        // tests that relate it to others.
        // Under `@exact`, where written constraints that share a name are enumerated
        // together, it is kept.
        if !(exact && inputs.len() == 1 && free.len() == 1) && !unit {
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
    /// holds no more pieces than one side gives. A refused preimage names the test as
    /// `written`, the test as the program wrote it: neither closed over its helpers nor with
    /// its static names substituted, each binder by its written name.
    fn atom_names(
        &mut self,
        t: &Term,
        written: &Term,
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
                    (Term::Prim(Prim::Mod, m), Term::Lit(r)) if equal => {
                        if let [Term::Var(x), Term::Lit(c)] = &m[..]
                            && let (Some(r), Some(c)) = (int_lit(r), int_lit(c))
                            && !c.is_zero()
                            && let Some(p) = self.names.get_mut(x)
                        {
                            let k = c.abs();
                            if r.signum() < 0 || r >= k {
                                p.ty.meet(&!&Type::int(), prem);
                            } else {
                                p.cell.congruence.meet(&Congruence::new(k, r), prem);
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
            if let Some(cause) = pre.refusal {
                self.refuse(Refused {
                    constraint: print::written(written, written_name).into(),
                    asked: Asked::Test { outcome },
                    cause,
                });
            }
            // The names bound by `let`s read through their summaries: the test narrows the
            // inputs they are computed from as well as the names.
            let (over, lets) = self.inputs_and_lets(&free);
            let through = if lets.is_empty() {
                Domains::new()
            } else {
                let_preimage(t, &over, lets, &Demand::Bool(outcome))
            };
            for (n, d) in pre.domains.iter().chain(&through) {
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
        self.empty_if_bottom();
    }

    /// [`Scope::reduce`] for a case of a test, which is joined or dropped and not shown: a
    /// case that no state reaches keeps its names as they were, with `bottom` set, since
    /// emptying each name costs the names in scope, once for each case that fails.
    fn reduce_case(&mut self) {
        self.reduce_with(false);
    }

    /// [`Scope::reduce`] with every tree of blocks projected as a whole, for the test that
    /// projecting by blocks keeps what this keeps.
    #[doc(hidden)]
    pub fn reduce_whole(&mut self) {
        self.reduce_with(true);
        self.empty_if_bottom();
    }

    /// Empties every name of a scope no state reaches, as a scope that is shown has them.
    fn empty_if_bottom(&mut self) {
        if self.bottom {
            self.names = self
                .names
                .keys()
                .map(|n| (n.clone(), Product::bottom()))
                .collect();
        }
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
            // The names whose bounds may have changed since the last projection, so that the
            // stars it finds are those of the bounds as they are.
            let moved: Vec<Arc<str>> = match &self.seen.projection {
                Some((names, _)) => names
                    .diff(&self.names)
                    .map(|d| match d {
                        DiffItem::Add(n, _)
                        | DiffItem::Remove(n, _)
                        | DiffItem::Update { new: (n, _), .. } => n.clone(),
                    })
                    .collect(),
                None => self.names.keys().cloned().collect(),
            };
            self.sync_bounds(&moved);
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
        let mut seeds = Seeds::default();
        let mut any = false;
        let blocks = self.relation.blocks();
        for d in names.diff(&self.names) {
            let (DiffItem::Add(n, _)
            | DiffItem::Remove(n, _)
            | DiffItem::Update { new: (n, _), .. }) = d;
            any = true;
            seeds.names.insert(n.clone());
            out.extend(
                self.relation
                    .moved(n, self.lazy)
                    .filter_map(|g| blocks.of(g)),
            );
        }
        // A leaf whose star went or changed may be stale ([`Scope::lazy`]) where nothing else
        // makes it due: its conjuncts' blocks now are.
        // An eager scope projects a new star at once, with the conjuncts among its hubs
        // ([`Conjuncts::core`]), so that the classes below hold only stars so projected.
        for d in old.stars().diff(self.relation.stars()) {
            match d {
                DiffItem::Remove(x, _) | DiffItem::Update { new: (x, _), .. } => {
                    any = true;
                    out.extend(self.relation.mentioning(x).filter_map(|g| blocks.of(g)));
                    seeds.names.insert(x.clone());
                    for g in self.relation.mentioning(x) {
                        seeds.names.extend(conjuncts::names(g));
                        seeds.added.insert(g.clone());
                    }
                }
                DiffItem::Add(_, &b) if !self.lazy => {
                    any = true;
                    out.insert(b);
                }
                DiffItem::Add(..) => {}
            }
        }
        // A conjunct among the hubs of a star of two hubs or more is projected with it
        // ([`Conjuncts::core`]): an eager scope projects the stars of each class it is among
        // again, unless the class gives its leaf the same bound as before
        // ([`Scope::same_leaf_bound`]). A lazy one finds the leaf stale when read, since the
        // star's part is keyed by those conjuncts. The star's projection gives the hubs no bound
        // that the hubs' own block lacks: the leaf is unbounded on the side away from them, and
        // the conjuncts among them are parts of both blocks, keyed apart ([`PartKey`]), so the
        // two scopes hold the hubs alike (item NARROW-lazy-settle).
        let mut classes: BTreeSet<conjuncts::Class> = BTreeSet::new();
        let mut gone: Vec<Arc<Formula>> = Vec::new();
        for d in old.set().diff(self.relation.set()) {
            any = true;
            match d {
                imbl::ordset::DiffItem::Add(g) => {
                    out.extend(blocks.of(g));
                    seeds.names.extend(conjuncts::names(g));
                    seeds.added.insert(g.clone());
                    if !self.lazy {
                        classes.extend(self.relation.classed(g));
                    }
                }
                imbl::ordset::DiffItem::Remove(g) => {
                    if !self.lazy {
                        classes.extend(old.classed(g));
                    }
                    // A conjunct gone from a tree of difference constraints and bounds leaves
                    // the bounds there a fixed point of those left. From any other tree, whose
                    // projection may have been refused, its names and its block's are made
                    // seeds, and so unsure, below.
                    let names = conjuncts::names(g);
                    let was = old.blocks().of(g);
                    if names.iter().any(|n| !old.differences_only_at(n)) {
                        seeds.names.extend(names);
                        let mates = was.into_iter().flat_map(|b| old.blocks().members(b));
                        seeds.names.extend(mates.flat_map(|h| conjuncts::names(h)));
                    }
                    let mates = was.into_iter().flat_map(|b| old.blocks().members(b));
                    out.extend(mates.filter_map(|h| blocks.of(h)));
                    gone.push(g.clone());
                }
            }
        }
        // A class with no star now held only stars that went or changed, made due above; a
        // star of a class that had none before is new, made due above too. The stars of a class
        // with stars before and now are the same stars, each projected with the class's
        // conjuncts as they were.
        //
        // Complexity tradeoff: when the class's bound on its leaf changes, or is not shown to
        // stay ([`Scope::same_leaf_bound`]), every star of the class is projected again, though
        // a leaf whose own product lies within both bounds keeps its product. Why: finding only
        // the leaves whose own bound lies past the class's needs them ordered by their own
        // products, which every narrowing of a leaf would have to keep. Trigger: a test among
        // the hubs of `k` stars of one class that moves the class's bound, or one of the cases
        // `same_leaf_bound` leaves out: `k` projections, as the `k` leaves that move cost.
        // Test: `l01_39_reduced_product::scaling::tests_among_the_hubs_of_many_stars_narrow_an_eager_scope_in_linear_time`.
        // COMPLEXITY.md row C26. A complete solution keeps the leaves of each class ordered by
        // their own bound on the side the class bounds, in each scope, and projects only those
        // the class's new bound cuts.
        for c in &classes {
            let Some(now) = self.relation.class_core(c) else {
                continue;
            };
            if old
                .class_core(c)
                .is_some_and(|then| self.same_leaf_bound(&then, &now))
            {
                continue;
            }
            out.extend(
                self.relation
                    .class_leaves(c)
                    .filter_map(|x| self.relation.star(x)),
            );
        }
        seeds.unsure = seeds
            .names
            .iter()
            .filter(|n| !old.differences_only_at(n))
            .cloned()
            .collect();
        for g in gone {
            let keys: Vec<PartKey> = self
                .projected
                .range((Formula::clone(&g), None, None)..)
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
        Some(Due::Blocks(out, seeds))
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
        // A projection of every block puts no edge in the potential, which may then fail at
        // the edges added since the last projection: it is found again where it is read.
        if matches!(due, Due::All) {
            self.potential = Potential::default();
        }
        if self.relation.is_top() {
            self.projected = imbl::OrdMap::new();
            return;
        }
        if whole {
            // The conjuncts linked by shared atoms, found by a union-find over the atoms, not
            // by the trees of blocks: a star is a tree of its own ([`Conjuncts::star`]), and
            // this projection is the one the blocks' is checked against.
            let mut index: BTreeMap<Atom, usize> = BTreeMap::new();
            let mut parent: Vec<usize> = Vec::new();
            fn root(parent: &mut [usize], mut x: usize) -> usize {
                while parent[x] != x {
                    parent[x] = parent[parent[x]];
                    x = parent[x];
                }
                x
            }
            let mut first: Vec<Option<usize>> = Vec::new();
            for g in self.relation.set() {
                let mut atoms = g.atoms();
                atoms.extend(conjuncts::names(g).into_iter().map(Atom::Sym));
                let mut at: Option<usize> = None;
                for a in atoms {
                    let next = parent.len();
                    let i = *index.entry(a).or_insert(next);
                    if i == next {
                        parent.push(i);
                    }
                    if let Some(j) = at {
                        let (ri, rj) = (root(&mut parent, i), root(&mut parent, j));
                        parent[ri] = rj;
                    }
                    at = Some(i);
                }
                first.push(at);
            }
            let mut trees: BTreeMap<usize, Vec<&Formula>> = BTreeMap::new();
            for (g, at) in self.relation.set().iter().zip(first) {
                if let Some(i) = at {
                    trees.entry(root(&mut parent, i)).or_default().push(&**g);
                }
            }
            let parts: Vec<(PartKey, Formula)> = trees
                .into_values()
                .flat_map(|tree| split(tree.into_iter(), None))
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
        // Every block, as after a change of every name, is projected block by block.
        let every = matches!(due, Due::All);
        let (due, seeds): (Vec<BlockId>, Seeds) = match due {
            Due::All => (blocks.all().collect(), Seeds::default()),
            Due::Blocks(bs, seeds) => (bs.into_iter().collect(), seeds),
        };
        // What changed in each tree of the forest, for those projected by shortest paths.
        let mut fresh: BTreeMap<BlockId, Seeds> = BTreeMap::new();
        for n in &seeds.names {
            if let Some(t) = blocks.tree_of_name(n) {
                let at = fresh.entry(t).or_default();
                at.names.insert(n.clone());
                if seeds.unsure.contains(n) {
                    at.unsure.insert(n.clone());
                }
            }
        }
        for g in &seeds.added {
            if let Some(b) = blocks.of(g).filter(|b| !blocks.is_apart(*b)) {
                fresh
                    .entry(blocks.tree(b))
                    .or_default()
                    .added
                    .insert(g.clone());
            }
        }
        // The trees projected block by block in this projection, each with a block of it when
        // its potential is to be found again ([`Scope::reseed`]).
        let mut fallen: BTreeMap<BlockId, Option<BlockId>> = BTreeMap::new();
        // Each edge added is put in the potential before any tree is projected, whichever way
        // its tree is, so that the potential holds at every edge it has ([`Scope::repair`]).
        for (&t, at) in &fresh {
            if at.added.is_empty() {
                continue;
            }
            match self.repair(&relation, t, &at.added) {
                Ok(None) => {}
                Ok(Some(n)) => {
                    self.empty_at(&n);
                    self.relation = relation;
                    return;
                }
                Err(_) => {
                    fallen.insert(t, at.added.iter().find_map(|g| blocks.of(g)));
                }
            }
        }
        // The trees a name of which has come to have holes or a class in this projection.
        let mut holed: BTreeSet<BlockId> = BTreeSet::new();
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
            let t = blocks.tree(b);
            if whole_trees.contains(&t) {
                continue;
            }
            // A tree of difference constraints and bounds whose names each have one interval
            // and no class is projected by shortest paths from what changed in it, once for
            // all its blocks on the worklist, and again for each move that reaches it from a
            // star; otherwise, or when that cannot be done, block by block as below.
            if !every
                && !blocks.is_apart(b)
                && !fallen.contains_key(&t)
                && !holed.contains(&t)
                && blocks.differences_only(t)
            {
                let mut at = fresh.remove(&t).unwrap_or_default();
                at.names.extend(from.iter().cloned());
                if at.names.is_empty() && at.added.is_empty() {
                    continue;
                }
                let found = if at.unsure.is_empty() {
                    self.shortest(&relation, t, &at.names)
                } else {
                    Err(Fall::Unsure)
                };
                match found {
                    Ok(Shortest::Moved(ns)) => {
                        for n in &ns {
                            for g in relation.moved(n, self.lazy) {
                                if let Some(c) = blocks.of(g)
                                    && blocks.tree(c) != t
                                {
                                    cause.entry(c).or_default().insert(n.clone());
                                    if queued.insert(c) {
                                        work.push_back(c);
                                    }
                                }
                            }
                        }
                        continue;
                    }
                    Ok(Shortest::Bottom(n)) => {
                        self.empty_at(&n);
                        self.relation = relation;
                        return;
                    }
                    Err(why) => {
                        fallen.insert(t, (why == Fall::Potential).then_some(b));
                    }
                }
            }
            let block = Block::of(&relation, b);
            let before = self.snapshot(&block.names);
            self.project_block(&block);
            let mut echo = false;
            for (n, old) in block.names.iter().zip(&before) {
                let p = self.get(n);
                if (p.ints(), &p.cell.congruence.element) == (&old.1, &old.2) {
                    continue;
                }
                if p.ints().is_empty() {
                    self.relation = relation;
                    return;
                }
                if gapped(&p)
                    && let Some(at) = blocks.tree_of_name(n)
                {
                    holed.insert(at);
                }
                // A star's projection onto its hubs is exact, a bound on each alone, so it
                // passes nothing back and forth ([`Conjuncts::star`]): its move of the name
                // that moved it is no echo.
                echo |= from.contains(n) && !blocks.is_apart(b);
                for g in relation.moved(n, self.lazy) {
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
        for (t, b) in fallen {
            if let Some(b) = b {
                self.reseed(&relation, t, b);
            }
        }
        self.relation = relation;
    }

    /// Projects tree `t` of the forest, a tree of difference constraints and bounds whose
    /// names each have one interval and no class ([`conjuncts::Blocks::differences_only`]),
    /// after the names `seeds` changed, by shortest paths: `y <= x + k` is an edge `x → y` of
    /// weight `k`, a name's greatest value is its least distance from a bound, and its least
    /// the negated least distance to one (Shostak, "Deciding linear inequalities by computing
    /// loop residues", J. ACM 28, 1981). Such rows are totally unimodular, so these are the
    /// ends of the name's projection, an interval, and an empty one is bottom.
    ///
    /// The bounds were a fixed point of the tree's other conjuncts at the last projection, so
    /// only paths from the seeds can move one: each seed takes the least bound its edges in
    /// give it, and a Dijkstra search from the seeds moves the names its paths reach, with the
    /// weights reduced by the scope's potential ([`Potential`]), which [`Scope::repair`] has
    /// put the edges added in. In O((s + m) log n) for the `s` seeds and the `m` edges at the
    /// names whose bound moves, of `n` names; the tree's other names are not read. `Err` says
    /// why the tree is to be projected block by block, and nothing has changed.
    fn shortest(
        &mut self,
        relation: &Conjuncts,
        t: BlockId,
        seeds: &BTreeSet<Arc<str>>,
    ) -> Result<Shortest, Fall> {
        let up = self.bound_pass(relation, t, seeds, true)?;
        let down = self.bound_pass(relation, t, seeds, false)?;
        let mut moved: BTreeMap<Arc<str>, (Option<Int>, Option<Int>)> = BTreeMap::new();
        for (n, hi) in up {
            moved.entry(n).or_default().1 = Some(hi);
        }
        for (n, lo) in down {
            moved.entry(n).or_default().0 = Some(-&lo);
        }
        // Every name moved was read, so has one interval.
        let mut out = Vec::with_capacity(moved.len());
        for (n, (lo, hi)) in &moved {
            let (was_lo, was_hi) = self.ends(n)?;
            let lo = lo.clone().or(was_lo);
            let hi = hi.clone().or(was_hi);
            if let (Some(lo), Some(hi)) = (&lo, &hi)
                && lo > hi
            {
                return Ok(Shortest::Bottom(n.clone()));
            }
            let end = |v: Option<Int>, inf: End| v.map_or(inf, |v| End::Fin(Num::from(&v)));
            out.push((n.clone(), end(lo, End::NegInf), end(hi, End::PosInf)));
        }
        let mut ns = Vec::with_capacity(out.len());
        for (n, lo, hi) in out {
            if let Some(p) = self.names.get_mut(&n) {
                let prem = p.premises();
                p.meet_ints(IntervalSet::range(lo, hi), &prem);
                ns.push(n);
            }
        }
        Ok(Shortest::Moved(ns))
    }

    /// Puts the edges of the conjuncts `added` to tree `t` of the forest in the potential
    /// ([`Potential`]), one at a time: an edge `u → v` whose reduced weight `γ` is negative
    /// lowers the potential of each name `x` by the least reduced distance from `v` to `x`
    /// plus `γ`, where that is below zero, found by a Dijkstra search from `v` over those names
    /// alone (Cotton and Maler, "Fast and flexible difference constraint propagation for
    /// DPLL(T)", SAT 2006). `Ok(Some(u))` when the edge closes a cycle of negative weight, so
    /// that no point meets the tree's difference constraints; `Err` when the search reads a
    /// name the potential lacks, or an edge with a negative reduced weight, and then nothing
    /// has changed. A conjunct other than a difference constraint or a bound has no edge, and
    /// the tree may hold some.
    ///
    /// Why the potential then holds at every edge, and the cycle is found, though only the
    /// edges at the names the search settles are read: the potential held at every edge of
    /// the relation before ([`Potential`]), so each edge read has a reduced weight of zero or
    /// more, each key pushed is at least the key popped, and the names settle in the order of
    /// their distances. Then an edge `a → b` keeps a reduced weight of zero or more: when
    /// neither end's potential falls it is unchanged; when only `b`'s falls it grows; when
    /// `a` settles its edges are read, and `b` either settles too, by at most `a`'s fall plus
    /// the old reduced weight, or keeps a reduced weight of zero or more from `a`'s new
    /// potential. The new edge's reduced weight is then zero, since `v` falls by `γ` and `u`
    /// does not fall unless the edge closes such a cycle. That cycle is a path `P` from `v` to
    /// `u` with `γ` plus its reduced weight below zero; each edge of `P` has a reduced weight
    /// of zero or more, so each of its prefixes is below zero as well, the search settles each
    /// of its names or reaches them by a path no longer, and so reaches `u`. A name the
    /// potential lacks takes its value from its first edge only when every edge at it is among
    /// those added, each put in after; otherwise, as after a projection of every block, the
    /// tree is found again from the solver ([`Scope::reseed`]). The check of each edge read
    /// therefore fails only at a name the potential lacks.
    ///
    /// In O(m log n) for the `m` edges at the names whose potential falls, of `n` names.
    fn repair(
        &mut self,
        relation: &Conjuncts,
        t: BlockId,
        added: &BTreeSet<Arc<Formula>>,
    ) -> Result<Option<Arc<str>>, Fall> {
        let blocks = relation.blocks();
        let mut pot = self.potential.0.clone();
        // The edges added and not yet in the potential's graph.
        let mut pending: Vec<(Arc<Formula>, bool, Edge)> = Vec::new();
        for g in added {
            let Some((e, back)) = conjuncts::edges(g) else {
                continue;
            };
            if !blocks.of(g).is_some_and(|b| blocks.tree(b) == t) {
                continue;
            }
            pending.push((g.clone(), false, e));
            if let Some(e) = back {
                pending.push((g.clone(), true, e));
            }
        }
        // A name the potential lacks may take a value from an edge added only when every edge
        // at it was added: those are put in after.
        let new_name = |n: &Arc<str>| -> Result<(), Fall> {
            let all_added = tree_edges(relation, t, n)
                .iter()
                .all(|(g, _, e)| e.from.is_none() || e.to.is_none() || added.contains(g));
            if all_added {
                Ok(())
            } else {
                Err(Fall::Potential)
            }
        };
        let mut waiting: BTreeSet<(Arc<Formula>, bool)> = pending
            .iter()
            .map(|(g, back, _)| (g.clone(), *back))
            .collect();
        for (g, back, e) in &pending {
            waiting.remove(&(g.clone(), *back));
            let (Some(u), Some(v)) = (&e.from, &e.to) else {
                continue;
            };
            let gamma = match (pot.get(u).cloned(), pot.get(v).cloned()) {
                (None, None) => {
                    new_name(u)?;
                    new_name(v)?;
                    pot.insert(u.clone(), Int::ZERO);
                    pot.insert(v.clone(), e.weight.clone());
                    continue;
                }
                (Some(pu), None) => {
                    new_name(v)?;
                    pot.insert(v.clone(), &pu + &e.weight);
                    continue;
                }
                (None, Some(pv)) => {
                    new_name(u)?;
                    pot.insert(u.clone(), &pv - &e.weight);
                    continue;
                }
                (Some(pu), Some(pv)) => &(&pu + &e.weight) - &pv,
            };
            if gamma >= Int::ZERO {
                continue;
            }
            // Each name's potential falls by the least reduced distance from `v` below zero;
            // the new values are kept apart until the search ends, so that the old ones check
            // the edges read.
            let mut fall: BTreeMap<Arc<str>, Int> = BTreeMap::from([(v.clone(), gamma.clone())]);
            let mut heap = BinaryHeap::from([Reverse((gamma, v.clone()))]);
            let mut new: BTreeMap<Arc<str>, Int> = BTreeMap::new();
            while let Some(Reverse((gs, s))) = heap.pop() {
                if new.contains_key(&s) || fall.get(&s) != Some(&gs) {
                    continue;
                }
                let ps = pot.get(&s).ok_or(Fall::Potential)?;
                let to_s = ps + &gs;
                for (h, hb, f) in tree_edges(relation, t, &s) {
                    let (Some(from), Some(x)) = (&f.from, &f.to) else {
                        continue;
                    };
                    if *from != s || new.contains_key(x) || waiting.contains(&(h, hb)) {
                        continue;
                    }
                    let px = pot.get(x).ok_or(Fall::Potential)?;
                    if &(ps + &f.weight) - px < Int::ZERO {
                        return Err(Fall::Potential);
                    }
                    let gx = &(&to_s + &f.weight) - px;
                    if gx >= Int::ZERO {
                        continue;
                    }
                    if x == u {
                        return Ok(Some(u.clone()));
                    }
                    if fall.get(x).is_none_or(|c| gx < *c) {
                        fall.insert(x.clone(), gx.clone());
                        heap.push(Reverse((gx, x.clone())));
                    }
                }
                new.insert(s, to_s);
            }
            for (s, ps) in new {
                pot.insert(s, ps);
            }
        }
        self.potential.0 = pot;
        Ok(None)
    }

    /// Empties the interval of `n`, or the scope when it has no product of `n`.
    fn empty_at(&mut self, n: &str) {
        match self.names.get_mut(n) {
            Some(p) => {
                let prem = p.premises();
                p.meet_ints(IntervalSet::empty(), &prem);
            }
            None => self.bottom = true,
        }
    }

    /// The least and greatest integers of `n`, `None` for an infinite end, when `n` has a
    /// product of one interval and no class ([`gapped`]).
    fn ends(&self, n: &str) -> Result<(Option<Int>, Option<Int>), Fall> {
        let p = self.names.get(n).ok_or(Fall::Name)?;
        if gapped(p) {
            return Err(Fall::Name);
        }
        let (lo, hi) = p.ints().bounds().ok_or(Fall::Name)?;
        let fin = |e: &End| match e {
            End::Fin(v) => Some(Int::from(v)),
            _ => None,
        };
        Ok((fin(lo), fin(hi)))
    }

    /// One side of [`Scope::shortest`]: with `up` the greatest values, along the edges, with
    /// the scope's potential; otherwise the least values negated, along the edges reversed,
    /// with the potential negated, under which the reduced weights are the same. Each seed
    /// first takes the least bound its edges in give it, then a Dijkstra search from the seeds
    /// lowers the names its paths reach. The names lowered, with their new bounds on this side.
    ///
    /// The bounds found do not depend on the potential: a name lowered is pushed again, and
    /// each name popped at its latest bound lowers along each of its edges, so the search
    /// stops at a fixed point of the edges at the names it lowers, and the others' bounds were
    /// one already. The potential bounds the cost: each edge read is checked to have a reduced
    /// weight of zero or more, so each key pushed is at least the key popped, and each name
    /// is popped at its latest bound once.
    fn bound_pass(
        &self,
        relation: &Conjuncts,
        t: BlockId,
        seeds: &BTreeSet<Arc<str>>,
        up: bool,
    ) -> Result<BTreeMap<Arc<str>, Int>, Fall> {
        // An edge on this side, from and to.
        let way = |e: &Edge| {
            if up {
                (e.from.clone(), e.to.clone())
            } else {
                (e.to.clone(), e.from.clone())
            }
        };
        let q = |n: &Arc<str>| -> Result<Int, Fall> {
            let v = self.potential.0.get(n).ok_or(Fall::Potential)?;
            Ok(if up { v.clone() } else { -v })
        };
        let mut label: BTreeMap<Arc<str>, Option<Int>> = BTreeMap::new();
        let read = |label: &BTreeMap<Arc<str>, Option<Int>>, n: &Arc<str>| {
            if let Some(l) = label.get(n) {
                return Ok(l.clone());
            }
            let (lo, hi) = self.ends(n)?;
            Ok(if up { hi } else { lo.map(|l| -&l) })
        };
        let mut moved: BTreeMap<Arc<str>, Int> = BTreeMap::new();
        let mut heap: BinaryHeap<Reverse<(Int, Arc<str>)>> = BinaryHeap::new();
        for s in seeds {
            let was = read(&label, s)?;
            let mut l = was.clone();
            for (_, _, e) in tree_edges(relation, t, s) {
                let (a, b) = way(&e);
                if b.as_ref() != Some(s) {
                    continue;
                }
                let by = match &a {
                    None => Some(e.weight.clone()),
                    Some(r) => read(&label, r)?.map(|lr| &lr + &e.weight),
                };
                if let Some(c) = by
                    && l.as_ref().is_none_or(|x| c < *x)
                {
                    l = Some(c);
                }
            }
            if l != was
                && let Some(l) = &l
            {
                moved.insert(s.clone(), l.clone());
            }
            label.insert(s.clone(), l);
        }
        for s in seeds {
            if let Some(Some(l)) = label.get(s) {
                heap.push(Reverse((l - &q(s)?, s.clone())));
            }
        }
        while let Some(Reverse((k, s))) = heap.pop() {
            let Some(Some(ls)) = label.get(&s).cloned() else {
                continue;
            };
            let qs = q(&s)?;
            if &ls - &qs != k {
                continue;
            }
            for (_, _, e) in tree_edges(relation, t, &s) {
                let (a, b) = way(&e);
                let (Some(a), Some(x)) = (a, b) else {
                    continue;
                };
                if a != s {
                    continue;
                }
                let qx = q(&x)?;
                if &(&qs + &e.weight) - &qx < Int::ZERO {
                    return Err(Fall::Potential);
                }
                let by = &ls + &e.weight;
                if read(&label, &x)?.is_none_or(|c| by < c) {
                    moved.insert(x.clone(), by.clone());
                    heap.push(Reverse((&by - &qx, x.clone())));
                    label.insert(x, Some(by));
                }
            }
        }
        Ok(moved)
    }

    /// Finds again the potential of tree `t` of the forest, which holds block `b`, as a point
    /// of its conjuncts, all difference constraints and bounds, from the solver: after the
    /// tree was projected block by block because its potential lacked a name
    /// ([`Fall::Potential`]). Nothing when the solver finds no point.
    ///
    /// Complexity tradeoff: the point is asked of the whole tree, in the solver's time for its
    /// conjuncts, though only the names the potential lacks need new values. Why: a potential
    /// of part of a tree must agree with the rest at every edge between them, which a point of
    /// the part alone need not, and a potential of any part is found only by shortest paths
    /// from all the tree's names, Bellman–Ford in O(n m). Trigger: once per tree after a
    /// projection of every block ([`Due::All`], as when a scope is made), which empties the
    /// potential. No other projection triggers it, so a sequence of tests cannot reseed a tree
    /// again and again: each projection repairs the potential at every edge added, whichever
    /// way the tree is projected ([`Scope::repair`]), so after a reseed a name lacks a potential
    /// only if it had no edge to another name at the last projection, and then every such edge
    /// it has now was added and seeds it. Measured with tests that leave the tree to the
    /// projection block by block (`x_i + w_i >= 0`) between difference tests on the same tree:
    /// 661 MB at k = 40 and 5576 MB at k = 320, 8.4 times for 8 times k, the same on the code
    /// before the repair covered those edges, with no reseed in either. Test:
    /// `l01_39_reduced_product::linked::if_statements_that_leave_a_ladder_block_by_block_between_rungs_are_linear`.
    /// COMPLEXITY.md row S25. A complete solution keeps the point the projection's own solver
    /// finds for each tree (`presburger::difference_hulls` reads one) and passes it back.
    fn reseed(&mut self, relation: &Conjuncts, t: BlockId, b: BlockId) {
        let blocks = relation.blocks();
        let mut names: BTreeSet<Arc<str>> = BTreeSet::new();
        let mut cons: BTreeSet<Arc<Formula>> = BTreeSet::new();
        let mut stack: Vec<Arc<str>> = Vec::new();
        for g in blocks.members(b) {
            for n in conjuncts::names(g) {
                if names.insert(n.clone()) {
                    stack.push(n);
                }
            }
        }
        while let Some(n) = stack.pop() {
            for g in relation.mentioning(&n) {
                let here = blocks
                    .of(g)
                    .is_some_and(|c| !blocks.is_apart(c) && blocks.tree(c) == t);
                if !here || !cons.insert(g.clone()) {
                    continue;
                }
                for m in conjuncts::names(g) {
                    if names.insert(m.clone()) {
                        stack.push(m);
                    }
                }
            }
        }
        // The potential is of the edges alone, so the point is of the difference constraints and
        // bounds alone, where the tree holds other conjuncts.
        let edges = cons.iter().filter(|g| conjuncts::edges(g).is_some());
        let all = Formula::and(edges.map(|g| Formula::clone(g)).collect());
        if let Ok(Some(point)) = presburger::satisfiable(&all) {
            for n in names {
                if let Some(v) = point.get(&Atom::Sym(n.clone())) {
                    self.potential.0.insert(n, v.clone());
                }
            }
        }
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
        // Each part is compared with the snapshot of its own names, not the block's: a part
        // new to the block, or a name of another part, leaves it as it was, so a new conjunct
        // costs its own part and not the block's (the walk through a shared name).
        let names: Vec<Vec<Arc<str>>> = b.parts.iter().map(|(_, g)| syms(g)).collect();
        let mut work: std::collections::VecDeque<usize> = b
            .parts
            .iter()
            .zip(&names)
            .enumerate()
            .filter(|(_, ((key, _), ns))| self.projected.get(key) != Some(&self.snapshot(ns)))
            .map(|(i, _)| i)
            .collect();
        if work.is_empty() {
            return;
        }
        // A star's leaf is unbounded on the side away from its hubs, so each part bounds it by
        // a half-line its interval does not change, and no part's projection onto the hubs
        // reads it ([`Conjuncts::star`]): a move of the leaf makes no other part due and is
        // no move back and forth. Every part of a star mentions the leaf, through the star's
        // own conjunct, so otherwise each move of it projected all of them (item
        // NARROW-lazy-settle).
        let leaf = b.leaf.as_ref();
        let mut users: BTreeMap<&Arc<str>, Vec<usize>> = BTreeMap::new();
        for (i, ns) in names.iter().enumerate() {
            for n in ns.iter().filter(|n| Some(*n) != leaf) {
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
                if (p.ints(), &p.cell.congruence.element) == (&old.1, &old.2) {
                    continue;
                }
                empty |= p.ints().is_empty();
                again |= Some(n) != leaf && !moved.insert(n);
                for &j in users.get(n).into_iter().flatten() {
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
        for ((key, _), ns) in b.parts.iter().zip(&names) {
            let at = self.snapshot(ns);
            self.projected.insert(key.clone(), at);
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

    /// Tells the relation whether each of `names` is bounded below and above, as its product
    /// is now: a leaf is a star's only while unbounded on the side away from a conjunct of
    /// two hubs or more ([`Conjuncts::star`]). And whether each has holes or a class
    /// ([`gapped`]), which keeps its tree from projection by shortest paths
    /// ([`Scope::shortest`]).
    fn sync_bounds<'a>(&mut self, names: impl IntoIterator<Item = &'a Arc<str>>) {
        for n in names {
            let (below, above) = sides(&self.names, n);
            self.relation.bound(n, below, above);
            let gap = self.names.get(n).is_some_and(gapped);
            self.relation.gapped(n, gap);
        }
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

    /// Whether the conjuncts `then` and `now` of a class of stars ([`conjuncts::Class`]) give
    /// its leaf the same bound, in the names' products as they are, shown by projecting each
    /// onto the leaf, written [`conjuncts::LEAF`], as [`Scope::project_block`] projects a star
    /// of the class, but with the leaf's own product left whole. A star bounds its leaf on one
    /// side only, by a half-line ([`Conjuncts::star`]), so when the projection is exact a leaf
    /// `x` of the class projects to its own product cut by that half-line, and keeps its
    /// product when the half-line stays. The projection is exact when every conjunct is a
    /// constraint or the negation of a bound and every name but the leaf has one interval: a
    /// leaf's own product of many intervals is then the one disjunction, which the solver
    /// projects exactly ([`presburger::project`]). Otherwise, or when the solver refuses, this
    /// says no. In time near the conjuncts' size.
    fn same_leaf_bound(&self, then: &[Arc<Formula>], now: &[Arc<Formula>]) -> bool {
        if then == now {
            return true;
        }
        let literal = |g: &Arc<Formula>| match &**g {
            Formula::Con(_) => true,
            Formula::Not(n) => matches!(&**n, Formula::Con(c) if c.rel == Rel::Ge),
            _ => false,
        };
        if !then.iter().chain(now).all(literal) {
            return false;
        }
        let leaf = Atom::Sym(Arc::from(conjuncts::LEAF));
        let bound = |core: &[Arc<Formula>]| -> Option<IntervalSet> {
            let mut out = IntervalSet::top();
            for (_, part) in split(core.iter().map(|g| &**g), None) {
                let (whole, syms) = self.framed(&part);
                let one = |a: &Atom| match a {
                    Atom::Sym(n) => a == &leaf || self.get(n).ints().pieces().len() <= 1,
                    _ => true,
                };
                if !syms.iter().all(one) {
                    return None;
                }
                let i = syms.iter().position(|a| a == &leaf)?;
                let (mut each, skipped) = presburger::project_each(&whole, &syms).ok()?;
                if !skipped.is_empty() {
                    return None;
                }
                out = out.meet(&each.swap_remove(i).ok()?);
            }
            Some(out)
        };
        matches!((bound(then), bound(now)), (Some(a), Some(b)) if a == b)
    }

    /// `part` with each name it mentions met with its interval and class, the congruence
    /// `x == m * k + r` with `k` free, and the names, to project onto ([`Scope::project_part`]).
    fn framed(&self, part: &Formula) -> (Formula, Vec<Atom>) {
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
                && let Congruence::Class { modulus, residue } = &self.get(n).cell.congruence.element
                && *modulus > Num::ONE
            {
                let k = Lin::atom(Atom::Sym(format!("{n} mod").into()));
                let rhs = k
                    .times(Int::from(modulus))
                    .plus(&Lin::constant(Int::from(residue)));
                parts.push(Formula::Con(Con::eq(&Lin::atom(a.clone()), &rhs)));
            }
        }
        parts.push(part.clone());
        let whole = Formula::and(parts);
        let syms: Vec<Atom> = mentioned
            .into_iter()
            .filter(|a| matches!(a, Atom::Sym(_)))
            .collect();
        (whole, syms)
    }

    /// Meets each name `part` mentions with its projection, within every interval.
    fn project_part(&mut self, part: &Formula) {
        let (whole, syms) = self.framed(part);
        // The text of `part`, each name as written, printed once, and only when a question
        // about it is refused.
        let mut text: Option<Arc<str>> = None;
        let mut refuse = |s: &mut Scope, asked: Asked, cause| {
            let constraint = text
                .get_or_insert_with(|| part.written(written_name).into())
                .clone();
            s.refuse(Refused {
                constraint,
                asked,
                cause,
            });
        };
        let each = match presburger::project_each(&whole, &syms) {
            Ok((each, skipped)) => {
                for cause in skipped {
                    refuse(self, Asked::Disjunct, cause);
                }
                each
            }
            Err(cause) => {
                refuse(self, Asked::Projection, cause);
                return;
            }
        };
        for (a, x) in syms.iter().zip(each) {
            let x = match x {
                Ok(x) => x,
                Err(cause) => {
                    if let Atom::Sym(n) = a {
                        refuse(self, Asked::Onto(written_name(n).into()), cause);
                    }
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
    /// `l01_39_reduced_product::controls::a_listed_set_is_enumerated_and_a_range_is_not`.
    /// COMPLEXITY.md row C6. A complete solution would enumerate the product of the open names
    /// (`@exact` does, by branch and prune), at a cost exponential in the open names, and a
    /// termination proof stronger than the form of the term (size-change termination,
    /// PSPACE-complete in the call graph).
    fn enumerate(&mut self) {
        let now = (
            self.names.clone(),
            self.written.clone(),
            self.enumerated.clone(),
        );
        let last = self.seen.enumeration.replace(now);
        if self.exact {
            self.enumerate_exactly(last.as_ref());
        }
        let texts: BTreeSet<String> = match last {
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
                        Shared::new(Term::Lit(Value::Int(v))),
                        Shared::new(c.clone()),
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
                            kept.iter().map(|&v| (End::of(v), End::of(v))).collect(),
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
    /// Under `@exact`: decides whether some point of the bounded integer names' intervals and
    /// classes meets the written constraints on them, and sets `bottom` when none does. The
    /// constraints taken are each written constraint whose free names are all in scope, with
    /// its static names substituted and its other names, its open names, all bounded integers;
    /// their groups that share open names are independent, so the conjunction has a point
    /// exactly when each group does. [`Scope::exactly`] keeps a point: every constraint taken
    /// holds at it, except those of a group whose search gave no answer, whose names it does
    /// not give. `last` is the scope as the last enumeration found it, and a constraint is due
    /// only when it is new or rewritten since, mentions a name changed since, or shares a name
    /// with one removed since. A constraint due is first searched over its own open names that
    /// the point does not give within their intervals and classes, the others fixed at the
    /// point; a point found extends the point kept, and the constraints on the names it gives
    /// are due in turn. Only when that finds none is the constraint's whole group searched,
    /// once in a call. A reduction then costs the constraints due and the names they reach,
    /// found by the persistent maps' difference and the index of constraints by name, and
    /// not every group (ST-exact-enum, COMPLEXITY.md row S40); a group is searched whole only
    /// when the point cannot be extended, at the cost [`witness`] states. Whether the scope
    /// is bottom does not depend on the point kept: a group is found to have no point only
    /// by the search of the whole group, which is what the search of each group in full
    /// would find.
    fn enumerate_exactly(&mut self, last: Option<&Enumeration>) {
        let mut due: BTreeSet<String> = BTreeSet::new();
        match last {
            None => due.extend(self.written.keys().cloned()),
            Some((names, written, _)) => {
                for d in written.diff(&self.written) {
                    match d {
                        DiffItem::Add(k, _) | DiffItem::Update { new: (k, _), .. } => {
                            due.insert(k.clone());
                        }
                        // The constraints on its names: a group whose search gave no answer
                        // may fall apart into groups that give one.
                        DiffItem::Remove(_, (_, free)) => {
                            for n in free {
                                due.extend(self.written_by.of(n).cloned());
                            }
                        }
                    }
                }
                for d in names.diff(&self.names) {
                    let (DiffItem::Add(n, _)
                    | DiffItem::Remove(n, _)
                    | DiffItem::Update { new: (n, _), .. }) = d;
                    due.extend(self.written_by.of(n).cloned());
                }
            }
        }
        let mut todo = due.clone();
        // The names of the groups searched whole in this call.
        let mut searched: BTreeSet<Arc<str>> = BTreeSet::new();
        let yes = Demand::Bool(true);
        while let Some(text) = todo.pop_first() {
            let Some((c, open)) = self.taken(&text) else {
                // A constraint due that is no longer taken may have linked groups, as a
                // removed one did: the constraints on its names are due in its place.
                if due.remove(&text)
                    && let Some((_, free)) = self.written.get(&text)
                {
                    for n in free {
                        todo.extend(self.written_by.of(n).filter(|k| **k != text).cloned());
                    }
                }
                continue;
            };
            if open.iter().any(|n| searched.contains(n)) {
                continue;
            }
            let mut fixed: BTreeMap<Arc<str>, Value> = BTreeMap::new();
            let mut free: BTreeSet<Arc<str>> = BTreeSet::new();
            for n in open {
                match self.exactly.get(&n) {
                    Some(v) if self.admits(&n, v) => {
                        fixed.insert(n, Value::from(v));
                    }
                    _ => {
                        free.insert(n);
                    }
                }
            }
            let (dom, classes) = self.box_of(&free);
            if let Some(Some(w)) = witness(&substitute(&c, &fixed), &dom, &classes, &yes) {
                for n in &free {
                    todo.extend(self.written_by.of(n).filter(|k| **k != text).cloned());
                }
                self.exactly.extend(w);
                continue;
            }
            // Complexity tradeoff: when the kept point cannot be extended to this constraint,
            // its whole group is searched, at the cost of `witness` (COMPLEXITY.md row S17),
            // and a point is not repaired from part of the group. Why: a search over part of
            // the group cannot show that the group has no point, and a repair that frees names
            // one hop at a time can visit the group many times before failing. Trigger: k
            // reduces each of whose constraints the point cannot meet, on one group of k
            // constraints: k searches of the group. Test:
            // `l01_39_reduced_product::scaling::many_reductions_under_exact_scale` covers the
            // case the point extends. COMPLEXITY.md row S40.
            let (all, names) = self.group(free.into_iter().chain(fixed.into_keys()));
            let (dom, classes) = self.box_of(&names);
            match witness(&all, &dom, &classes, &yes) {
                Some(Some(w)) => self.exactly.extend(w),
                Some(None) => {
                    self.bottom = true;
                    return;
                }
                None => {
                    for n in &names {
                        self.exactly.remove(n);
                    }
                }
            }
            searched.extend(names);
        }
    }

    /// The written constraint of text `text` as [`Scope::enumerate_exactly`] takes it, with
    /// its static names substituted, and its open names; `None` when it is not taken: a free
    /// name not in scope, no open name, or an open name not a bounded integer.
    fn taken(&self, text: &str) -> Option<(Term, BTreeSet<Arc<str>>)> {
        let (c, free) = self.written.get(text)?;
        if !free.iter().all(|n| self.names.contains_key(n)) {
            return None;
        }
        let statics = self.statics_of(free);
        let open: BTreeSet<Arc<str>> = free
            .iter()
            .filter(|n| !statics.contains_key(*n))
            .cloned()
            .collect();
        let int = Type::int();
        let bounded_int = |n: &Arc<str>| {
            self.names.get(n).is_some_and(|p| {
                p.ty.element.subtype(&int)
                    && matches!(p.ints().bounds(), Some((End::Fin(_), End::Fin(_))))
            })
        };
        (!open.is_empty() && open.iter().all(bounded_int)).then(|| (substitute(c, &statics), open))
    }

    /// Whether `v` lies in the interval and the class of the name `n`.
    fn admits(&self, n: &str, v: &Num) -> bool {
        self.names.get(n).is_some_and(|p| {
            p.ints().contains_end(&End::Fin(v.clone())) && p.cell.congruence.element.contains(v)
        })
    }

    /// The intervals and classes of `names`, the box a [`witness`] searches.
    fn box_of(&self, names: &BTreeSet<Arc<str>>) -> (Domains, Classes) {
        let product = |n: &Arc<str>| self.names.get(n).expect("a name in scope");
        let dom = names
            .iter()
            .map(|n| (n.clone(), product(n).ints().clone()))
            .collect();
        let classes = names
            .iter()
            .map(|n| (n.clone(), product(n).cell.congruence.element.clone()))
            .collect();
        (dom, classes)
    }

    /// The group of a taken constraint whose open names are `open`: the conjunction of the
    /// taken constraints linked to it by shared open names, in the order of their texts, and
    /// their open names. Each constraint and name is visited once.
    fn group(&self, open: impl IntoIterator<Item = Arc<str>>) -> (Term, BTreeSet<Arc<str>>) {
        let mut names: BTreeSet<Arc<str>> = open.into_iter().collect();
        let mut todo: Vec<Arc<str>> = names.iter().cloned().collect();
        let mut texts: BTreeSet<&String> = BTreeSet::new();
        let mut taken: BTreeMap<&String, Term> = BTreeMap::new();
        while let Some(n) = todo.pop() {
            for k in self.written_by.of(&n) {
                if !texts.insert(k) {
                    continue;
                }
                let Some((t, more)) = self.taken(k) else {
                    continue;
                };
                for m in more {
                    if !names.contains(&m) {
                        names.insert(m.clone());
                        todo.push(m);
                    }
                }
                taken.insert(k, t);
            }
        }
        let all = taken
            .into_values()
            .reduce(|a, b| Term::Prim(Prim::And, vec![a, b]))
            .expect("the constraint the group is of is taken");
        (all, names)
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
    /// The node's place in the order of the forms of the tests, from 1: equal for two tests
    /// that differ only in the order of the sides of their nests, and otherwise ordered by
    /// height and then by form ([`Tree::of`]). No hash decides it, so neither the order the
    /// tests are written in nor a collision of hashes changes it (step L1.37a).
    id: usize,
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
    /// order of their ranks, ids and polarities, those equal kept once.
    Nest(bool, Vec<(usize, bool)>),
    /// `if c { a } else { b }` with tests as arms: `c`, `a` and `b`, each with its polarity.
    If([(usize, bool); 3]),
}

impl Kind {
    /// The kind's place in the order of forms: literals, atoms, nests, `if`s.
    fn tag(&self) -> u8 {
        match self {
            Kind::Lit(_) => 0,
            Kind::Atom => 1,
            Kind::Nest(..) => 2,
            Kind::If(_) => 3,
        }
    }
}

/// The ids of the nodes `s` names, with their polarities.
fn ids<'n>(nodes: &'n [Node], s: &'n [(usize, bool)]) -> impl Iterator<Item = (usize, bool)> + 'n {
    s.iter().map(|&(k, p)| (nodes[k].id, p))
}

/// Where a node stands among the sides of a nest, before its id: a later case knows the
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
            id: 0,
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
        // The nodes by height, each node after the nodes below it; an atom's text once.
        let mut height = vec![0usize; nodes.len()];
        let mut texts = vec![String::new(); nodes.len()];
        for i in (0..nodes.len()).rev() {
            let below = |k: &(usize, bool)| height[k.0] + 1;
            height[i] = match &nodes[i].kind {
                Kind::Nest(_, sides) => sides.iter().map(below).max().unwrap_or(1),
                Kind::If(arms) => arms.iter().map(below).max().unwrap_or(1),
                Kind::Atom => {
                    texts[i] = nodes[i].term.to_string();
                    0
                }
                Kind::Lit(_) => 0,
            };
        }
        let mut levels: Vec<Vec<usize>> =
            vec![Vec::new(); height.iter().max().map_or(0, |h| h + 1)];
        for (i, &h) in height.iter().enumerate() {
            levels[h].push(i);
        }
        // Ids and sizes, one height at a time from the leaves up: a node's sides are put in
        // order by the ids below it, then the nodes of the height are sorted by their forms
        // and numbered after those below them.
        let mut next = 0;
        for mut level in levels {
            for &i in &level {
                let mut kind = std::mem::replace(&mut nodes[i].kind, Kind::Atom);
                let mut size = 1;
                match &mut kind {
                    Kind::Lit(_) | Kind::Atom => {}
                    Kind::Nest(_, sides) => {
                        sides.sort_by_key(|&(k, p)| (nodes[k].rank, nodes[k].id, p));
                        sides.dedup_by(|x, y| {
                            x.1 == y.1
                                && nodes[x.0].id == nodes[y.0].id
                                && nodes[x.0].term == nodes[y.0].term
                        });
                        size += sides.iter().map(|&(k, _)| nodes[k].size).sum::<usize>();
                    }
                    Kind::If(arms) => {
                        size += arms.iter().map(|&(k, _)| nodes[k].size).sum::<usize>();
                    }
                }
                nodes[i].kind = kind;
                nodes[i].size = size;
                nodes[i].rank = rank(&nodes[i]);
            }
            let form = |a: usize, b: usize| match (&nodes[a].kind, &nodes[b].kind) {
                (Kind::Lit(x), Kind::Lit(y)) => x.cmp(y),
                (Kind::Atom, Kind::Atom) => texts[a].cmp(&texts[b]),
                (Kind::Nest(x, s), Kind::Nest(y, t)) => {
                    x.cmp(y).then_with(|| ids(&nodes, s).cmp(ids(&nodes, t)))
                }
                (Kind::If(s), Kind::If(t)) => ids(&nodes, s).cmp(ids(&nodes, t)),
                (x, y) => x.tag().cmp(&y.tag()),
            };
            level.sort_by(|&a, &b| form(a, b));
            let new: Vec<bool> = (0..level.len())
                .map(|j| j == 0 || form(level[j - 1], level[j]).is_ne())
                .collect();
            for (&i, new) in level.iter().zip(new) {
                next += usize::from(new);
                nodes[i].id = next;
            }
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
                    let [c, a, b] = [*c, *a, *b].map(|s| Shared::new(take(s)));
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
                        j.reduce_case();
                    }
                    j
                }
                None => l,
            });
        }
    }
    cases.pop().expect("a test has a case")
}

/// A comparison of a literal with a value whose carrier is inferred, as the elaborator writes
/// it: `let v = x in v op m`, or `m op v`, where `m` is the match [`follow_own`] reads on `v`.
struct Follow<'t> {
    op: Prim,
    /// The value compared, `x`.
    value: &'t Term,
    /// The side the match is on.
    at: usize,
    /// The literal's own term.
    own: &'t Term,
}

impl Follow<'_> {
    /// The comparison of `x`, found as `value`, with the literal itself: what the comparison
    /// is when `x` is an integer, since no other arm is taken.
    fn plain(&self, value: Term) -> Term {
        let mut args = vec![value, self.own.clone()];
        if self.at == 0 {
            args.swap(0, 1);
        }
        Term::Prim(self.op, args)
    }
}

/// `t` read as a [`Follow`], by its form alone.
fn follow<'t>(t: &'t Term) -> Option<Follow<'t>> {
    let Term::Let(v, x, body) = t else {
        return None;
    };
    let Term::Prim(op, args) = &**body else {
        return None;
    };
    if !is_comparison(*op) || args.len() != 2 {
        return None;
    }
    let bound = |a: &Term| matches!(a, Term::Var(w) if w == v);
    let own = |a: &'t Term| match a {
        Term::Match(s, arms) if bound(s) => follow_own(arms),
        _ => None,
    };
    (0..2).find_map(|at| {
        Some(Follow {
            op: *op,
            value: x,
            at,
            own: own(&args[at]).filter(|_| bound(&args[1 - at]))?,
        })
    })
}

/// The comparison `t` is when it is a [`Follow`] whose value is a name that is an integer in
/// `scope`: the name compared with the literal itself, which the narrowing reads as an equality
/// of the name with a literal. A [`Follow`] whose value is not a name is left as written: the
/// preimage catalog reads its match as the literal itself where the value is an integer
/// (`preimage::Node::Follow`), so its preimage and its linear relation are those of the plain
/// comparison. Deciding here that such a value is an integer would mean finding its product,
/// and a value can hold tests of the same kind, each found again for every test around it: a
/// chain `d` deep of `if` tests, each comparing the `if` below with a literal, cost about `2^d`
/// that way (6.1 s at `d = 12`), and `d` times the plain chain when found once per test.
/// `l01_39_reduced_product::follow` tests both (COMPLEXITY.md row F69).
fn plain_comparison(t: &Term, scope: &Scope) -> Option<Term> {
    let f = follow(t)?;
    let Term::Var(x) = f.value else {
        return None;
    };
    scope
        .get(x)
        .ty
        .element
        .subtype(&Type::int())
        .then(|| f.plain(f.value.clone()))
}

/// `test` with each comparison [`plain_comparison`] reads made plain, through its
/// connectives; `None` when it holds none. An explicit stack, since a test nests as deep as
/// it is written.
fn plain_test(test: &Term, scope: &Scope) -> Option<Term> {
    enum Step<'a> {
        Visit(&'a Term),
        Build(&'a Term),
    }
    fn kids(t: &Term) -> Vec<&Term> {
        match t {
            Term::Prim(Prim::And | Prim::Or | Prim::Not, a) => a.iter().collect(),
            Term::If(c, a, b) => vec![&**c, &**a, &**b],
            _ => Vec::new(),
        }
    }
    let (mut todo, mut done) = (vec![Step::Visit(test)], Vec::<Option<Term>>::new());
    while let Some(step) = todo.pop() {
        match step {
            Step::Visit(t) => {
                let ks = kids(t);
                if ks.is_empty() {
                    done.push(plain_comparison(t, scope));
                } else {
                    todo.push(Step::Build(t));
                    todo.extend(ks.into_iter().rev().map(Step::Visit));
                }
            }
            Step::Build(t) => {
                let ks = kids(t);
                let got = done.split_off(done.len() - ks.len());
                if got.iter().all(Option::is_none) {
                    done.push(None);
                    continue;
                }
                let mut new: Vec<Term> = (got.into_iter().zip(ks))
                    .map(|(g, k)| g.unwrap_or_else(|| k.clone()))
                    .collect();
                done.push(Some(match t {
                    Term::Prim(p, _) => Term::Prim(*p, new),
                    _ => {
                        let b = new.pop().expect("three parts");
                        let a = new.pop().expect("three parts");
                        let c = new.pop().expect("three parts");
                        Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
                    }
                }));
            }
        }
    }
    done.pop().expect("one result")
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

/// The integer literal `v`, of any size.
fn int_lit(v: &Value) -> Option<Num> {
    match v {
        Value::Int(n) => Some(Num::from(*n)),
        Value::Big(n) => Some(Num::from(&**n)),
        _ => None,
    }
}

/// The product of a literal equality's outcome on `p`: the literal itself, or every value but
/// it, excluded by complement in the type, the interval and the finite set.
fn equality(p: &mut Product, v: &Value, equal: bool, prem: &Premises) {
    if equal {
        let lit = Product::literal(v);
        p.ty.meet(&lit.ty.element, prem);
        p.cell.finite.meet(&lit.cell.finite.element, prem);
        if let Some(n) = int_lit(v) {
            p.meet_ints(IntervalSet::point(n.clone()), prem);
            p.cell.congruence.meet(&Congruence::single(n), prem);
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
            Term::Let(n.clone(), Shared::new(Term::Lit(v.clone())), Shared::new(b))
        })
}

/// The element of `e`'s value in `scope`: a literal, a value computed from static names, the
/// revision table's forward transfer over integers, or the join of an `if`'s reachable arms.
/// `scope` is as it was on return. The walk keeps its `let`s, `if`s and primitives on frames
/// on the heap (`Run`), so any depth of nesting runs on a small thread stack.
pub fn forward(e: &Term, scope: &mut Scope) -> Product {
    let run = Run::new(scope);
    run.stack.run(run.forward(e))
}

/// The walks of [`arms`] and [`forward`], each `let`, `if` and primitive they enter a call on a
/// frame of its own ([`zed_kernel::frames`]), so that the depth of a term is limited by memory
/// and not by the thread's stack; the calls run in the order the recursive walks ran them
/// (item PA-let-stack). The scope the walk is in is the top of `inner`, or `outer` when
/// `inner` is empty: the scope of an `if` arm is pushed while its arm is walked.
struct Run<'m> {
    stack: Stack<'m>,
    /// The scope the walk starts in.
    outer: RefCell<&'m mut Scope>,
    /// The scopes of the arms being walked, innermost last.
    inner: RefCell<Vec<Scope>>,
    /// The arms found so far, in the order written.
    out: RefCell<Vec<Arm>>,
    /// How many tests the walk has met: the position of the next test's premise.
    count: std::cell::Cell<u32>,
}

impl<'m> Run<'m> {
    fn new(scope: &'m mut Scope) -> Self {
        Run {
            stack: Stack::default(),
            outer: RefCell::new(scope),
            inner: RefCell::new(Vec::new()),
            out: RefCell::new(Vec::new()),
            count: std::cell::Cell::new(0),
        }
    }

    /// `f` of the scope the walk is in, borrowed for the call of `f` alone.
    fn scope<R>(&self, f: impl FnOnce(&mut Scope) -> R) -> R {
        match self.inner.borrow_mut().last_mut() {
            Some(s) => f(s),
            None => f(&mut self.outer.borrow_mut()),
        }
    }

    /// [`forward`] of `e` in the scope the walk is in.
    fn forward(&'m self, e: &'m Term) -> Deep<'m, Product> {
        match e {
            Term::Let(..) | Term::If(..) | Term::Prim(..) => {
                self.stack.call(move || self.forward_at(e))
            }
            _ => Stack::ready(self.scope(|s| leaf(e, s))),
        }
    }

    async fn forward_at(&'m self, e: &'m Term) -> Product {
        if self.scope(|s| s.bottom) {
            return Product::bottom();
        }
        match e {
            Term::Let(x, v, b) => {
                let p = self.forward(v).await;
                // A literal compared with the bound value that follows its carrier is, at an
                // integer, the literal itself, compared with the value just found.
                let plain = follow(e).filter(|_| p.ty.element.subtype(&Type::int()));
                let u = self.scope(|s| s.bind(x, p, v));
                let out = match plain {
                    // The comparison `Follow::plain` writes, `x` on one side and the literal's
                    // own term on the other.
                    Some(f) if !self.scope(|s| s.bottom) => {
                        let mut xs = Vec::with_capacity(2);
                        for side in 0..2 {
                            xs.push(if side == f.at {
                                self.forward(f.own).await
                            } else {
                                self.scope(|s| s.get(x))
                            });
                        }
                        forward_prim(f.op, xs)
                    }
                    Some(_) => Product::bottom(),
                    None => self.forward(b).await,
                };
                self.scope(|s| s.unbind(u));
                out
            }
            Term::If(c, a, b) => {
                let none = Premises::new();
                let (t, f) = self.scope(|s| (s.assume(c, true, &none), s.assume(c, false, &none)));
                self.inner.borrow_mut().extend([f, t]);
                let mut p = self.forward(a).await;
                self.inner.borrow_mut().pop();
                p.join(&self.forward(b).await);
                self.inner.borrow_mut().pop();
                p
            }
            Term::Prim(op, args) => {
                let mut xs = Vec::with_capacity(args.len());
                for a in args {
                    xs.push(self.forward(a).await);
                }
                forward_prim(*op, xs)
            }
            _ => self.scope(|s| leaf(e, s)),
        }
    }

    /// The arms of `t` in the scope the walk is in, appended to `out`; the scope is as it was
    /// on return.
    fn walk(&'m self, t: &'m Term) -> Deep<'m, ()> {
        match t {
            Term::Let(..) | Term::If(..) | Term::Prim(..) | Term::App(..) => {
                self.stack.call(move || self.walk_at(t))
            }
            _ => Stack::ready(()),
        }
    }

    async fn walk_at(&'m self, t: &'m Term) {
        match t {
            Term::Let(x, e, b) => {
                self.walk(e).await;
                let p = self.forward(e).await;
                let u = self.scope(|s| s.bind(x, p, e));
                self.walk(b).await;
                self.scope(|s| s.unbind(u));
            }
            Term::If(c, a, b) => {
                let count = self.count.get();
                self.count.set(count + 1);
                let at = FactAddress {
                    node: NodeAddress(Vector::unit(Position::root().child(count))),
                    keypath: Vector::new(),
                };
                let prem = Premises::one(Premise::Constraint(at));
                for (o, arm) in [(true, a), (false, b)] {
                    let s = self.scope(|s| s.assume(c, o, &prem));
                    self.out.borrow_mut().push(Arm {
                        guard: c.to_string(),
                        outcome: o,
                        scope: s.clone(),
                    });
                    self.inner.borrow_mut().push(s);
                    self.walk(arm).await;
                    self.inner.borrow_mut().pop();
                }
            }
            Term::Prim(_, args) => {
                for a in args {
                    self.walk(a).await;
                }
            }
            Term::App(f, args) => {
                self.walk(f).await;
                for a in args {
                    self.walk(a).await;
                }
            }
            _ => {}
        }
    }
}

/// [`forward`] of a term it does not enter: a literal, a name, or a term whose value is
/// computed when its free names are static.
fn leaf(e: &Term, scope: &Scope) -> Product {
    if scope.bottom {
        return Product::bottom();
    }
    match e {
        Term::Lit(v) => return Product::literal(v),
        Term::Var(x) => return scope.get(x),
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

/// [`forward`] of a primitive whose arguments have the elements `xs`: its value when every
/// argument has one, else the revision table's transfer over integers.
fn forward_prim(op: Prim, xs: Vec<Product>) -> Product {
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
        p.cell.ints.element = Bounds::ints(revision::forward(&op, xs[0].ints(), &y));
        p.reduce_domains();
    } else if zed_kernel::bits::is_bit_word(op)
        && op.arity() == Some(xs.len())
        && xs.iter().all(|x| {
            let want = match op {
                Prim::F64Bits => Type::f64(),
                _ => Type::int(),
            };
            x.ty.element.subtype(&want)
        })
    {
        let ints: Vec<IntervalSet> = xs.iter().map(|x| x.ints().clone()).collect();
        p.ty.element = Type::int();
        p.cell.ints.element = Bounds::ints(zedc_lattice::interval::bit_word(op, &ints));
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
/// The premise of each test is its position in the walk. The walk keeps its nesting on frames
/// on the heap (`Run`), so a block of any depth runs on a small thread stack.
pub fn arms(term: &Term, scope: &Scope) -> Vec<Arm> {
    let mut scope = scope.clone();
    let run = Run::new(&mut scope);
    run.stack.run(run.walk(term));
    run.out.take()
}

/// Whether the integers of `p` are other than one interval with no class: such a name keeps a
/// tree of difference constraints from projection by shortest paths
/// ([`conjuncts::Blocks::differences_only`]), since its holes may narrow the others past the
/// intervals' bounds. A class of modulus 0, a single value, counts only where the interval is
/// that value.
fn gapped(p: &Product) -> bool {
    let ints = p.ints();
    let plain = match &p.cell.congruence.element {
        Congruence::Class { modulus, .. } if *modulus == Num::ONE => true,
        Congruence::Class { modulus, residue } if *modulus == Num::ZERO => {
            ints.bounds() == Some((&End::Fin(residue.clone()), &End::Fin(residue.clone())))
        }
        _ => false,
    };
    !(plain && ints.pieces().len() == 1)
}

/// Whether `n` is bounded below and above in `names`: a name not there is unbounded, and an
/// empty product is bounded.
fn sides(names: &imbl::OrdMap<Arc<str>, Product>, n: &str) -> (bool, bool) {
    match names.get(n).map(|p| p.ints().bounds()) {
        Some(Some((lo, hi))) => (*lo != End::NegInf, *hi != End::PosInf),
        Some(None) => (true, true),
        None => (false, false),
    }
}
