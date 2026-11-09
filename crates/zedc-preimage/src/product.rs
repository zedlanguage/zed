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
//! - the type loses `int` when the interval or the congruence is empty, keeps only its own
//!   integer literals within the interval, the member of a one-member interval, or the members
//!   of a finite set, and gives its literals back to the finite set and the interval; an
//!   interval of more members is never listed, whatever its width;
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
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap};
use std::fmt;
use std::sync::atomic::{self, AtomicU64};
use std::sync::{Arc, Mutex, PoisonError};

use zed_kernel::frames::{Deep, Stack};
use zed_kernel::print;
use zed_kernel::provenance::{FactAddress, NodeAddress, Position, Vector};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Prim, Shared, Term, Value, World};

use super::address::Address;
use super::holes;
use super::images;
use super::preimage::{
    Classes, Demand, Domains, LetIn, LetPa, Lets, Listed, Shift, TermBounds, follow_own,
    let_narrowing, let_summary, preimage_listed, relations, witness,
};
use super::threshold;
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

/// The element of the reduced product for one name: its domains ([`ProductDomains`]) behind a
/// shared pointer, so that a copy costs `O(1)` and a change copies the domains only when
/// another product shares them. A scope keeps its names in a persistent map, and the caches of
/// a walk keep earlier versions of it (each held summary and its last read keep the names they
/// were made over), so an insertion copies the map's nodes on the path to the name, and every
/// product in them; with each product copied whole, a binding cost about 70 KB and a third of
/// its time (item PA-bind-cost).
#[derive(Clone)]
pub struct Product(Arc<ProductDomains>);

/// The domains of a [`Product`].
#[derive(Clone, PartialEq, Debug)]
pub struct ProductDomains {
    /// The domains of step L1.24.
    pub cell: Cell,
    /// The type.
    pub ty: Entry<Type>,
    /// The binding time.
    pub time: Entry<Time>,
}

impl std::ops::Deref for Product {
    type Target = ProductDomains;
    fn deref(&self) -> &ProductDomains {
        &self.0
    }
}

impl std::ops::DerefMut for Product {
    /// The domains, copied first when another product shares them.
    fn deref_mut(&mut self) -> &mut ProductDomains {
        Arc::make_mut(&mut self.0)
    }
}

impl PartialEq for Product {
    fn eq(&self, other: &Product) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0 == other.0
    }
}

impl fmt::Debug for Product {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Product")
            .field("cell", &self.cell)
            .field("ty", &self.ty)
            .field("time", &self.time)
            .finish()
    }
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
        Product(Arc::new(ProductDomains {
            cell: Cell::top(),
            ty: Entry::new(Type::top()),
            time: Entry::new(Time::Run),
        }))
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
        Product(Arc::new(ProductDomains {
            cell: Cell::literal(v),
            ty: Entry::new(Type::lit(v).unwrap_or_else(Type::top)),
            time: Entry::new(Time::Build),
        }))
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
    fn meet_ints(&mut self, x: IntervalSet, premises: &Premises) -> bool {
        self.cell.ints.meet(&Bounds::ints(x), premises)
    }

    /// The reductions between this product's own domains, once each; whether one changed a
    /// domain. Each change is a meet, so the product only descends.
    fn reduce_domains(&mut self) -> bool {
        let prem = self.premises();
        let int = Type::int();
        let (x, c) = reduce_congruence(self.ints(), &self.cell.congruence.element);
        let mut changed = self.meet_ints(x, &prem);
        changed |= self.cell.congruence.meet(&c, &prem);
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
                changed |= self.meet_ints(ints, &prem);
            }
            changed |= self.cell.finite.meet(&FiniteSet::Set(kept), &prem);
        }
        // The type from the other domains.
        if self.ints().is_empty() || self.cell.congruence.element == Congruence::Bottom {
            changed |= self.ty.meet(&!&int, &prem);
        } else {
            // The type's integers narrowed to the interval: the type's own integer literals,
            // which the source lists, met with the interval; or, for a type that lists none,
            // the interval's one member when it has one, which is a value and not a list.
            //
            // Complexity tradeoff: an interval of more than one member whose type lists no
            // literals is not listed, whatever its width, so the type keeps all of `int` there
            // and loses what listing would carry into it; `int[0..=1]` and `int[0..=1000]` are
            // read alike. Why: listing an interval costs time and space in its members, which
            // can be exponential in the bits written, and a rule by width would change what
            // is known when one member is added (DESIGN.md L1.25, author's answer to Q11).
            // Trigger: a name whose type lists no integer literals and whose interval holds
            // two or more members. Tests:
            // `l01_39_reduced_product::controls::a_listed_set_is_enumerated_and_a_range_is_not`,
            // `l01_39_reduced_product::controls::ranges_of_every_width_list_nothing`.
            // COMPLEXITY.md row C5. A complete solution would let the type language hold
            // integer ranges, so that the interval enters the type without listing.
            let x = self.ints();
            let vs: Option<Vec<Value>> = match self.ty.element.ints_listed() {
                Some(vs) => Some(
                    vs.into_iter()
                        .filter(|v| !matches!(v, Value::Int(n) if !x.contains(*n)))
                        .collect(),
                ),
                None => match x.bounds() {
                    Some((End::Fin(a), End::Fin(b))) if a == b => Some(vec![Value::from(a)]),
                    _ => None,
                },
            };
            if let Some(vs) = vs {
                let lits = Type::union_all(vs.iter().filter_map(Type::lit));
                changed |= self.ty.meet(&(&!&int | &lits), &prem);
            }
        }
        if let FiniteSet::Set(vs) = &self.cell.finite.element {
            let lits: Option<Vec<Type>> = vs.iter().map(Type::lit).collect();
            if let Some(lits) = lits {
                let t = Type::union_all(lits);
                changed |= self.ty.meet(&t, &prem);
            }
        }
        // The other domains from the type.
        // A finite set already held is kept where the type holds each member, so the type's
        // values are not listed: the cost is one membership test per member. With no finite
        // set, the type's values become it only when the type writes them as a list
        // (`Type::values_listed`), at a cost in the values written (COMPLEXITY.md row S34).
        //
        // Complexity tradeoff: a finite type that is not written as a list, a tuple type with
        // a component of two or more values such as `(bool, bool)` or `t(d)`, `t(i + 1) =
        // (t(i), t(i))`, keeps no finite set: the set stays the top and the type alone holds
        // the name's values. Membership and emptiness are read from the type and lose
        // nothing. What is lost: the one value of such a type when it has exactly one, as
        // `(0 | 1, 0) - (1, 0)`, so the name is not taken as static (`Product::value`); a join
        // of two arms keeps no list for it; and `x != v` for a tuple literal `v` takes `v` out
        // of no list, so excluding each value of `(bool, bool)` in turn does not empty the
        // scope (the type cannot take `v` out, since a key path of `v`'s shape is in the
        // tuple type and is not equal to `v`).
        // Why: listing a product of `k` components of two values each costs `2^k` values, and
        // `t(d)` has `2^(2^d)`, exponential in the type as written; whether a combination of
        // tuple types has exactly one value is coNP-hard (`types/empty.rs`). No size is
        // compared: the rule reads the type's form. Trigger: a box of the type with a
        // component of two or more literals or tuple types. Tests:
        // `l01_39_reduced_product::finite_from_type::a_named_finite_type_stays_a_type`,
        // `a_named_finite_type_reduces_in_time_linear_in_its_form`,
        // `a_fact_on_a_listed_type_narrows_its_list_and_a_named_type_answers_from_the_type`.
        // COMPLEXITY.md row S34. A complete solution would keep the finite set as a type,
        // with the type's operations, and decide a type's one value by an emptiness search
        // over its tuple types.
        if self.ty.element.finite() {
            let ty = &self.ty.element;
            let kept = match &self.cell.finite.element {
                FiniteSet::Set(vs) => {
                    Some(FiniteSet::of(vs.iter().filter(|v| ty.contains(v)).cloned()))
                }
                FiniteSet::Top => ty.values_listed().map(FiniteSet::of),
            };
            if let Some(kept) = kept {
                changed |= self.cell.finite.meet(&kept, &prem);
            }
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
            changed |= self.meet_ints(ints, &prem);
        }
        changed
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
/// set holds the literals the source lists (a type's literals, a literal equated with the
/// name) and the one member of a one-member interval, never the members of a wider interval,
/// so the list is no longer than what the source lists.
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
    /// The written constraints that hold, a test and its negations by content address (each
    /// held as its canonical term, [`Address::term`]), each with its free names.
    pub written: imbl::OrdMap<Address, Vec<Arc<str>>>,
    /// The addresses of the written constraints on each name.
    written_by: Uses<Address>,
    /// Whether no state reaches this scope.
    pub bottom: bool,
    /// Whether each name is already the bottom, in a scope no state reaches ([`Emptied`]).
    emptied: Emptied,
    /// The written constraints already enumerated, each as its address with the values of its
    /// static names. A second enumeration removes nothing more: the members a constraint holds
    /// at do not depend on the interval, which already lies within them.
    pub enumerated: imbl::OrdSet<Enumerated>,
    /// The top-level parts of the relation already projected: its constraints together, and
    /// each other conjunct with them, each with what it was projected with and the intervals
    /// and classes of the names it mentions at that projection, which are all a projection
    /// reads of them. A part is projected again only when one of these has changed since
    /// (docs/thresholds.md, replacement 4). Each part has one entry, which its next
    /// projection replaces, so the map holds one entry for each part of the relation, not one
    /// for each change of the equalities or constraints a part is projected with
    /// ([`PartKey`]).
    pub projected: imbl::OrdMap<PartKey, (PartWith, Projected)>,
    /// Whether the scope is under `@exact`.
    pub exact: bool,
    /// Under `@exact`, a point that meets the written constraints the last enumeration took: a
    /// value for each open name of each group of them whose search found a point, and none for
    /// the names of a group whose search gave no answer (`Scope::enumerate_exactly`).
    pub exactly: imbl::OrdMap<Arc<str>, Num>,
    /// Each question the integer solver left undecided while this scope was narrowed or
    /// projected, with the constraint it was asked of and how the scope came to ask it; each
    /// one leaves the scope sound but wider than it could be. [`Scope::warnings`] reports them.
    /// Each keeps the sets its variables kept when it was refused (none when nothing stood in
    /// for its answer), which its warning names: a repeat in one scope keeps their meet, and a
    /// join keeps their join. Recording one costs O(log k + m log m) for k refusals and m
    /// variables.
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
    pub refusals: imbl::OrdMap<Refused, Kept>,
    /// Each name a `let` of the walk bound, with the order of its binding and, for a function,
    /// its lambda: a test that calls a function is closed over it before its preimage is taken
    /// ([`Scope::close`]). Shared between the scopes of a walk's arms, not copied.
    bindings: imbl::OrdMap<Arc<str>, Binding>,
    /// The order of each name's binding ([`Orders`]).
    orders: Orders,
    /// What the summaries of the bindings read where they were last read ([`Reads`]).
    reads: Reads,
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

/// A name's `let` binding in a [`Scope`]; the order of its binding is in [`Scope::orders`].
#[derive(Clone, PartialEq, Debug)]
struct Binding {
    /// The lambda the name is bound to, when it is one.
    function: Option<Shared>,
    /// The summary of the integer the name is bound to, over its inputs ([`Scope::summary`]).
    summary: Option<Arc<Held>>,
}

/// The order of each name's binding in a [`Scope`]: a binding made later has a larger one. A
/// map of its own, apart from the bindings, so that a summary keeps the orders it was made
/// with ([`Held`]) and not the bindings, which keep summaries in turn.
type Orders = imbl::OrdMap<Arc<str>, u64>;

/// The summary of the value of a `let` ([`LetPa`]) as its binding keeps it, with what it was
/// made over: it holds while each input it reads is the binding it was and that input's
/// integers lie within those it was made over ([`Scope::holds`]). A cache, equal in every
/// binding, as [`Reduced`] is.
struct Held {
    /// A number no other held summary has, by which its reads are kept ([`Reads`]).
    id: u64,
    summary: LetPa,
    /// The integers of the inputs when it was made.
    made: Made,
    /// The orders of the bindings when it was made.
    orders: Orders,
    /// The held summary with the most inputs among those of the names the value reads, whose
    /// read the first read of this one starts from ([`Scope::holds`]).
    widest: Option<u64>,
}

/// The integers of the inputs of a [`Held`] summary when it was made.
enum Made {
    /// Those of the names of the scope it was made in, all its inputs among them.
    Scope(imbl::OrdMap<Arc<str>, Product>),
    /// Those given with it ([`Scope::bind_summarized`]).
    Given(Domains),
}

static HELD_IDS: AtomicU64 = AtomicU64::new(0);

impl Held {
    fn new(summary: LetPa, made: Made, orders: Orders, widest: Option<u64>) -> Arc<Held> {
        Arc::new(Held {
            id: HELD_IDS.fetch_add(1, atomic::Ordering::Relaxed),
            summary,
            made,
            orders,
            widest,
        })
    }

    /// What the input `v`, of product `q` in a scope of binding orders `orders`, adds there:
    /// a failure unless it is the binding it was and its integers lie within those it was made
    /// over.
    fn leaf(&self, orders: &Orders, v: &Arc<str>, q: &Product) -> images::Leaf {
        let made = match &self.made {
            Made::Scope(names) => names.get(v).map(Product::ints),
            Made::Given(doms) => doms.get(v),
        };
        let holds =
            made.is_some_and(|d| q.ints().is_subset(d)) && orders.get(v) == self.orders.get(v);
        images::Leaf {
            shift: Shift::ZERO,
            fails: usize::from(!holds),
            premises: Premises::new(),
        }
    }
}

impl PartialEq for Held {
    fn eq(&self, _: &Held) -> bool {
        true
    }
}

impl fmt::Debug for Held {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("..")
    }
}

/// For each held summary, by its id, what it read in the scope of its last read
/// ([`images::Read`]), with the orders of the bindings there, from which the next read is
/// found ([`Scope::holds`]). A cache shared by the copies of a scope, equal in every scope:
/// a read finds the same whichever earlier read it starts from.
/// What one summary read: the scope's names, the summary with the orders of the scope's
/// bindings, and the tree of its inputs.
type HeldRead = images::Read<(Arc<Held>, Orders), Product>;

/// What a test last read of one summary: the scope's names, and the tree of the bounds of the
/// summary's terms over the inputs there ([`Scope::term_read`]).
type BoundsRead = images::Read<(), Product, TermBounds>;

/// The reads of each held summary ([`HeldRead`]), and those of tests ([`BoundsRead`]).
#[derive(Clone, Default)]
struct Reads(
    Arc<Mutex<HashMap<u64, HeldRead>>>,
    Arc<Mutex<HashMap<u64, BoundsRead>>>,
);

impl PartialEq for Reads {
    fn eq(&self, _: &Reads) -> bool {
        true
    }
}

impl fmt::Debug for Reads {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("..")
    }
}

/// Whether each name of a scope no state reaches is already the bottom
/// ([`Scope::empty_if_bottom`]): a cache, equal in every scope, so that the arms a walk shows
/// below a test no state passes empty the names once and not once each.
#[derive(Clone, Copy, Default)]
struct Emptied(bool);

impl PartialEq for Emptied {
    fn eq(&self, _: &Emptied) -> bool {
        true
    }
}

impl fmt::Debug for Emptied {
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
    imbl::OrdMap<Address, Vec<Arc<str>>>,
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

/// A value of names at which every difference constraint among them holds, each edge's weight
/// lowered by the gap of the name it enters: under it no edge has a negative reduced weight,
/// so a Dijkstra search finds the bounds of a tree of blocks projected by shortest paths
/// ([`Scope::shortest`]). It holds at every edge of the relation as of its last projection,
/// except the edges of names it lacks: each edge added is put in it at the next projection,
/// whichever way its tree is projected ([`Scope::repair`]), and a projection of every block
/// ([`Due::All`]) empties it. A cache, equal in every scope, and checked at every edge it is
/// read at.
///
/// A name's gap is the length of the longest run of integers its interval leaves out between
/// its ends ([`hole_gap`]); the potential holds with the gap in `gap`, which is at least the
/// name's own unless the relation records the name as keeping its tree from shortest paths
/// ([`Conjuncts::gapped`], [`Scope::sync_bounds`]). Every cycle `C` of edges then has a
/// weight of at least the sum of the gaps of its names, which is what makes shortest paths
/// with holes the projection ([`Scope::shortest`]).
///
/// Each value is a pair, compared first by its first part: an edge of weight `k` weighs
/// `(k, -1)`, or `(k, 0)` when it is tied, less the gap in both cases, and no edge has a
/// reduced weight below `(0, 0)`. The first parts are then a point as above. A cycle of such
/// weight 0 weighs `(0, -j)` for its `j` edges not tied, which no such point allows unless
/// `j` is 0, so each edge of such a cycle is tied. An edge is tied when it is found on such a
/// cycle ([`Scope::repair`], [`Scope::reseed`]); one whose cycle has gone since stays tied.
#[derive(Clone, Default)]
struct Potential {
    /// Each name's value.
    at: imbl::OrdMap<Arc<str>, (Int, i64)>,
    /// The tied edges, each a conjunct and whether it is its back edge ([`conjuncts::edges`]).
    tied: imbl::OrdSet<(Arc<Formula>, bool)>,
    /// The gap each name's edges in are lowered by; none for 0.
    gap: imbl::OrdMap<Arc<str>, Int>,
}

impl Potential {
    /// The gap the edges into `n` are lowered by.
    fn gap_of(&self, n: &str) -> Int {
        self.gap.get(n).cloned().unwrap_or(Int::ZERO)
    }
}

/// The weight in a [`Potential`] of the edge `e` of conjunct `g`, its back edge with `back`,
/// under the tied edges `tied` and the gaps `gap`.
fn pair_weight(
    tied: &imbl::OrdSet<(Arc<Formula>, bool)>,
    gap: &imbl::OrdMap<Arc<str>, Int>,
    g: &Arc<Formula>,
    back: bool,
    e: &Edge,
) -> (Int, i64) {
    let tied = tied.contains(&(g.clone(), back));
    let w = match e.to.as_ref().and_then(|v| gap.get(v)) {
        Some(d) => &e.weight - d,
        None => e.weight.clone(),
    };
    (w, if tied { 0 } else { -1 })
}

/// `a + b` and `a - b` on the pairs of a [`Potential`].
fn pair_plus(a: &(Int, i64), b: &(Int, i64)) -> (Int, i64) {
    (&a.0 + &b.0, a.1 + b.1)
}

fn pair_minus(a: &(Int, i64), b: &(Int, i64)) -> (Int, i64) {
    (&a.0 - &b.0, a.1 - b.1)
}

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
    /// The seeds whose products changed since the last projection, or that a block of another
    /// tree moved in this one: the only seeds whose bounds may have moved since the bounds were
    /// a fixed point of the edges ([`Scope::bound_pass`]).
    changed: BTreeSet<Arc<str>>,
    /// The conjuncts added, and those of the stars that went or changed, which may now be in
    /// the forest.
    added: BTreeSet<Arc<Formula>>,
    /// The seeds whose tree at the last projection held a conjunct other than a difference
    /// constraint or a bound: their bounds may be no fixed point of the difference constraints
    /// alone. A tree of those alone, with names with holes or a class among them, was
    /// projected block by block to a fixed point: each block is one edge, projected exactly,
    /// and the least value of an edge's head over its projection is at least the least of
    /// its tail plus the weight, so that the bounds were a fixed point of the edges.
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

/// What [`Scope::by_holes`] did with a tree.
enum Ends {
    /// It projected the tree, as [`Scope::shortest`] does.
    Done(Shortest),
    /// It refused the tree, whose names, these, then had their gaps raised to their holes, so
    /// shortest paths project it.
    Paths(Vec<Arc<str>>),
    /// A name has a class, or it refused the tree: the tree is projected block by block.
    Blockwise,
}

/// Why [`Scope::shortest`] left a tree to be projected block by block.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Fall {
    /// The potential lacks a name it reads, as after a projection of every block, or an edge
    /// it reads has a negative reduced weight under it: it is found again after
    /// ([`Scope::reseed`]).
    Potential,
    /// A name it reads has a class, or no product.
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

/// The search of [`Scope::repair`]: puts each edge of `pending` in the potential `pot` of
/// tree `t` of the forest, with the tied edges `tied` and the gaps `gap` ([`Potential`]). A
/// name `pot` lacks takes a value from an edge only when every edge at it is among `added`.
/// `Ok(Some(u))` when an edge closes a cycle of negative weight, and `Err` when the search
/// reads a name `pot` lacks, an edge of negative reduced weight, or a cycle negative only
/// with the gaps; `pot` and `tied` are then to be dropped.
fn put_in(
    relation: &Conjuncts,
    t: BlockId,
    added: &BTreeSet<Arc<Formula>>,
    pending: &[(Arc<Formula>, bool, Edge)],
    pot: &mut imbl::OrdMap<Arc<str>, (Int, i64)>,
    tied: &mut imbl::OrdSet<(Arc<Formula>, bool)>,
    gap: &imbl::OrdMap<Arc<str>, Int>,
) -> Result<Option<Arc<str>>, Fall> {
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
    let gap_of = |n: &Arc<str>| gap.get(n).cloned().unwrap_or(Int::ZERO);
    let zero = (Int::ZERO, 0i64);
    let mut waiting: BTreeSet<(Arc<Formula>, bool)> = pending
        .iter()
        .map(|(g, back, _)| (g.clone(), *back))
        .collect();
    for (g, back, e) in pending {
        waiting.remove(&(g.clone(), *back));
        let (Some(u), Some(v)) = (&e.from, &e.to) else {
            continue;
        };
        // Each round puts the edge in, or finds a cycle of weight 0 through it, whose
        // edges are then tied, and the edge is put in again with their weights raised.
        'round: loop {
            let w = pair_weight(tied, gap, g, *back, e);
            let gamma = match (pot.get(u).cloned(), pot.get(v).cloned()) {
                (None, None) => {
                    new_name(u)?;
                    new_name(v)?;
                    pot.insert(u.clone(), zero.clone());
                    pot.insert(v.clone(), w);
                    break 'round;
                }
                (Some(pu), None) => {
                    new_name(v)?;
                    pot.insert(v.clone(), pair_plus(&pu, &w));
                    break 'round;
                }
                (None, Some(pv)) => {
                    new_name(u)?;
                    pot.insert(u.clone(), pair_minus(&pv, &w));
                    break 'round;
                }
                (Some(pu), Some(pv)) => pair_minus(&pair_plus(&pu, &w), &pv),
            };
            if gamma >= zero {
                break 'round;
            }
            // Each name's potential falls by the least reduced distance from `v` below
            // zero; the new values are kept apart until the search ends, so that the old
            // ones check the edges read. Each name reached keeps the edge it was last
            // reached by, so that a cycle found can be followed back.
            let mut fall: BTreeMap<Arc<str>, (Int, i64)> =
                BTreeMap::from([(v.clone(), gamma.clone())]);
            let mut via: BTreeMap<Arc<str>, (Arc<str>, Arc<Formula>, bool)> = BTreeMap::new();
            let mut heap = BinaryHeap::from([Reverse((gamma, v.clone()))]);
            let mut new: BTreeMap<Arc<str>, (Int, i64)> = BTreeMap::new();
            while let Some(Reverse((gs, s))) = heap.pop() {
                if new.contains_key(&s) || fall.get(&s) != Some(&gs) {
                    continue;
                }
                let ps = pot.get(&s).ok_or(Fall::Potential)?;
                let to_s = pair_plus(ps, &gs);
                for (h, hb, f) in tree_edges(relation, t, &s) {
                    let (Some(from), Some(x)) = (&f.from, &f.to) else {
                        continue;
                    };
                    if *from != s || new.contains_key(x) || waiting.contains(&(h.clone(), hb)) {
                        continue;
                    }
                    let px = pot.get(x).ok_or(Fall::Potential)?;
                    let fw = pair_weight(tied, gap, &h, hb, &f);
                    if pair_minus(&pair_plus(ps, &fw), px) < zero {
                        return Err(Fall::Potential);
                    }
                    let gx = pair_minus(&pair_plus(&to_s, &fw), px);
                    if gx >= zero {
                        continue;
                    }
                    if x == u {
                        if gx.0 < Int::ZERO {
                            // The cycle's weight without the gaps: each of its names
                            // lowered the edge into it by its gap.
                            let mut weight = &gx.0 + &gap_of(u);
                            let mut at = s.clone();
                            weight = &weight + &gap_of(&at);
                            while let Some((before, _, _)) = via.get(&at) {
                                at = before.clone();
                                weight = &weight + &gap_of(&at);
                            }
                            return if weight < Int::ZERO {
                                Ok(Some(u.clone()))
                            } else {
                                Err(Fall::Potential)
                            };
                        }
                        // A cycle of weight 0: the edge, the one into `u`, and those
                        // back to `v`.
                        tied.insert((g.clone(), *back));
                        tied.insert((h, hb));
                        let mut at = s.clone();
                        while let Some((before, k, kb)) = via.get(&at) {
                            tied.insert((k.clone(), *kb));
                            at = before.clone();
                        }
                        continue 'round;
                    }
                    if fall.get(x).is_none_or(|c| gx < *c) {
                        fall.insert(x.clone(), gx.clone());
                        via.insert(x.clone(), (s.clone(), h.clone(), hb));
                        heap.push(Reverse((gx, x.clone())));
                    }
                }
                new.insert(s, to_s);
            }
            for (s, ps) in new {
                pot.insert(s, ps);
            }
            break 'round;
        }
    }
    Ok(None)
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

/// Which part of the relation an entry of [`Scope::projected`] is for: the conjunct it is
/// projected for, or the least of the constraints for the part of the constraints alone; and
/// the leaf of the star whose block the part is projected in, `None` in the forest. A
/// conjunct among the hubs of a star is a part of the star's block and of the hubs' block,
/// each with other constraints and names, and one key for both made each block find the
/// other's snapshot there and project every such part again at each test (item
/// NARROW-lazy-settle). What the part is projected with is beside the key, not in it
/// ([`PartWith`]): in the key, each change of a block's equalities, or of its constraints for
/// their own part, left the part's old entry in the map, which grew by one entry for each
/// change until the conjunct left (item ST-projected-stale).
pub type PartKey = (Formula, Option<Arc<str>>);

/// What a part of the relation was projected with: the equalities among the constraints it is
/// projected with, sorted, and the constraints among them on the terms the part's conjunct
/// compares, as `x - y` in `x - y >= 5 || y - x >= 5` (the box of its terms), or, for the part
/// of the constraints alone, their conjunction. A part is projected again when an equality,
/// or a constraint on one of its terms, joins or leaves them, as `-2 <= x - y <= 2` after the
/// disjunction above, which leaves no value. A constraint on other terms alone does not make
/// a conjunct's part due, so that a new constraint costs the parts on its term and not the
/// block's (the walk `v_i + w <= 0 || v_(i+1) - w >= 1` through the shared name `w`).
pub type PartWith = (Arc<[Con]>, Option<Formula>);

/// The term of `c` with its sign chosen so that its first coefficient is positive: one key for
/// `x - y >= 5` and `y - x >= 5`.
fn unsigned(c: &Con) -> BTreeMap<Atom, Int> {
    if c.lin.terms.values().next().is_some_and(Int::is_negative) {
        c.lin.terms.iter().map(|(a, k)| (a.clone(), -k)).collect()
    } else {
        c.lin.terms.clone()
    }
}

/// Each of `conjuncts` that is not a constraint, with the constraints, and the constraints
/// alone when there are any; each part with its key and what it is projected with, in the
/// star of leaf `leaf` if any.
fn split<'a>(
    conjuncts: impl Iterator<Item = &'a Formula>,
    leaf: Option<&Arc<str>>,
) -> Vec<(PartKey, PartWith, Formula)> {
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
    let eqs: Arc<[Con]> = eqs.into();
    // The constraints on each term, either sign, which only the other conjuncts read.
    let mut on: BTreeMap<BTreeMap<Atom, Int>, Vec<Con>> = BTreeMap::new();
    for g in cons.iter().filter(|_| !others.is_empty()) {
        if let Formula::Con(c) = g {
            on.entry(unsigned(c)).or_default().push(c.clone());
        }
    }
    let least = cons.iter().min().map(|&c| c.clone());
    let base = Formula::and(cons.into_iter().cloned().collect());
    let mut parts: Vec<(PartKey, PartWith, Formula)> = others
        .into_iter()
        .map(|g| {
            let terms: BTreeSet<BTreeMap<Atom, Int>> = g.cons().into_iter().map(unsigned).collect();
            let mut boxed: Vec<Con> = terms
                .iter()
                .filter_map(|t| on.get(t))
                .flatten()
                .cloned()
                .collect();
            boxed.sort_unstable();
            let boxed = Formula::and(boxed.into_iter().map(Formula::Con).collect());
            (
                (g.clone(), leaf.cloned()),
                (eqs.clone(), Some(boxed)),
                Formula::and(vec![g.clone(), base.clone()]),
            )
        })
        .collect();
    if let Some(least) = least.filter(|_| base != Formula::top()) {
        parts.push(((least, leaf.cloned()), (eqs, Some(base.clone())), base));
    }
    parts
}

/// Top-level conjuncts of a relation projected together: a block of [`Conjuncts::blocks`].
struct Block {
    /// What is projected: each conjunct that is not a constraint, with the constraints, and
    /// the constraints alone, each with the conjunct it is projected for ([`split`]). A new
    /// conjunct then costs its own part, not the block's.
    parts: Vec<(PartKey, PartWith, Formula)>,
    /// The names they mention.
    names: Vec<Arc<str>>,
    /// The leaf, when the block is a star ([`Conjuncts::star`]).
    leaf: Option<Arc<str>>,
    /// Its conjuncts, of which [`Scope::project_block`] finds the threshold-implication
    /// component, when it is one ([`threshold::shape`]), only when a part is due: a block
    /// built to ask whether a leaf is stale ([`Scope::stale`]) does not need it.
    core: Vec<Arc<Formula>>,
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
            core: gs,
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

/// A written constraint's address with the values of its static names.
pub type Enumerated = (Address, Vec<(Arc<str>, Value)>);

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
    /// Why it was left undecided.
    pub cause: Cause,
}

/// The sets a refused question left its variables, each by its name in the scope: a set holds
/// every value the question allows the variable and may hold more. For a refused projection
/// they are the bounds the box stage gives the rows (DESIGN step L1.38), and for a refused test
/// the box of its preimage. Empty where the question left no variable such a set: a case of an
/// alternative set aside, or the ends of names with holes.
pub type Kept = Arc<BTreeMap<Arc<str>, IntervalSet>>;

/// The sets of `a` and `b` combined by `f` for each variable both hold; with `either`, a
/// variable only one holds keeps its set, and otherwise it is left out. O(m log m) in the m
/// variables.
fn merged(
    a: &BTreeMap<Arc<str>, IntervalSet>,
    b: &BTreeMap<Arc<str>, IntervalSet>,
    f: impl Fn(&IntervalSet, &IntervalSet) -> IntervalSet,
    either: bool,
) -> BTreeMap<Arc<str>, IntervalSet> {
    let mut out = BTreeMap::new();
    for (n, x) in a {
        match b.get(n) {
            Some(y) => {
                out.insert(n.clone(), f(x, y));
            }
            None if either => {
                out.insert(n.clone(), x.clone());
            }
            None => {}
        }
    }
    if either {
        for (n, y) in b {
            out.entry(n.clone()).or_insert_with(|| y.clone());
        }
    }
    out
}

/// Why a question was left undecided.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Cause {
    /// The integer solver refused it.
    Solver(presburger::Refusal),
    /// The ends of names with holes are not found exactly: the difference constraints join
    /// `names` names, both ways, in more than one cycle, and more than two of them, `holed`,
    /// have holes (item ST-holes-moves). It depends on the constraints and on which names
    /// have holes alone.
    Holes {
        /// The names with holes, as written, in order.
        holed: Vec<Arc<str>>,
        /// The number of names the constraints join.
        names: usize,
    },
}

impl From<presburger::Refusal> for Cause {
    fn from(r: presburger::Refusal) -> Cause {
        Cause::Solver(r)
    }
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

/// Whether `text` has `||` outside every parenthesis, O(its length).
fn or_outside_parentheses(text: &str) -> bool {
    let mut depth = 0usize;
    let b = text.as_bytes();
    for (i, &c) in b.iter().enumerate() {
        match c {
            b'(' => depth += 1,
            b')' => depth = depth.saturating_sub(1),
            b'|' if depth == 0 && b.get(i + 1) == Some(&b'|') => return true,
            _ => {}
        }
    }
    false
}

/// The sets a refused question left its variables, as a warning names them ([`shown`]). Each
/// list is in the order of the names in the scope, each name as the program wrote it.
enum Shown {
    /// It left no variable a set.
    None,
    /// The sets of the variables with a bound, each as a type, `` `b: int[-4..=16]` ``, and
    /// the variables left every integer, each in backquotes; each list joined by commas and a
    /// last "and".
    Bounds {
        /// The variables with a bound and their sets.
        bounded: String,
        /// The variables with none.
        open: String,
    },
    /// The variables whose sets are empty, so that no values meet the question.
    NoValue(String),
}

/// `items` joined by commas and a last "and": `a`, `a and b`, `a, b and c`.
fn listed_and(items: &[String]) -> String {
    match items.split_last() {
        None => String::new(),
        Some((last, [])) => last.clone(),
        Some((last, rest)) => format!("{} and {last}", rest.join(", ")),
    }
}

/// The sets `kept` as a warning names them ([`Shown`]). O(the length of the text).
fn shown(kept: &Kept) -> Shown {
    if kept.is_empty() {
        return Shown::None;
    }
    let quoted = |n: &Arc<str>| format!("`{}`", written_name(n));
    let empty: Vec<String> = (kept.iter())
        .filter(|(_, x)| x.is_empty())
        .map(|(n, _)| quoted(n))
        .collect();
    if !empty.is_empty() {
        return Shown::NoValue(listed_and(&empty));
    }
    let (open, bounded): (Vec<_>, Vec<_>) =
        kept.iter().partition(|(_, x)| **x == IntervalSet::top());
    let bounded: Vec<String> = (bounded.into_iter())
        .map(|(n, x)| format!("`{}: int{x}`", written_name(n)))
        .collect();
    let open: Vec<String> = open.into_iter().map(|(n, _)| quoted(n)).collect();
    Shown::Bounds {
        bounded: listed_and(&bounded),
        open: listed_and(&open),
    }
}

impl Refused {
    /// The warning that reports this refusal, with its derivation and its repairs, and the sets
    /// `sets` it left its variables.
    fn warning(&self, sets: &Kept) -> Warning {
        let c = &self.constraint;
        let cause = match &self.cause {
            Cause::Solver(r) => r,
            Cause::Holes { holed, names } => {
                let holed: Vec<String> = holed.iter().map(|n| format!("`{n}`")).collect();
                return Warning {
                    message: "the ends of names with holes are not found exactly".to_string(),
                    steps: vec![
                        format!("the constraints `{c}` hold in the scope"),
                        format!(
                            "they join their {names} names both ways in more than one cycle, \
                             and {} of them have holes: {}; the ends of such names are found \
                             exactly when at most two of them have holes",
                            holed.len(),
                            holed.join(", ")
                        ),
                        "the names of the constraints are narrowed one block at a time, and \
                         their ends may be wider than the constraints make them"
                            .to_string(),
                    ],
                };
            }
        };
        // A refused projection or test keeps sets for its variables, and its cause ends by
        // naming them; a case set aside keeps none, and its cause ends with the search.
        let last = |source: &str| match shown(sets) {
            Shown::None => cause.to_string(),
            Shown::Bounds { bounded, open } => {
                let text = match (bounded.is_empty(), open.is_empty()) {
                    (true, _) => format!(
                        "The checker stopped there, and {source} rule out no value: {open} may \
                         still be any whole number"
                    ),
                    (false, true) => format!("The checker stopped there, with {source}: {bounded}"),
                    (false, false) => format!(
                        "The checker stopped there, with {source}: {bounded}; {open} may still \
                         be any whole number"
                    ),
                };
                cause.closed_by(&text).to_string()
            }
            Shown::NoValue(names) => cause
                .closed_by(&format!(
                    "The checker stopped there, but {source} leave no value for {names}"
                ))
                .to_string(),
        };
        let (given, asked, kept) = match &self.asked {
            Asked::Test { outcome } => (
                format!("here the test `{c}` is {outcome}"),
                format!(
                    "the checker could not work out which values its variables can take when \
                     it is {outcome}: {}",
                    last("the bounds it found on the test's variables")
                ),
                "so the test narrows the values of its variables here only to those bounds, \
                 which may be wider than it allows",
            ),
            Asked::Projection => (
                format!("here the conditions `{c}` hold"),
                format!(
                    "the checker could not work out which values each of their variables can \
                     take: {}",
                    last(
                        "the bounds that each condition gives each variable from the bounds of the others"
                    )
                ),
                "so here each of their variables keeps only those bounds, which may be wider \
                 than the conditions allow",
            ),
            Asked::Disjunct => (
                format!("here the conditions `{c}` hold"),
                format!(
                    "the checker could not work out which values one case of an alternative \
                     among them allows (a side of a `||`), so it set that case aside: {cause}"
                ),
                "so the conditions narrow the values of their variables without that case",
            ),
            Asked::Onto(n) => (
                format!("here the conditions `{c}` hold"),
                format!(
                    "the checker could not work out which values `{n}` can take: {}",
                    last(&format!(
                        "the bounds that each condition gives `{n}` from the bounds of the others"
                    ))
                ),
                "so here that variable keeps only those bounds, which may be wider than the \
                 conditions allow",
            ),
        };
        // The repairs rewrite the test or the conditions as printed: a scope is built from
        // kernel terms and has no program text (the front end, which has it, rewrites a
        // refused function as written). A printed `||` outside parentheses is grouped, so the
        // stated value joins all of it.
        let names = presburger::names_in(c);
        let joined = if or_outside_parentheses(c) {
            format!("({c})")
        } else {
            c.to_string()
        };
        let what = match self.asked {
            Asked::Test { .. } => "the test",
            _ => "the conditions",
        };
        let repairs = cause.repairs(&presburger::Written {
            what,
            head: "",
            tail: "",
            split: None,
            conjuncts: &[joined.as_str()],
            names: &names,
        });
        Warning {
            message: "the checker knows less here about the values of some variables than \
                      the program's conditions say, so it may reject or warn about code that \
                      is correct; it does not accept code that is wrong"
                .to_string(),
            steps: [given, asked, kept.to_string()]
                .into_iter()
                .chain(repairs)
                .collect(),
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
            emptied: Emptied::default(),
            enumerated: imbl::OrdSet::new(),
            projected: imbl::OrdMap::new(),
            exact,
            exactly: imbl::OrdMap::new(),
            refusals: imbl::OrdMap::new(),
            bindings: imbl::OrdMap::new(),
            orders: imbl::OrdMap::new(),
            reads: Reads::default(),
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
    /// of its names or of the satellites its hubs admit than they now have, or with other
    /// free conjuncts at its hubs ([`Conjuncts::core`]), and there settling the leaf,
    /// projecting its star with those conjuncts and reducing as [`Scope::reduce`] does, gives
    /// the eager product. No written constraint holds of a leaf, so its product reaches no
    /// other name but through its star, whose projection onto its hubs is a bound on each
    /// alone, through the leaf's greatest or least member, which a cut of the leaf by the
    /// hubs' moves keeps, so no hub moves; and the cut is a half-line that holds that member,
    /// so it empties no leaf, and the scope is bottom exactly when the eager one is. A star
    /// that goes or changes makes its leaf's conjuncts due at the next projection, which
    /// settles the leaf.
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
                .any(|(key, with, g)| !self.is_projected(key, with, &syms(g)))
            {
                out.push(block);
            }
        }
        out
    }

    /// Settles the stale leaves among `names` ([`Scope::lazy`]): projects each one's star,
    /// then reduces, which costs the leaves settled.
    ///
    /// Two stars of one class have one core but for the name of the leaf
    /// ([`Conjuncts::class_core`]), so the projection of the second, when its other names and
    /// its leaf's interval and class are as the first's were, gives its leaf the first's
    /// projection and moves nothing else, as the first moved nothing else. The stars at hubs
    /// whose free conjuncts changed, as those of a satellite ([`Conjuncts::star`]), are then
    /// projected once for the class and not once for each leaf. A projection the solver
    /// refused in part, which records the leaf's name, is not reused. Each part's projection
    /// reads only the part and the interval and class of each name it mentions
    /// (`Scope::framed`), and the parts of the two stars are one but for the leaf's name, so
    /// the two projections are one but for that name. Test
    /// `l01_39_reduced_product::lazy::leaves_of_one_class_settled_together_get_what_each_gets_alone`.
    pub fn settle<'a>(&mut self, names: impl IntoIterator<Item = &'a Arc<str>>) {
        if !self.lazy || self.bottom {
            return;
        }
        let blocks = self.stale(names);
        if blocks.is_empty() {
            return;
        }
        // Per class, the other names and the leaf's interval and class before its last
        // projection, and the leaf's interval after.
        type Before = (Projected, (IntervalSet, Congruence));
        let mut done: BTreeMap<conjuncts::Class, (Before, IntervalSet)> = BTreeMap::new();
        for b in &blocks {
            let class = b.leaf.as_ref().and_then(|x| {
                let c = self.relation.class_of(x)?.clone();
                Some((x.clone(), c))
            });
            let Some((leaf, class)) = class else {
                self.project_block(b);
                continue;
            };
            let others: Vec<Arc<str>> = b.names.iter().filter(|n| **n != leaf).cloned().collect();
            let own = |s: &Scope| {
                let p = s.get(&leaf);
                (p.ints().clone(), p.cell.congruence.element.clone())
            };
            let before: Before = (self.snapshot(&others), own(self));
            if let Some((_, after)) = done.get(&class).filter(|(was, _)| *was == before) {
                let after = after.clone();
                if let Some(p) = self.names.get_mut(&leaf) {
                    let prem = p.premises();
                    p.meet_ints(after, &prem);
                }
                for (key, with, g) in &b.parts {
                    let at = self.snapshot(&syms(g));
                    self.projected.insert(key.clone(), (with.clone(), at));
                }
                continue;
            }
            let refused = self.refusals.len();
            self.project_block(b);
            if self.refusals.len() == refused
                && !self.get(&leaf).ints().is_empty()
                && self.snapshot(&others) == before.0
            {
                done.insert(class, (before, self.get(&leaf).ints().clone()));
            }
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
            Some((s, doms)) if self.summarizes(&p) => {
                let made = Made::Given(doms.clone());
                Some(Held::new(s.clone(), made, self.orders.clone(), None))
            }
            _ => None,
        };
        if let Some(held) = &summary
            && self.holds(held)
            && let Some(image) = (held.summary).image(|v| self.names.get(v).map(Product::ints))
        {
            let mut premises = Premises::new();
            for v in held.summary.vars() {
                premises.extend(&self.names[v].premises());
            }
            p.meet_ints(image, &premises);
        }
        // Until no reduction changes a domain; each change is a meet, so the loop descends.
        while p.reduce_domains() {}
        let summary = match given {
            None => self.summarize(e, &p),
            Some(_) => summary,
        };
        let order = self.clock;
        let binding = Binding {
            function: matches!(**e, Term::Lam(..)).then(|| e.clone()),
            summary,
        };
        self.clock += 1;
        if !self.bottom && !p.is_empty() && !self.names.contains_key(x) {
            let before = self.names.clone();
            self.names.insert(x.clone(), p);
            self.bindings.insert(x.clone(), binding);
            self.orders.insert(x.clone(), order);
            self.seen_fresh(x, &before);
            return Unbind::Fresh(x.clone());
        }
        let saved = Unbind::Saved(Box::new(self.clone()));
        if self.bottom {
            return saved;
        }
        // The stars that forgetting `x` takes or changes, and their leaves keep what they
        // have: those at `x` as a hub, and those whose hub it leaves with too few conjuncts
        // or with one no star holds, and those whose projection reads a conjunct at `x`, such as
        // the stars at the hubs a satellite `x` relates to ([`Conjuncts::around`]). No
        // reduction follows to settle them, so they are settled first, against the relation
        // they were stars of.
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
            .chain(self.relation.around(x))
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
        let gone: Vec<Address> = self.written_by.of(x).cloned().collect();
        for k in &gone {
            self.unwrite(k);
        }
        self.bindings.insert(x.clone(), binding);
        self.orders.insert(x.clone(), order);
        self.names.insert(x.clone(), p);
        if self.names[x].is_empty() {
            self.bottom = true;
            self.empty_if_bottom();
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
                self.orders.remove(&x);
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
    /// and the others are inputs. It keeps the integers of its inputs here as the scope's
    /// names, and the orders of their bindings as the scope's orders, each a copy in `O(1)` of
    /// a persistent map. Costs `e`'s size and the domains of the inputs it reads itself, not
    /// the summaries of the names it reads ([`Scope::inputs_and_lets`]), beside checking that
    /// those hold ([`Scope::holds`]).
    fn summarize(&self, e: &Term, p: &Product) -> Option<Arc<Held>> {
        if !self.summarizes(p) {
            return None;
        }
        let (inputs, lets, widest) = self.inputs_and_lets(&stage::free(e), false);
        let s = let_summary(e, &inputs, lets)?;
        let made = Made::Scope(self.names.clone());
        Some(Held::new(s, made, self.orders.clone(), widest))
    }

    /// Whether a name of product `p` bound here keeps a summary: an integer in a reachable
    /// scope.
    fn summarizes(&self, p: &Product) -> bool {
        !self.bottom && p.ty.element.subtype(&Type::int())
    }

    /// Whether the summary `held` holds here: each input it reads is still the binding it was
    /// made over, and that input's integers lie within those it was made over (a scope's
    /// integers only narrow while a name is bound, but a name bound again is another binding).
    ///
    /// The inputs are kept in a tree with the number that fail ([`images::Read`]), found from
    /// the tree of `held`'s last read, or else, for its first, of the last read of the summary
    /// with the most inputs among those its value reads ([`Held::widest`]), by setting the
    /// inputs where the two scopes' names or orders, or the two summaries' inputs, integers or
    /// orders made over, differ ([`images::updated`]); afresh from the inputs the scope has,
    /// when there is none, the summaries were not both made in a scope, or the differences
    /// are as many as the inputs ([`images::fresh`]). Each read costs the lesser of the
    /// differences and the inputs, times `O(log k)` for `k` inputs: a chain
    /// `x_k = x_(k-1) + q_k` under a test of each `q_k` reads `x_(k-1)` at the binding of
    /// `x_k` from `x_(k-2)` read at that of `x_(k-1)`, which differ at a few names, where
    /// checking each input cost `O(k)` a binding and the chain `Θ(d²)` (item PA-walk-multi).
    /// The answer is the same whichever read it starts from.
    fn holds(&self, held: &Arc<Held>) -> bool {
        // The names whose products or orders differ between the scope of `r` and `s`.
        fn here<'a>(r: &'a HeldRead, s: &'a Scope) -> impl Iterator<Item = &'a Arc<str>> + 'a {
            let names = images::changed(&r.names, &s.names);
            names.chain(images::changed(&r.sum.1, &s.orders))
        }
        let vars = held.summary.vars();
        let limit = vars.len().min(self.names.len());
        let leaf = |v: &Arc<str>, q: &Product| held.leaf(&self.orders, v, q);
        let mut reads = self.reads.0.lock().unwrap_or_else(PoisonError::into_inner);
        let tree = {
            match reads.get(&held.id) {
                Some(r) => images::updated(&r.tree, here(r, self), vars, &self.names, limit, leaf),
                None => (held.widest.and_then(|w| reads.get(&w))).and_then(|r| {
                    let base = &r.sum.0;
                    let (Made::Scope(was), Made::Scope(now)) = (&base.made, &held.made) else {
                        return None;
                    };
                    let inputs = (base.summary.vars().diff(vars)).map(|d| match d {
                        imbl::ordset::DiffItem::Add(v) | imbl::ordset::DiffItem::Remove(v) => v,
                    });
                    let changed = (inputs.chain(images::changed(was, now)))
                        .chain(images::changed(&base.orders, &held.orders))
                        .chain(here(r, self));
                    images::updated(&r.tree, changed, vars, &self.names, limit, leaf)
                }),
            }
        }
        .unwrap_or_else(|| images::fresh(vars, &self.names, leaf));
        let holds = images::total(&tree).fails == 0 && images::len(&tree) == vars.len();
        let read = images::Read {
            names: self.names.clone(),
            sum: (held.clone(), self.orders.clone()),
            tree,
        };
        reads.insert(held.id, read);
        holds
    }

    /// The summary of the integer `x` is bound to, with the id it is held by, when it has one
    /// and it holds ([`Scope::holds`]).
    fn summary(&self, x: &Arc<str>) -> Option<(LetPa, u64)> {
        let held = self.bindings.get(x)?.summary.as_ref()?;
        self.holds(held).then(|| (held.summary.clone(), held.id))
    }

    /// The integer names of `free`, as inputs over their integers, or, when bound by a `let`
    /// with a summary that holds ([`Scope::summary`]), as names read through it, and the id
    /// of the summary with the most inputs among these. With `all`, for a test, which narrows
    /// the inputs of each summary too ([`let_narrowing`]), a summary over two or more inputs
    /// is read through the tree of its terms' bounds ([`Scope::term_read`]), its inputs not
    /// among the inputs, so that the test costs the inputs it narrows and not all `k`, and the
    /// input of a summary over one is an input, read in `O(log n)`. A test reads no scope no
    /// state reaches (`Scope::narrow_node`, `Scope::exclude`). Without `all`, only the input
    /// of a summary over one, which a term of a value other than a sum reads it through
    /// (`2 * y` is a sum, `y * y` is not), for a value's summary ([`let_summary`]), which does not
    /// read the inputs of the summaries it adds: so a chain of bindings each adding the one
    /// before costs each binding its own term, not the inputs of all before it.
    fn inputs_and_lets(
        &self,
        free: &BTreeSet<Arc<str>>,
        all: bool,
    ) -> (Domains, Lets, Option<u64>) {
        debug_assert!(
            !(all && self.bottom),
            "a test read in a scope no state reaches"
        );
        let int = Type::int();
        let mut inputs = Domains::new();
        let mut lets = Lets::new();
        let mut widest: Option<(usize, u64)> = None;
        for n in free {
            let p = self.get(n);
            if !self.names.contains_key(n) || !p.ty.element.subtype(&int) {
                continue;
            }
            match self.summary(n) {
                Some((summary, id)) => {
                    let k = summary.vars().len();
                    if widest.is_none_or(|(w, _)| k > w) {
                        widest = Some((k, id));
                    }
                    let mut read = None;
                    if all && k > 1 {
                        read = Some(Arc::new(self.term_read(&summary, id)) as _);
                    } else if all || k == 1 {
                        for v in summary.vars() {
                            inputs.insert(v.clone(), self.get(v).ints().clone());
                        }
                    }
                    lets.insert(
                        n.clone(),
                        LetIn {
                            summary,
                            ints: p.ints().clone(),
                            read,
                        },
                    );
                }
                None => _ = inputs.insert(n.clone(), p.ints().clone()),
            }
        }
        (inputs, lets, widest.map(|(_, id)| id))
    }

    /// The inputs of `summary`, held by the id `id`, as a test reads them here: each input's
    /// integers, and the bounds of the summary's term of each ([`LetPa::term_bounds`]) in a
    /// tree found from that of the last test of the summary by setting the inputs whose
    /// products differ between the two scopes ([`images::updated`]), or afresh when there is
    /// none or the differences are as many as the inputs ([`images::fresh`]). Costs the lesser
    /// of the differences and the inputs, times `O(log k)` for `k` inputs: `k` tests of one
    /// name, each narrowing a few names, cost `O(k log k)`, where reading the inputs cost
    /// `O(k)` a test (item PA-letpre-linear). The summary holds here ([`Scope::holds`]), so
    /// the scope has each of its inputs.
    fn term_read(&self, summary: &LetPa, id: u64) -> images::TermRead<Product> {
        let vars = summary.vars();
        let limit = vars.len().min(self.names.len());
        let leaf = |v: &Arc<str>, q: &Product| summary.term_bounds(v, q.ints());
        let mut reads = self.reads.1.lock().unwrap_or_else(PoisonError::into_inner);
        let tree = (reads.get(&id))
            .and_then(|r| {
                let changed = images::changed(&r.names, &self.names);
                images::updated(&r.tree, changed, vars, &self.names, limit, leaf)
            })
            .unwrap_or_else(|| images::fresh(vars, &self.names, leaf));
        let read = images::Read {
            names: self.names.clone(),
            sum: (),
            tree: tree.clone(),
        };
        reads.insert(id, read);
        images::TermRead {
            names: self.names.clone(),
            vars: vars.clone(),
            tree,
            ints: Product::ints,
        }
    }

    /// Records `t` as a written constraint that holds, by its content address: a constraint
    /// that differs from one already written only in the names of its binders is that one.
    pub fn write(&mut self, t: Term) {
        let k = Address::of(&t);
        self.unwrite(&k);
        let free: Vec<Arc<str>> = stage::free(&t).into_iter().collect();
        for n in &free {
            self.written_by.add(n, &k);
            self.relation.pin(n, true);
        }
        self.written.insert(k, free);
    }

    /// Forgets the written constraint of address `k`.
    fn unwrite(&mut self, k: &Address) {
        if let Some(free) = self.written.remove(k) {
            for n in &free {
                self.written_by.remove(n, k);
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
            let order = self.orders[name];
            let reads = stage::free(f);
            let later = |m: &Arc<str>| self.orders.get(m).is_some_and(|c| *c >= order);
            if reads.iter().any(later) {
                continue;
            }
            reached.push((order, name, f));
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
        (self.refusals.iter())
            .map(|(r, kept)| r.warning(kept))
            .collect()
    }

    /// Keeps `r`, a question the integer solver left undecided while this scope was narrowed or
    /// projected, once, with `kept`, the sets it left its variables. The same question asked
    /// again in this scope keeps the meet of the sets of each time, each of which holds every
    /// value the question allows here, so the sets do not depend on the order the questions
    /// were met in. O(log k) in the k refusals kept and O(m log m) in the m variables of `kept`.
    /// Every refused test and part of the relation is kept through here.
    pub fn refuse(&mut self, r: Refused, kept: Kept) {
        let kept = match self.refusals.get(&r) {
            Some(old) if *old != kept => Arc::new(merged(old, &kept, IntervalSet::meet, true)),
            _ => kept,
        };
        self.refusals.insert(r, kept);
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
            let (DiffItem::Add(_, free)
            | DiffItem::Remove(_, free)
            | DiffItem::Update { old: (_, free), .. }) = d;
            differ.extend(free.iter().cloned());
        }
        let mut leaves = differ.clone();
        for side in [&self.relation, &other.relation] {
            for n in &differ {
                leaves.extend(side.hanging(n).flat_map(|g| conjuncts::names(g)));
                leaves.extend(side.around(n));
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
            if let DiffItem::Remove(k, free) = d {
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
        // intervals lie within its projection, and the join's within their union. A part
        // projected with other equalities or constraints on the two sides is not.
        let mut projected = self.projected.clone();
        for d in self.projected.diff(&other.projected) {
            match d {
                DiffItem::Remove(k, _) => {
                    projected.remove(k);
                }
                DiffItem::Update {
                    old: (k, (with, v)),
                    new: (_, (theirs, _)),
                } => {
                    if with != theirs {
                        projected.remove(k);
                        continue;
                    }
                    let at = v
                        .iter()
                        .map(|(n, _, _)| {
                            let p = names.get(n).cloned().unwrap_or_else(Product::top);
                            (
                                n.clone(),
                                p.ints().clone(),
                                p.cell.congruence.element.clone(),
                            )
                        })
                        .collect();
                    projected.insert(k.clone(), (with.clone(), at));
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
        // A question refused on both sides keeps, for each variable, the join of its sets, since
        // the join's values are those of either side; one refused on one side keeps that
        // side's sets.
        for d in self.refusals.diff(&other.refusals) {
            match d {
                DiffItem::Add(r, kept) => {
                    refusals.insert(r.clone(), kept.clone());
                }
                DiffItem::Update {
                    old: (r, mine),
                    new: (_, theirs),
                } => {
                    let both = merged(mine, theirs, IntervalSet::join, false);
                    refusals.insert(r.clone(), Arc::new(both));
                }
                DiffItem::Remove(..) => {}
            }
        }
        Scope {
            relation,
            written,
            written_by,
            bottom: false,
            emptied: Emptied::default(),
            enumerated,
            projected,
            exact: self.exact,
            exactly,
            refusals,
            // Both sides narrow one scope, which bound the names; neither binds one the other
            // does not.
            bindings: self.bindings.clone(),
            orders: self.orders.clone(),
            reads: self.reads.clone(),
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

    /// Whether some state may reach this scope where `test` gave `outcome`: false only when
    /// [`Scope::assume_case`] would be bottom, and then not always, since the test's relation
    /// taken whole is not kept. A test that splits into cases, as `!(a >= n && a >= m)`, stops
    /// at the first case some state reaches and joins none: a join reads the relation of
    /// both cases, which under `k` stars at a hub is `k` conjuncts.
    pub fn reaches(&self, test: &Term, outcome: bool, premises: &Premises) -> bool {
        if self.bottom {
            return false;
        }
        let mut s = self.clone();
        s.settle_test(test);
        let plain = plain_test(test, &s);
        let (tree, pol) = Tree::of(plain.as_ref().unwrap_or(test));
        let value = outcome == pol;
        match &tree.nodes[0].kind {
            Kind::Nest(and, _) if *and != value => {
                s.cases(&tree, 0, value, premises, true).is_some()
            }
            Kind::If(_) => s.cases(&tree, 0, value, premises, true).is_some(),
            _ => {
                s.narrow_node(&tree, 0, value, premises);
                s.reduce_case();
                !s.bottom
            }
        }
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
            Kind::Nest(..) | Kind::If(_) => match self.cases(tree, n, value, prem, false) {
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
    /// nest's nodes is narrowed by a call within this one. With `any`, the first case some
    /// state reaches, unjoined ([`Scope::reaches`]).
    fn cases(
        &self,
        tree: &Tree,
        n: usize,
        value: bool,
        prem: &Premises,
        any: bool,
    ) -> Option<Scope> {
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
                        None if any && !s.bottom => return Some(s),
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
                    if any && !s.bottom {
                        return Some(s);
                    }
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
            // A name whose finite set lists its integers (`x: {0, 1, 2}`) is a listed input,
            // its domain the interval met with the list, so that the preimage may enumerate it
            // at a cost in the members listed; any other name is a range, whatever its width.
            let mut listed_names = Listed::new();
            let doms: Domains = inputs
                .iter()
                .map(|n| {
                    let p = self.get(n);
                    let d = match listed(&p) {
                        Some(vs) => {
                            listed_names.insert(n.clone());
                            p.ints().meet(&IntervalSet::from_pieces(
                                vs.iter().map(|&v| (End::of(v), End::of(v))).collect(),
                            ))
                        }
                        None => p.ints().clone(),
                    };
                    (n.clone(), d)
                })
                .collect();
            let pre = preimage_listed(t, &doms, &listed_names, &Demand::Bool(outcome));
            exact = pre.exact;
            if let Some(cause) = pre.refusal {
                // What the refused preimage kept: its bounds on the test's variables, which
                // hold every value at which the test has this outcome.
                let kept: Kept = Arc::new(
                    (pre.domains.iter())
                        .filter(|(n, _)| self.names.contains_key(*n))
                        .map(|(n, d)| (n.clone(), d.clone()))
                        .collect(),
                );
                self.refuse(
                    Refused {
                        constraint: print::written(written, written_name).into(),
                        asked: Asked::Test { outcome },
                        cause: cause.into(),
                    },
                    kept,
                );
            }
            // The names bound by `let`s read through their summaries: the test narrows the
            // inputs they are computed from as well as the names. Only the inputs it narrows
            // are met, each `O(log k)` for a summary of `k` inputs read through the tree of its
            // terms' bounds ([`Scope::inputs_and_lets`], `Tx::invert_read`); the others keep
            // their integers, which meeting with their own would not change. A box with no
            // point empties every input, once, as the scope then becomes one no state reaches.
            let (over, lets, _) = self.inputs_and_lets(&free, true);
            let through = if lets.is_empty() {
                Domains::new()
            } else {
                let reads: Vec<_> = lets.values().filter_map(|l| l.read.clone()).collect();
                match let_narrowing(t, &over, lets, &Demand::Bool(outcome)) {
                    Some(narrowed) => narrowed,
                    None => {
                        let vars = reads.iter().flat_map(|r| r.vars().iter());
                        (over.keys().chain(vars))
                            .map(|n| (n.clone(), IntervalSet::empty()))
                            .collect()
                    }
                }
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

    /// Empties every name of a scope no state reaches, as a scope that is shown has them: once,
    /// when it is first shown, since nothing narrows or binds a name in it after
    /// ([`Scope::narrow`], [`Scope::bind`]) and its copies share the emptied names.
    fn empty_if_bottom(&mut self) {
        if self.bottom && !self.emptied.0 {
            self.names = self
                .names
                .keys()
                .map(|n| (n.clone(), Product::bottom()))
                .collect();
            self.emptied.0 = true;
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
            seeds.changed.insert(n.clone());
            out.extend(
                self.relation
                    .moved(n, self.lazy)
                    .filter_map(|g| blocks.of(g)),
            );
            // A satellite moved changes the stars at the hubs it relates to, whose conjuncts do
            // not mention it ([`Conjuncts::around`]); a lazy scope finds their leaves stale.
            if !self.lazy {
                out.extend(
                    self.relation
                        .around(n)
                        .iter()
                        .filter_map(|x| self.relation.star(x)),
                );
            }
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
        // A tree of difference constraints and bounds alone, with holes or a class or none, was
        // projected to a fixed point of its blocks, each exact, so the bounds of its names were
        // a fixed point of its edges; and a name changed since is a seed ([`Seeds::unsure`]).
        let old_blocks = old.blocks();
        seeds.unsure = seeds
            .names
            .iter()
            .filter(|n| {
                old_blocks
                    .tree_of_name(n)
                    .is_some_and(|t| old_blocks.gaps(t).is_none())
            })
            .cloned()
            .collect();
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
        // the edges added since the last projection: it is found again where it is read. Each
        // name with holes then keeps its tree from shortest paths until the potential is found
        // again with its gap ([`Scope::repair`], [`Scope::reseed`]); this reads every name, as
        // the projection reads every block.
        if matches!(due, Due::All) {
            self.potential = Potential::default();
            for (n, p) in &self.names {
                self.relation.gapped(n, gapped(p));
            }
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
            let parts: Vec<(PartKey, PartWith, Formula)> = trees
                .into_values()
                .flat_map(|tree| split(tree.into_iter(), None))
                .collect();
            for (key, with, g) in parts {
                let names = syms(&g);
                self.project_due(key, with, &g, &names);
            }
            return;
        }
        // A projection narrows the names and neither reads nor changes the relation, which is
        // taken out while the worklist reads its blocks and put back after; only whether each
        // name keeps its tree from shortest paths is recorded in it ([`Scope::sync_gap`]).
        let mut relation = std::mem::take(&mut self.relation);
        // Every block, as after a change of every name, is projected block by block.
        let every = matches!(due, Due::All);
        let (due, seeds): (Vec<BlockId>, Seeds) = match due {
            Due::All => (relation.blocks().all().collect(), Seeds::default()),
            Due::Blocks(bs, seeds) => (bs.into_iter().collect(), seeds),
        };
        // What changed in each tree of the forest, for those projected by shortest paths.
        let mut fresh: BTreeMap<BlockId, Seeds> = BTreeMap::new();
        // The trees projected block by block in this projection, each with a block of it when
        // its potential is to be found again ([`Scope::reseed`]).
        let mut fallen: BTreeMap<BlockId, Option<BlockId>> = BTreeMap::new();
        {
            let blocks = relation.blocks();
            for n in &seeds.names {
                if let Some(t) = blocks.tree_of_name(n) {
                    let at = fresh.entry(t).or_default();
                    at.names.insert(n.clone());
                    if seeds.changed.contains(n) {
                        at.changed.insert(n.clone());
                    }
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
            // Each edge added is put in the potential before any tree is projected, whichever
            // way its tree is, so that the potential holds at every edge it has
            // ([`Scope::repair`]); then the gap of each seed whose interval's gap has grown
            // past the one the potential holds with, as when a test leaves a hole in it
            // ([`Scope::raise`]). A raise that fails leaves its name past its gap, so its tree
            // is projected by the ends of its names, which do not read the gaps, whatever the
            // other raises do: the tree's raises stop there, and are made only if the ends
            // refuse the tree ([`Scope::by_holes`]). Otherwise `k` holes in one test on a cycle
            // of `k` names with no slack each lowered the potential round the cycle before
            // failing, Θ(k²).
            for (&t, at) in &fresh {
                if !at.added.is_empty() {
                    match self.repair(&relation, t, &at.added) {
                        Ok(None) => {}
                        Ok(Some(n)) => {
                            self.empty_at(&n);
                            self.relation = relation;
                            return;
                        }
                        Err(_) => {
                            fallen.insert(t, at.added.iter().find_map(|g| blocks.of(g)));
                            continue;
                        }
                    }
                }
                for n in &at.names {
                    if !self.raise(&relation, t, n) {
                        break;
                    }
                }
            }
        }
        // Whether each seed keeps its tree from shortest paths, now that the gaps are raised.
        for n in &seeds.names {
            self.sync_gap(&mut relation, n);
        }
        let blocks = relation.blocks();
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
        // The trees projected by the ends of their names, and those left to be projected
        // block by block, in this projection.
        let mut solved: BTreeSet<BlockId> = BTreeSet::new();
        let mut blockwise: BTreeSet<BlockId> = BTreeSet::new();
        // The trees whose ends were refused and whose gaps were then raised, to be projected by
        // shortest paths, with their names, whose record in the relation is brought up to date
        // after the worklist, which reads the relation ([`Scope::sync_gap`]).
        let mut paths: BTreeSet<BlockId> = BTreeSet::new();
        let mut raised: Vec<Arc<str>> = Vec::new();
        while let Some(b) = work.pop_front() {
            queued.remove(&b);
            let from = cause.remove(&b).unwrap_or_default();
            let t = blocks.tree(b);
            if whole_trees.contains(&t) {
                continue;
            }
            // A tree of difference constraints and bounds whose names have no class, and holes
            // only within the gaps the potential holds with ([`Potential`]), is projected by
            // shortest paths from what changed in it, once for all its blocks on the worklist,
            // and again for each move that reaches it from a star. A tree of them with holes
            // past those gaps, or one that shortest paths left, is projected by the ends of its
            // names ([`Scope::by_holes`]), once, and again for each move that reaches it from
            // another tree. Otherwise, or when neither can be done, block by block as below.
            //
            // Complexity tradeoff: a tree with a class in a name, or one whose ends the method
            // refuses (holes in three names or more of a part that its constraints join both
            // ways in more than one cycle, [`holes`]), is projected block by block, from the
            // blocks due, with the whole tree projected at an echo. Why: shortest paths over
            // the names' hulls are then not the projection (`x, z` in `[w, w + 1]`,
            // `x <= z <= x + 1`, `x != 5`, `z != 6` leave out `w = 5`), and no exact method in
            // O(N log N) is known for such parts; the holes of one name then leave holes in the
            // others. Trigger: tests that each leave a hole in another name of such a part,
            // with `if`s joined between them: the band `10 <= x_i - x_(i+1) <= 11`,
            // `x_i != 10 (k - i) + 5` and rungs `x_i - x_(i+2) >= 20` read 138 M, 4,115 M and
            // 110,524 M instructions at k = 5, 10 and 20, as on the code before ST-holes-moves.
            // The ends solve the whole tree at each projection that reaches it, in O(N log N)
            // for its `N` names, conjuncts and pieces, and tests that leave a hole in one more
            // name of a tree each, one at a time, also raise the potential of the names below
            // it ([`Scope::raise`]): `k` such tests on a tree of `k` names cost O(k² log k), as
            // the chain and the grid of `linked` measure, and so do `k` holes in one test on a
            // chain with slack enough that every raise holds. That cost is open, item O7 of the
            // cross-review xst, and not approved. COMPLEXITY.md row S25.
            let shortest =
                !every && !blocks.is_apart(b) && !fallen.contains_key(&t) && !holed.contains(&t);
            let ends = !blocks.is_apart(b)
                && !blockwise.contains(&t)
                && !paths.contains(&t)
                && blocks
                    .gaps(t)
                    .is_some_and(|k| k > 0 || fallen.contains_key(&t) || holed.contains(&t));
            let mut kept = false;
            if ends && !(solved.contains(&t) && from.is_empty()) {
                match self.by_holes(&relation, t, b, shortest) {
                    Ends::Done(Shortest::Moved(ns)) => {
                        solved.insert(t);
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
                        // The ends are exact, the values between them not always: the block's
                        // own projection still runs, as before this item, and may leave out
                        // more of them (CE-A's `a = 5`).
                        kept = true;
                    }
                    Ends::Done(Shortest::Bottom(n)) => {
                        self.empty_at(&n);
                        self.relation = relation;
                        return;
                    }
                    Ends::Paths(ns) => {
                        paths.insert(t);
                        raised.extend(ns);
                    }
                    Ends::Blockwise => {
                        blockwise.insert(t);
                    }
                }
            } else if ends {
                continue;
            }
            if !kept && shortest && (blocks.gaps(t) == Some(0) || paths.contains(&t)) {
                let mut at = fresh.remove(&t).unwrap_or_default();
                at.names.extend(from.iter().cloned());
                at.changed.extend(from.iter().cloned());
                if at.names.is_empty() && at.added.is_empty() {
                    continue;
                }
                let found = if !at.unsure.is_empty() {
                    Err(Fall::Unsure)
                } else {
                    self.shortest(&relation, t, &at)
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
        for n in &raised {
            self.sync_gap(&mut relation, n);
        }
        for (t, b) in fallen {
            if let Some(b) = b {
                self.reseed(&mut relation, t, b);
            }
        }
        self.relation = relation;
    }

    /// Projects tree `t` of the forest, a tree of difference constraints and bounds some of
    /// whose names have holes, `b` a block of it, by the ends of its names (item
    /// ST-holes-moves, [`holes`]): each name is met with its integers between its least and
    /// greatest values over the integer points of the tree's constraints within the names'
    /// integers. The ends are exact; the values between them are exact for a name on no cycle
    /// of constraints with a name with holes, and may have no point otherwise.
    ///
    /// When the method refuses the tree and `paths` is set, the gap of each of its names is
    /// raised to its holes ([`Scope::raise`]); when every raise holds, shortest paths project
    /// the tree exactly ([`Ends::Paths`]), as they did before the projection skipped the
    /// raises ([`Scope::project`]). Otherwise the refusal is recorded as a warning of its own
    /// ([`Cause::Holes`]), and the tree is projected block by block, as when a name has a
    /// class.
    ///
    /// In O(N log N) for the tree's names, conjuncts and the pieces of its names' integers, as
    /// [`holes`]: the conjuncts are found by a search from the block's names with a visited set.
    /// A refused tree's raises cost as [`Scope::raise`] states.
    fn by_holes(&mut self, relation: &Conjuncts, t: BlockId, b: BlockId, paths: bool) -> Ends {
        let blocks = relation.blocks();
        let mut seen: BTreeSet<Arc<str>> = BTreeSet::new();
        let mut work: Vec<Arc<str>> = Vec::new();
        for g in blocks.members(b) {
            for n in conjuncts::names(g) {
                if seen.insert(n.clone()) {
                    work.push(n);
                }
            }
        }
        let mut tree: BTreeSet<Arc<Formula>> = BTreeSet::new();
        while let Some(n) = work.pop() {
            for g in relation.mentioning(&n) {
                if !blocks
                    .of(g)
                    .is_some_and(|c| !blocks.is_apart(c) && blocks.tree(c) == t)
                    || !tree.insert(g.clone())
                {
                    continue;
                }
                for m in conjuncts::names(g) {
                    if seen.insert(m.clone()) {
                        work.push(m);
                    }
                }
            }
        }
        // The names in order, each name's bounds from the conjuncts that bound it alone, and
        // the edges between names, each with its conjunct.
        let names: Vec<Arc<str>> = seen.into_iter().collect();
        let at = |n: &Arc<str>| names.binary_search(n).ok();
        let mut lo: Vec<Option<Int>> = vec![None; names.len()];
        let mut hi: Vec<Option<Int>> = vec![None; names.len()];
        let mut edges: Vec<(usize, usize, Int)> = Vec::new();
        let mut of: Vec<&Arc<Formula>> = Vec::new();
        for g in &tree {
            let Some((e, back)) = conjuncts::edges(g) else {
                return Ends::Blockwise;
            };
            for e in std::iter::once(e).chain(back) {
                match (e.from.as_ref().and_then(at), e.to.as_ref().and_then(at)) {
                    (Some(u), Some(v)) => {
                        edges.push((u, v, e.weight));
                        of.push(g);
                    }
                    // `x_v <= w`.
                    (None, Some(v)) => {
                        if hi[v].as_ref().is_none_or(|h| e.weight < *h) {
                            hi[v] = Some(e.weight);
                        }
                    }
                    // `0 <= x_u + w`.
                    (Some(u), None) => {
                        let l = -&e.weight;
                        if lo[u].as_ref().is_none_or(|x| l > *x) {
                            lo[u] = Some(l);
                        }
                    }
                    (None, None) => return Ends::Blockwise,
                }
            }
        }
        let end = |x: &Option<Int>, inf: End| x.as_ref().map_or(inf, |x| End::Fin(Num::from(x)));
        let int = |e: &End| match e {
            End::Fin(v) => Some(Int::from(v)),
            _ => None,
        };
        let mut dom: Vec<holes::Pieces> = Vec::with_capacity(names.len());
        for (i, n) in names.iter().enumerate() {
            let bound = IntervalSet::range(end(&lo[i], End::NegInf), end(&hi[i], End::PosInf));
            let ints = match self.names.get(n) {
                Some(p) if classed(p) => return Ends::Blockwise,
                Some(p) => p.ints().meet(&bound),
                None => bound,
            };
            if ints.pieces().is_empty() {
                return Ends::Done(Shortest::Bottom(n.clone()));
            }
            dom.push(
                ints.pieces()
                    .iter()
                    .map(|(a, b)| (int(a), int(b)))
                    .collect(),
            );
        }
        let potential: Vec<Option<Int>> = names
            .iter()
            .map(|n| self.potential.at.get(n).map(|x| x.0.clone()))
            .collect();
        let graph = holes::Graph {
            dom,
            edges,
            potential,
        };
        match holes::solve(&graph) {
            holes::Outcome::Empty => Ends::Done(Shortest::Bottom(names[0].clone())),
            holes::Outcome::Refused { names: part, holed } => {
                // A raise that fails leaves its name past its gap, and the tree off shortest
                // paths whatever the others do, so the raises stop there.
                if paths && names.iter().all(|n| self.raise(relation, t, n)) {
                    return Ends::Paths(names);
                }
                // The constraints between the names of the part, as written.
                let inside: BTreeSet<usize> = part.iter().copied().collect();
                let gs: BTreeSet<&Arc<Formula>> = graph
                    .edges
                    .iter()
                    .zip(&of)
                    .filter(|((u, v, _), _)| inside.contains(u) && inside.contains(v))
                    .map(|(_, g)| *g)
                    .collect();
                let constraint = Formula::and(gs.into_iter().map(|g| (**g).clone()).collect())
                    .written(written_name)
                    .into();
                let mut holed: Vec<Arc<str>> = holed
                    .iter()
                    .map(|&i| written_name(&names[i]).into())
                    .collect();
                holed.sort_unstable();
                self.refuse(
                    Refused {
                        constraint,
                        asked: Asked::Projection,
                        cause: Cause::Holes {
                            holed,
                            names: part.len(),
                        },
                    },
                    Kept::default(),
                );
                Ends::Blockwise
            }
            holes::Outcome::Kept(sets) => {
                let mut moved = Vec::new();
                for (n, set) in names.iter().zip(sets) {
                    let Some(p) = self.names.get_mut(n) else {
                        continue;
                    };
                    let set = IntervalSet::from_pieces(
                        set.iter()
                            .map(|(a, b)| (end(a, End::NegInf), end(b, End::PosInf)))
                            .collect(),
                    );
                    let before = p.ints().clone();
                    let prem = p.premises();
                    p.meet_ints(set, &prem);
                    if *p.ints() != before {
                        moved.push(n.clone());
                    }
                }
                Ends::Done(Shortest::Moved(moved))
            }
        }
    }

    /// Projects tree `t` of the forest, a tree of difference constraints and bounds whose
    /// names have no class and holes only within the gaps the potential holds with
    /// ([`conjuncts::Blocks::differences_only`], [`Potential`]), after the names `seeds`
    /// changed, by shortest paths: `y <= x + k` is an edge `x → y` of weight `k`, a name's
    /// greatest value is its least distance from a bound, and its least the negated least
    /// distance to one (Shostak, "Deciding linear inequalities by computing loop residues",
    /// J. ACM 28, 1981), each moved off a hole to the nearest integer of the name inward. An
    /// empty interval is bottom; otherwise each name is met with the interval between its new
    /// ends, and keeps its holes.
    ///
    /// Why the ends are those of the projection: each constraint `y <= x + k` holds at the
    /// greatest values of `x` and `y` among those of any two points, so a greatest bound of
    /// each name taken to its own integers, the search's fixed point, is at or above every
    /// point, and is a point when no bound crosses the least (Jeavons and Cooper, "Tractable
    /// constraints on ordered domains", Artificial Intelligence 79, 1995); the same holds of
    /// the least bounds. Why no name takes other holes than its own: write `g_y` for the gap of
    /// `y` the potential holds with, at least the longest run of integers it leaves out between
    /// its ends `L_y` and `H_y`, and `d(y)` for the least weight of a path from `v` to `y`
    /// with each edge out of a name `x` other than `v` lowered by `g_x`. A cycle weighs at least
    /// the sum of its names' gaps ([`Potential`]), so `d` meets no negative cycle. For `a` an
    /// integer of `v` in `[L_v, H_v]`, take `v` to `a` and each other `y` to the greatest of
    /// its integers at or below `m_y = min(H_y, a + d(y))`, or to `L_y` when `m_y < L_y`: at
    /// least `m_y - g_y` in the first case, and `H_y` itself when `m_y = H_y`. An edge
    /// `x → y` of weight `k` holds there: at `y = L_y`, by `L_y <= L_x + k`; at `x = H_x`, by
    /// `H_y <= H_x + k`; otherwise `y <= a + d(y) <= a + d(x) + k - g_x`, and `x` is at least
    /// `a + d(x) - g_x`, or `a` at `x = v`, where `d(x)` is 0 and the edge is not lowered. So
    /// the projection onto `v` is its integers in `[L_v, H_v]`.
    ///
    /// The bounds were a fixed point of the tree's other conjuncts at the last projection, so
    /// only the conjuncts added and the names changed since can move one ([`Seeds::changed`]):
    /// each seed takes the least bound the edges of the conjuncts added give it, and a changed
    /// seed the least its edges in give it, since its own bound may have risen; then a Dijkstra
    /// search from the changed seeds and those lowered moves the names their paths reach, with
    /// the weights reduced by the scope's potential ([`Potential`]), which [`Scope::repair`]
    /// and [`Scope::raise`] have put the edges added and the gaps grown in. Any other edge, of
    /// a conjunct not added between names not changed, held at the fixed point and still
    /// holds, unless the search lowers its tail and so reads it. In O((s + a + m) log n) for
    /// the `s` seeds, the `a` conjuncts added, and the `m` edges at the changed seeds and at
    /// the names whose bound moves, of `n` names, and the pieces of each name moved; the tree's
    /// other names, and the other edges at a seed, are not read. A name of a conjunct added has
    /// only that conjunct's edges read, so a hub that each of `k` tests relates to a new name
    /// costs O(1) a test, not the O(k) edges it has (item NARROW-hub-seed-edges; before it,
    /// every edge at every seed was read, and the search started from every seed, `k^2` in
    /// all). `Err` says why the tree is to be projected block by block, and nothing has
    /// changed.
    fn shortest(
        &mut self,
        relation: &Conjuncts,
        t: BlockId,
        seeds: &Seeds,
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
        // Every name moved was read; the meet below keeps its holes.
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
    /// The weights and distances are the pairs of [`Potential`], with each edge's weight lowered
    /// by the gap of the name it enters: the search reaches `u` with a distance whose first
    /// part is zero when the edge closes a cycle of such weight 0, and then the edges of the
    /// cycle, the new one, the one by which `u` was reached and those of the search's path back
    /// to `v`, are tied and the edge is put in again, so that a cycle of weight 0 is never
    /// mistaken for a negative one. The two edges of an equality are tied before either is put
    /// in: otherwise each equality of a chain would tie its cycle by a search over the names
    /// tied before it, `O(k²)` for a chain of `k`. A cycle negative with the gaps but not
    /// without them is no bottom: no potential holds with those gaps, and the tree is found
    /// again from the solver ([`Scope::reseed`]).
    ///
    /// In O(m log n) for the `m` edges at the names whose potential falls, of `n` names, and
    /// once more for each cycle of weight 0 tied.
    fn repair(
        &mut self,
        relation: &Conjuncts,
        t: BlockId,
        added: &BTreeSet<Arc<Formula>>,
    ) -> Result<Option<Arc<str>>, Fall> {
        let blocks = relation.blocks();
        let mut pot = self.potential.at.clone();
        let mut tied = self.potential.tied.clone();
        let gap = &self.potential.gap;
        let lowered = |e: &Edge| match e.to.as_ref().and_then(|v| gap.get(v)) {
            Some(d) => &e.weight - d,
            None => e.weight.clone(),
        };
        // The edges added and not yet in the potential's graph.
        let mut pending: Vec<(Arc<Formula>, bool, Edge)> = Vec::new();
        for g in added {
            let Some((e, back)) = conjuncts::edges(g) else {
                continue;
            };
            if !blocks.of(g).is_some_and(|b| blocks.tree(b) == t) {
                continue;
            }
            // The two edges of an equality form a cycle of weight 0 of their own, so are tied
            // before they are put in: otherwise the first, not tied, lowers the second parts of
            // every name a cycle of weight 0 already joins to its end, and a chain of
            // equalities costs the square of its length.
            if let Some(b) = &back
                && e.from.is_some()
                && e.to.is_some()
                && (&lowered(&e) + &lowered(b)).is_zero()
            {
                tied.insert((g.clone(), false));
                tied.insert((g.clone(), true));
            }
            pending.push((g.clone(), false, e));
            if let Some(e) = back {
                pending.push((g.clone(), true, e));
            }
        }
        let found = put_in(relation, t, added, &pending, &mut pot, &mut tied, gap)?;
        if found.is_none() {
            self.potential.at = pot;
            self.potential.tied = tied;
        }
        Ok(found)
    }

    /// Raises the gap the potential holds with at name `x` of tree `t` of the forest to the
    /// gap of its interval ([`hole_gap`]), when that has grown, as after a test that leaves a
    /// hole in it: lowering the potential of `x` by the growth keeps every edge into `x` as it
    /// was, and lowers each edge out of `x` by the growth, which are then put in again as
    /// edges added are ([`Scope::repair`]). When that finds a cycle negative with the gaps,
    /// nothing changes, and `x` keeps its tree from shortest paths ([`Scope::sync_gap`]): the
    /// holes of `x` may then leave holes in the other names. A name the potential lacks takes
    /// the gap alone, with no edge to read. Whether `x` is now within its gap, or has a class
    /// or no product, which no raise changes.
    ///
    /// In O((r + their edges) log n) for the `r` names whose potential falls, which is every
    /// name below `x` on a chain with no slack in the potential: `k` raises that each hold on
    /// a chain of `k` names cost O(k² log k), open, item O7 of the cross-review xst
    /// (COMPLEXITY.md row S25). A projection stops raising a tree at the first raise that
    /// fails ([`Scope::project`]).
    fn raise(&mut self, relation: &Conjuncts, t: BlockId, x: &Arc<str>) -> bool {
        let Some(p) = self.names.get(x).filter(|p| !classed(p)) else {
            return true;
        };
        let g = hole_gap(p.ints());
        let was = self.potential.gap_of(x);
        if g <= was {
            return true;
        }
        let Some(px) = self.potential.at.get(x).cloned() else {
            self.potential.gap.insert(x.clone(), g);
            return true;
        };
        let mut pot = self.potential.at.clone();
        let mut tied = self.potential.tied.clone();
        let mut gap = self.potential.gap.clone();
        pot.insert(x.clone(), (&px.0 - &(&g - &was), px.1));
        gap.insert(x.clone(), g);
        let out: Vec<(Arc<Formula>, bool, Edge)> = tree_edges(relation, t, x)
            .into_iter()
            .filter(|(_, _, e)| e.from.as_ref() == Some(x) && e.to.is_some())
            .collect();
        if let Ok(None) = put_in(
            relation,
            t,
            &BTreeSet::new(),
            &out,
            &mut pot,
            &mut tied,
            &gap,
        ) {
            self.potential.at = pot;
            self.potential.tied = tied;
            self.potential.gap = gap;
            return true;
        }
        false
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
    /// product with no class ([`classed`]) whose holes are within the gap the potential holds
    /// with ([`Potential`]). In O(p) for its `p` pieces.
    fn ends(&self, n: &str) -> Result<(Option<Int>, Option<Int>), Fall> {
        let p = self.names.get(n).ok_or(Fall::Name)?;
        if classed(p) || hole_gap(p.ints()) > self.potential.gap_of(n) {
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
    /// the scope's potential; otherwise the least values negated, along the edges reversed.
    /// Each seed first takes the least bound the edges of the conjuncts added give it, and a
    /// changed seed the least its edges in give it ([`Seeds::changed`]), then a Dijkstra search
    /// from the changed seeds and those lowered lowers the names its paths reach, each bound
    /// taken to the nearest integer of the name at or inside it ([`snap_down`], [`snap_up`]), or kept where the name has none
    /// there, which is bottom. The names lowered, with their new bounds on this side.
    ///
    /// The bounds found do not depend on the potential: a name lowered is pushed again, and
    /// each name popped at its latest bound lowers along each of its edges, so the search
    /// stops at a fixed point of the edges at the names it lowers, and the others' bounds were
    /// one already. The potential bounds the cost: a bound moved to an integer of `x` falls by
    /// at most the gap `g_x` the potential holds with, so the key of a name is its bound less
    /// `q`, the potential up, and the potential plus the gap, negated, down; an edge `s → x`
    /// of weight `k` read is checked to have `q_s + k - q_x - g_x` of zero or more, which is
    /// its reduced weight in the potential on either side ([`Potential`]). Each key pushed is
    /// then at least the key popped, and each name is popped at its latest bound once.
    fn bound_pass(
        &self,
        relation: &Conjuncts,
        t: BlockId,
        seeds: &Seeds,
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
        let gap = |n: &Arc<str>| self.potential.gap_of(n);
        let q = |n: &Arc<str>| -> Result<Int, Fall> {
            let v = &self.potential.at.get(n).ok_or(Fall::Potential)?.0;
            Ok(if up { v.clone() } else { -&(v + &gap(n)) })
        };
        // A bound `by` on this side of `n` taken to the nearest integer of `n` inside it.
        let snap = |n: &Arc<str>, by: Int| -> Int {
            let Some(p) = self.names.get(n) else {
                return by;
            };
            if up {
                snap_down(p.ints(), &by).unwrap_or(by)
            } else {
                snap_up(p.ints(), &-&by).map_or(by, |m| -&m)
            }
        };
        // Each name's bound on this side, once read.
        let mut label: BTreeMap<Arc<str>, Option<Int>> = BTreeMap::new();
        let read = |label: &mut BTreeMap<Arc<str>, Option<Int>>, n: &Arc<str>| {
            if let Some(l) = label.get(n) {
                return Ok(l.clone());
            }
            let (lo, hi) = self.ends(n)?;
            let l = if up { hi } else { lo.map(|l| -&l) };
            label.insert(n.clone(), l.clone());
            Ok(l)
        };
        let mut moved: BTreeMap<Arc<str>, Int> = BTreeMap::new();
        let mut heap: BinaryHeap<Reverse<(Int, Arc<str>)>> = BinaryHeap::new();
        for s in &seeds.names {
            read(&mut label, s)?;
        }
        // The edges that can lower a seed: each edge into a changed seed, whose own bound may
        // have risen, as at a join, and each edge of a conjunct added. Every other edge into a
        // seed held at the bounds of its ends at the fixed point, and comes from a name
        // unchanged since, at whose bound it holds, or from a changed one, from which the search
        // below starts.
        let mut edges: Vec<Edge> = Vec::new();
        for s in &seeds.changed {
            edges.extend(
                tree_edges(relation, t, s)
                    .into_iter()
                    .map(|(_, _, e)| e)
                    .filter(|e| way(e).1.as_ref() == Some(s)),
            );
        }
        for g in &seeds.added {
            if let Some((e, back)) = conjuncts::edges(g) {
                edges.push(e);
                edges.extend(back);
            }
        }
        // The least bound the edges give each seed.
        let mut least: BTreeMap<Arc<str>, Int> = BTreeMap::new();
        for e in &edges {
            let (a, b) = way(e);
            let Some(s) = b.filter(|s| seeds.names.contains(s)) else {
                continue;
            };
            let by = match &a {
                None => Some(e.weight.clone()),
                Some(r) => read(&mut label, r)?.map(|lr| &lr + &e.weight),
            };
            if let Some(c) = by
                && least.get(&s).is_none_or(|x| c < *x)
            {
                least.insert(s, c);
            }
        }
        for (s, by) in least {
            if read(&mut label, &s)?.is_none_or(|was| by < was) {
                let at = snap(&s, by);
                moved.insert(s.clone(), at.clone());
                label.insert(s, Some(at));
            }
        }
        // The search starts from the seeds whose bounds may have moved since the fixed point:
        // those changed, and those lowered above. At any other seed, its edges out hold.
        for s in &seeds.names {
            if !(seeds.changed.contains(s) || moved.contains_key(s)) {
                continue;
            }
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
                if &(&(&qs + &e.weight) - &qx) - &gap(&x) < Int::ZERO {
                    return Err(Fall::Potential);
                }
                let by = &ls + &e.weight;
                if read(&mut label, &x)?.is_none_or(|c| by < c) {
                    let at = snap(&x, by);
                    moved.insert(x.clone(), at.clone());
                    heap.push(Reverse((&at - &qx, x.clone())));
                    label.insert(x, Some(at));
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
    fn reseed(&mut self, relation: &mut Conjuncts, t: BlockId, b: BlockId) {
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
        // Each name's gap, from its interval; a name with a class keeps the tree from shortest
        // paths whatever its gap.
        let gaps: BTreeMap<Arc<str>, Int> = names
            .iter()
            .filter_map(|n| {
                let p = self.names.get(n).filter(|p| !classed(p))?;
                let g = hole_gap(p.ints());
                g.is_positive().then(|| (n.clone(), g))
            })
            .collect();
        let gap_of = |n: &Arc<str>| gaps.get(n).cloned().unwrap_or(Int::ZERO);
        // The edges between names, each lowered by the gap of the name it enters: a point of
        // them is a potential with the names' gaps ([`Potential`]), and there is none when a
        // cycle weighs less than the sum of its names' gaps. Then the point is of the
        // difference constraints and bounds as they are, and the names with holes keep the
        // tree from shortest paths.
        let lowered: Vec<Formula> = cons
            .iter()
            .filter_map(|g| conjuncts::edges(g))
            .flat_map(|(e, back)| std::iter::once(e).chain(back))
            .filter_map(|e| {
                let (Some(u), Some(v)) = (&e.from, &e.to) else {
                    return None;
                };
                let from =
                    Lin::atom(Atom::Sym(u.clone())).plus(&Lin::constant(&e.weight - &gap_of(v)));
                Some(Formula::Con(Con::ge(
                    &from,
                    &Lin::atom(Atom::Sym(v.clone())),
                )))
            })
            .collect();
        let found = if gaps.is_empty() {
            None
        } else {
            presburger::satisfiable(&Formula::and(lowered))
                .ok()
                .flatten()
        };
        let (point, gaps) = match found {
            Some(point) => (Some(point), gaps),
            None => {
                // The potential is of the edges alone, so the point is of the difference
                // constraints and bounds alone, where the tree holds other conjuncts.
                let edges = cons.iter().filter(|g| conjuncts::edges(g).is_some());
                let all = Formula::and(edges.map(|g| Formula::clone(g)).collect());
                (
                    presburger::satisfiable(&all).ok().flatten(),
                    BTreeMap::new(),
                )
            }
        };
        let gap_of = |n: &Arc<str>| gaps.get(n).cloned().unwrap_or(Int::ZERO);
        if let Some(point) = point {
            let mut at: BTreeMap<Arc<str>, usize> = BTreeMap::new();
            let mut main: Vec<(Arc<str>, Int)> = Vec::new();
            for n in &names {
                if let Some(v) = point.get(&Atom::Sym(n.clone())) {
                    at.insert(n.clone(), main.len());
                    main.push((n.clone(), v.clone()));
                }
            }
            // The tight edges, of reduced weight 0 under the point: a cycle of weight 0 is one
            // of them, and lies in one of their strongly connected components, whose edges are
            // tied. The second parts are then each name's height in the graph of the others,
            // so that each tight edge not tied falls by one or more ([`Potential`]).
            let mut tight: Vec<(usize, usize, Arc<Formula>, bool)> = Vec::new();
            for g in &cons {
                let Some((e, back)) = conjuncts::edges(g) else {
                    continue;
                };
                for (e, b) in std::iter::once((e, false)).chain(back.map(|e| (e, true))) {
                    let (Some(u), Some(v)) = (&e.from, &e.to) else {
                        continue;
                    };
                    let (Some(&i), Some(&j)) = (at.get(u), at.get(v)) else {
                        continue;
                    };
                    if &(&(&main[i].1 + &e.weight) - &gap_of(v)) - &main[j].1 == Int::ZERO {
                        tight.push((i, j, g.clone(), b));
                    }
                }
            }
            let mut out: Vec<Vec<usize>> = vec![Vec::new(); main.len()];
            for (i, j, _, _) in &tight {
                out[*i].push(*j);
            }
            // Numbered with each component after those it reaches.
            let comp = zedc_solvers::utvpi::components(&out, |j| *j);
            tight.sort_unstable_by_key(|(i, _, _, _)| comp[*i]);
            let mut height: Vec<i64> = vec![0; main.len()];
            for (i, j, g, b) in tight {
                let (ci, cj) = (comp[i], comp[j]);
                if ci == cj {
                    self.potential.tied.insert((g, b));
                } else {
                    height[ci] = height[ci].max(height[cj] + 1);
                }
            }
            for (i, (n, v)) in main.into_iter().enumerate() {
                self.potential.at.insert(n, (v, height[comp[i]]));
            }
            for n in &names {
                match gaps.get(n) {
                    Some(g) => self.potential.gap.insert(n.clone(), g.clone()),
                    None => self.potential.gap.remove(n),
                };
            }
        }
        for n in &names {
            self.sync_gap(relation, n);
        }
    }

    /// Records in `relation` whether `n` keeps its tree from projection by shortest paths
    /// ([`Conjuncts::gapped`]): when it has a class, or holes past the gap the potential
    /// holds with at it ([`Potential`]). In O(p + log n) for its `p` pieces.
    fn sync_gap(&self, relation: &mut Conjuncts, n: &Arc<str>) {
        relation.gapped(n, self.off_paths(n));
    }

    /// Whether `n` has a class, or holes past the gap the potential holds with at it.
    fn off_paths(&self, n: &str) -> bool {
        self.names
            .get(n)
            .is_some_and(|p| classed(p) || hole_gap(p.ints()) > self.potential.gap_of(n))
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
        let names: Vec<Vec<Arc<str>>> = b.parts.iter().map(|(_, _, g)| syms(g)).collect();
        let mut work: std::collections::VecDeque<usize> = b
            .parts
            .iter()
            .zip(&names)
            .enumerate()
            .filter(|(_, ((key, with, _), ns))| !self.is_projected(key, with, ns))
            .map(|(i, _)| i)
            .collect();
        if work.is_empty() {
            return;
        }
        // A threshold-implication component is solved as a whole, exactly ([`threshold::solve`]).
        // Complexity tradeoff: the component is solved again from the start each time one of
        // its parts is due, so a block of N parts narrowed by N tests, one at a time, costs
        // O(N · N log N log W) and not O(N log N log W). Why: the solver keeps no state between
        // calls. Keeping it would not make such a walk near linear: each test is first split
        // into cases, and a case that fixes the shared name narrows every earlier name, Θ(i)
        // output per case (COMPLEXITY.md row S25, hard); measured at n = 320 the solve is 5% of
        // the time and the case split 88%. Trigger: a walk of N disjunctions on one shared
        // name, tested one at a time. Test:
        // `l01_39_reduced_product::xst::s4::a_walk_of_disjunctions_narrows_in_near_linear_time`
        // (ignored). COMPLEXITY.md row S4-ti.
        if let Some(shape) = &threshold::shape(&b.core)
            && self.project_threshold(shape)
        {
            for ((key, with, _), ns) in b.parts.iter().zip(&names) {
                let at = self.snapshot(ns);
                self.projected.insert(key.clone(), (with.clone(), at));
            }
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
            self.project_part(&b.parts[i].2);
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
                let all = Formula::and(b.parts.iter().map(|(_, _, g)| g.clone()).collect());
                self.project_part(&all);
                break;
            }
        }
        for ((key, with, _), ns) in b.parts.iter().zip(&names) {
            let at = self.snapshot(ns);
            self.projected.insert(key.clone(), (with.clone(), at));
        }
    }

    /// Meets each name of the threshold-implication component `shape` with its exact bounds,
    /// and the hub with its values that pass ([`threshold::solve`]); `false`, changing nothing,
    /// when the hub has three or more values and its coefficients have both signs (plan row
    /// S4-hub-mixed).
    fn project_threshold(&mut self, shape: &threshold::Shape) -> bool {
        let sys = shape.system(|n| self.get(n).ints().clone());
        match threshold::solve(&sys) {
            threshold::Answer::MixedHub => false,
            threshold::Answer::Empty => {
                match shape.names.first().or(shape.hub.as_ref()) {
                    Some(n) => self.empty_at(&n.clone()),
                    None => self.bottom = true,
                }
                true
            }
            threshold::Answer::Bounds { names, hub } => {
                let mut meet = |n: &Arc<str>, x: IntervalSet| {
                    if let Some(p) = self.names.get_mut(n) {
                        let prem = p.premises();
                        p.meet_ints(x, &prem);
                    }
                };
                for (n, (lo, hi)) in shape.names.iter().zip(names) {
                    meet(n, IntervalSet::range(lo, hi));
                }
                if let Some(w) = &shape.hub {
                    meet(w, hub);
                }
                true
            }
        }
    }

    /// Whether part `key`, which mentions `names`, was last projected with `with` and with
    /// their intervals and classes as they are now.
    fn is_projected(&self, key: &PartKey, with: &PartWith, names: &[Arc<str>]) -> bool {
        self.projected
            .get(key)
            .is_some_and(|(w, at)| w == with && *at == self.snapshot(names))
    }

    /// Projects `part`, which mentions `names`, when `key` is new, was last projected with
    /// other equalities or constraints than `with`, or one of their intervals or classes has
    /// changed since its last projection. A conjunct's part is not projected again when only
    /// inequalities on terms it does not compare have changed ([`PartWith`]).
    fn project_due(&mut self, key: PartKey, with: PartWith, part: &Formula, names: &[Arc<str>]) {
        if self.is_projected(&key, &with, names) {
            return;
        }
        self.project_part(part);
        let at = self.snapshot(names);
        self.projected.insert(key, (with, at));
    }

    /// Tells the relation whether each of `names` is bounded below and above, as its product
    /// is now: a leaf is a star's only while unbounded on the side away from a conjunct of
    /// two hubs or more ([`Conjuncts::star`]). And whether each keeps its tree from projection
    /// by shortest paths ([`Scope::sync_gap`]).
    fn sync_bounds<'a>(&mut self, names: impl IntoIterator<Item = &'a Arc<str>>) {
        for n in names {
            let (below, above) = sides(&self.names, n);
            self.relation.bound(n, below, above);
            let on = self.off_paths(n);
            self.relation.gapped(n, on);
        }
    }

    /// The interval and class of each of `names`.
    fn snapshot(&self, names: &[Arc<str>]) -> Projected {
        names
            .iter()
            .map(|n| {
                let p = self.get(n);
                (
                    n.clone(),
                    p.ints().clone(),
                    p.cell.congruence.element.clone(),
                )
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
            for (_, _, part) in split(core.iter().map(|g| &**g), None) {
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

    /// The projection of `part` onto each name it mentions, as `Scope::project_part` gives
    /// it, found by eliminating its pendants first; `None` where `part` is not of the form
    /// below, or the projection of what is left refuses a question, and today's projection of
    /// the whole part is to be asked.
    ///
    /// A pendant is a top-level constraint `s·x + σ·F + k == 0`, or `>= 0`, of names alone,
    /// where `x`, of coefficient `s` one or minus one, is mentioned by no other top-level
    /// conjunct of `part` and holds one interval with no class, and `F`, the form, is a linear
    /// term of two names or more with its first coefficient positive (`σ` one or minus one).
    /// The pendants of each form are replaced by one new name `w == F` with `w` in the values
    /// of the form at which each of them has a value of its `x` (`Pendant::allows`); the rest
    /// of `part`, with these, is projected as today, and each `x` takes the values its
    /// constraint gives from those of `w` (`Pendant::takes`). Eliminating `x` this way is
    /// exact: in each disjunct, `x` ranges over the image of the form's values under its
    /// constraint, so its hull is the image of the form's hull.
    ///
    /// The route is taken by structure alone: `part` has a pendant, every other top-level
    /// conjunct is a constraint, a negated constraint, or a disjunction of constraints and
    /// conjunctions of constraints, and the disjunctions, counting `!(t == 0)` and each name
    /// other than a pendant's `x` whose integers are more than one interval, number at most
    /// one, so that the projection is the hull in each disjunct, and the hull of the image is
    /// the image of the hull. With fewer names, the integer solver refuses fewer questions
    /// (Growth, Tie) than on the whole part; where it refuses none on either, the answers are
    /// the same.
    // Complexity tradeoff: a part with two disjunctions or more, or whose would-be pendants
    // have a coefficient other than one or minus one at `x`, or an `x` with holes or a class,
    // is projected whole, at O(k) names per question: for k such constraints added one at a
    // time to one part, O(k^3) in all. Eliminating `x` there is not exact by an image of
    // hulls: with two disjunctions the projection is not the hull in each disjunct, and a
    // coefficient other than one or minus one, or holes or a class at `x`, give an image of
    // the form with gaps, not an interval. A form of one name, `x - a >= k` and the like, a
    // difference constraint, is left to the whole projection too, which keeps the parts of
    // difference constraints on their present route; its elimination would be exact. Test
    // `l01_39_reduced_product::pendants`, COMPLEXITY.md S43. A complete solution would project
    // each combination of disjuncts with the pendants eliminated, exponential in the number
    // of disjunctions.
    pub fn project_by_pendants(&self, part: &Formula) -> Option<Vec<(Arc<str>, IntervalSet)>> {
        let tops = distinct_conjuncts(part);
        if tops.contains(&Formula::bottom()) {
            // A conjunct is `false` (`2t == 1`), so `part` has no point and each name is empty.
            return Some(
                conjuncts::names(part)
                    .into_iter()
                    .map(|n| (n, IntervalSet::empty()))
                    .collect(),
            );
        }
        let mut count: BTreeMap<Arc<str>, usize> = BTreeMap::new();
        for t in &tops {
            for n in conjuncts::names(t) {
                *count.entry(n).or_default() += 1;
            }
        }
        let mut hung: Vec<Pendant> = Vec::new();
        let mut rest: Vec<Formula> = Vec::new();
        for t in &tops {
            match self.pendant(t, |n| count.get(n).copied().unwrap_or(0)) {
                Some(p) => hung.push(p),
                None => rest.push(t.clone()),
            }
        }
        if hung.is_empty() {
            return None;
        }
        let xs: BTreeSet<&Arc<str>> = hung.iter().map(|p| &p.x).collect();
        let mut disjunctions = 0usize;
        for t in &rest {
            disjunctions += one_disjunction(t)?;
        }
        for n in count.keys().filter(|n| !xs.contains(n)) {
            let pieces = self.get(n).ints().pieces().len();
            if pieces == 0 {
                return None;
            }
            disjunctions += usize::from(pieces > 1);
        }
        if disjunctions > 1 {
            return None;
        }
        // Each form, with a new name for it and the values at which each of its pendants has
        // a value of its `x`. A name begins with `#` here, which no program writes.
        let mut forms: BTreeMap<Lin, (Atom, IntervalSet)> = BTreeMap::new();
        for p in &hung {
            let i = forms.len();
            let (_, d) = forms
                .entry(p.form.clone())
                .or_insert_with(|| (Atom::Sym(format!("#w{i}").into()), IntervalSet::top()));
            *d = d.meet(&p.allows(self.get(&p.x).ints()));
        }
        let mut left = rest;
        for (f, (w, d)) in &forms {
            left.push(Formula::Con(Con::eq(f, &Lin::atom(w.clone()))));
            left.push(presburger::member(w, d));
        }
        let (whole, syms) = self.framed(&Formula::and(left));
        let mut out: Vec<(Arc<str>, IntervalSet)> = Vec::new();
        if matches!(&whole, Formula::Or(v) if v.is_empty()) {
            // The pendants of a form allow no common value of it, or what is left has no
            // point: neither has `part`, and each of its names is empty. The conjunction is
            // `false` then, with no name left in it to project onto.
            for n in count.into_keys() {
                out.push((n, IntervalSet::empty()));
            }
            return Some(out);
        }
        let (each, skipped) = presburger::project_each(&whole, &syms).ok()?;
        if !skipped.is_empty() {
            return None;
        }
        let mut forms_at: BTreeMap<&Atom, IntervalSet> = BTreeMap::new();
        for (a, x) in syms.iter().zip(each) {
            let x = x.ok()?;
            match a {
                Atom::Sym(n) if n.starts_with('#') => {
                    forms_at.insert(a, x);
                }
                Atom::Sym(n) if count.contains_key(n) => out.push((n.clone(), x)),
                _ => {}
            }
        }
        for p in &hung {
            out.push((p.x.clone(), p.takes(&forms_at[&forms[&p.form].0])));
        }
        Some(out)
    }

    /// `t` as a pendant of a part whose names have the counts `count`: a constraint of names
    /// alone, one of which, `x`, of coefficient one or minus one, no other conjunct mentions,
    /// with two names or more besides, and `x` of one interval and no class.
    fn pendant(&self, t: &Formula, count: impl Fn(&str) -> usize) -> Option<Pendant> {
        let Formula::Con(c) = t else { return None };
        let mut x: Option<(&Arc<str>, &Int)> = None;
        for (a, k) in &c.lin.terms {
            let Atom::Sym(n) = a else { return None };
            if count(n) == 1 {
                if x.is_some() {
                    return None;
                }
                x = Some((n, k));
            }
        }
        let (x, k) = x?;
        let s: i8 = if *k == Int::ONE {
            1
        } else if *k == -&Int::ONE {
            -1
        } else {
            return None;
        };
        if c.lin.terms.len() < 3 || gapped(&self.get(x)) {
            return None;
        }
        let mut form: BTreeMap<Atom, Int> = c
            .lin
            .terms
            .iter()
            .filter(|(a, _)| !matches!(a, Atom::Sym(n) if n == x))
            .map(|(a, k)| (a.clone(), k.clone()))
            .collect();
        let sigma: i8 = if form.values().next().is_some_and(Int::is_negative) {
            for v in form.values_mut() {
                *v = -&*v;
            }
            -1
        } else {
            1
        };
        Some(Pendant {
            x: x.clone(),
            s,
            sigma,
            k: Num::from(&c.lin.constant),
            eq: c.rel == Rel::Eq,
            form: Lin {
                terms: form,
                constant: Int::ZERO,
            },
        })
    }

    /// Meets each name `part` mentions with its projection, within every interval; where the
    /// solver refuses the projection, with the bounds the box stage gives the rows of `part`
    /// ([`presburger::project_each_boxed`]).
    fn project_part(&mut self, part: &Formula) {
        if let Some(out) = self.project_by_pendants(part) {
            for (n, x) in out {
                if let Some(p) = self.names.get_mut(&n) {
                    let prem = p.premises();
                    p.meet_ints(x, &prem);
                }
            }
            return;
        }
        let (whole, syms) = self.framed(part);
        // The text of `part`, each name as written, printed once, and only when a question
        // about it is refused.
        let mut text: Option<Arc<str>> = None;
        let mut refuse = |s: &mut Scope, asked: Asked, cause: presburger::Refusal, kept: Kept| {
            let constraint = text
                .get_or_insert_with(|| part.written(written_name).into())
                .clone();
            let r = Refused {
                constraint,
                asked,
                cause: cause.into(),
            };
            s.refuse(r, kept);
        };
        // A refused projection keeps the bounds the box stage gives the rows (DESIGN step
        // L1.38), and is reported with them: each name of the scope that `part` mentions, or
        // for a projection onto one name refused alone, that name.
        let got = presburger::project_each_boxed(&whole, &syms);
        let boxed = |s: &Scope, only: Option<usize>| -> Kept {
            let each = syms.iter().zip(&got.each).enumerate();
            let sets = each.filter_map(|(i, (a, (x, _)))| match a {
                Atom::Sym(n) if only.is_none_or(|k| k == i) && s.names.contains_key(n) => {
                    Some((n.clone(), x.clone()))
                }
                _ => None,
            });
            Arc::new(sets.collect())
        };
        let mut refused = Vec::new();
        match &got.whole {
            Some(cause) => refused.push((Asked::Projection, cause.clone(), boxed(self, None))),
            None => {
                for cause in &got.skipped {
                    refused.push((Asked::Disjunct, cause.clone(), Kept::default()));
                }
                for (i, (a, (_, e))) in syms.iter().zip(&got.each).enumerate() {
                    if let (Some(cause), Atom::Sym(n)) = (e, a) {
                        let onto = Asked::Onto(written_name(n).into());
                        refused.push((onto, cause.clone(), boxed(self, Some(i))));
                    }
                }
            }
        }
        for (asked, cause, kept) in refused {
            refuse(self, asked, cause, kept);
        }
        for (a, (x, _)) in syms.iter().zip(got.each) {
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
        let due: BTreeSet<Address> = match last {
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
        let pending: Vec<(Term, Vec<Arc<str>>, Enumerated)> = due
            .into_iter()
            .filter_map(|k| {
                let free = self.written.get(&k)?;
                if !free.iter().all(|n| self.names.contains_key(n)) {
                    return None;
                }
                let statics = self.statics_of(free);
                let open: Vec<Arc<str>> = free
                    .iter()
                    .filter(|n| !statics.contains_key(*n))
                    .cloned()
                    .collect();
                let key = (k.clone(), statics.clone().into_iter().collect());
                (open.len() <= 1 && !self.enumerated.contains(&key))
                    .then(|| substitute(k.term(), &statics))
                    .filter(stage::ends)
                    .map(|c| (c, open, key))
            })
            .collect();
        if pending.is_empty() {
            return;
        }
        self.enumerate_on(pending);
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
        let mut due: BTreeSet<Address> = BTreeSet::new();
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
                        DiffItem::Remove(_, free) => {
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
        while let Some(k) = todo.pop_first() {
            let Some((c, open)) = self.taken(&k) else {
                // A constraint due that is no longer taken may have linked groups, as a
                // removed one did: the constraints on its names are due in its place.
                if due.remove(&k)
                    && let Some(free) = self.written.get(&k)
                {
                    for n in free {
                        todo.extend(self.written_by.of(n).filter(|j| **j != k).cloned());
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
                    todo.extend(self.written_by.of(n).filter(|j| **j != k).cloned());
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

    /// The written constraint of address `k` as [`Scope::enumerate_exactly`] takes it, with
    /// its static names substituted, and its open names; `None` when it is not taken: a free
    /// name not in scope, no open name, or an open name not a bounded integer.
    fn taken(&self, k: &Address) -> Option<(Term, BTreeSet<Arc<str>>)> {
        let free = self.written.get(k)?;
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
        (!open.is_empty() && open.iter().all(bounded_int))
            .then(|| (substitute(k.term(), &statics), open))
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
    /// taken constraints linked to it by shared open names, in the order of their addresses, and
    /// their open names. Each constraint and name is visited once.
    fn group(&self, open: impl IntoIterator<Item = Arc<str>>) -> (Term, BTreeSet<Arc<str>>) {
        let mut names: BTreeSet<Arc<str>> = open.into_iter().collect();
        let mut todo: Vec<Arc<str>> = names.iter().cloned().collect();
        let mut seen: BTreeSet<&Address> = BTreeSet::new();
        let mut taken: BTreeMap<&Address, Term> = BTreeMap::new();
        while let Some(n) = todo.pop() {
            for k in self.written_by.of(&n) {
                if !seen.insert(k) {
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

    /// The arms of `t` appended to `out`, as [`Run::walk`] finds them, and the value of `t`, as
    /// [`Run::forward`] finds it, in one pass, the scope as it was on return: each `let` in
    /// `t` is bound once, where walking `t` and then finding its value bound each twice (item
    /// PA-bind-cost). The arms, their order and their scopes are those of the walk, and the
    /// value that of the transfer: an `if` is assumed with the walk's premises for its arms
    /// and again without them for its value, since the two scopes differ in their premises.
    fn walk_value(&'m self, t: &'m Term) -> Deep<'m, Product> {
        match t {
            Term::Let(..) | Term::If(..) | Term::Prim(..) | Term::App(..) => {
                self.stack.call(move || self.walk_value_at(t))
            }
            _ => Stack::ready(self.scope(|s| leaf(t, s))),
        }
    }

    async fn walk_value_at(&'m self, t: &'m Term) -> Product {
        if self.scope(|s| s.bottom) {
            // The transfer finds nothing in a scope no state reaches; the walk still shows
            // the arms below, each unreachable.
            self.walk(t).await;
            return Product::bottom();
        }
        match t {
            Term::Let(x, e, b) => {
                let p = self.walk_value(e).await;
                // As in `Run::forward_at`: a comparison that follows its carrier is, at an
                // integer, the literal compared with the value just found.
                let plain = follow(t).filter(|_| p.ty.element.subtype(&Type::int()));
                let u = self.scope(|s| s.bind(x, p, e));
                let out = match plain {
                    Some(f) => {
                        self.walk(b).await;
                        if self.scope(|s| s.bottom) {
                            Product::bottom()
                        } else {
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
                    }
                    None => self.walk_value(b).await,
                };
                self.scope(|s| s.unbind(u));
                out
            }
            // A literal in each arm: the value is the literal of each arm some state reaches,
            // which the walk's scopes of the arms tell, so the test is not assumed again.
            Term::If(c, a, b) if matches!((&**a, &**b), (Term::Lit(_), Term::Lit(_))) => {
                let reached = self.walk_if(c, a, b).await;
                let value = |reached: bool, arm: &Term| match arm {
                    Term::Lit(v) if reached => Product::literal(v),
                    _ => Product::bottom(),
                };
                let mut p = value(reached[0], a);
                p.join(&value(reached[1], b));
                p
            }
            Term::If(..) => {
                self.walk_at(t).await;
                self.forward(t).await
            }
            Term::Prim(op, args) => {
                let mut xs = Vec::with_capacity(args.len());
                for a in args {
                    xs.push(self.walk_value(a).await);
                }
                forward_prim(*op, xs)
            }
            Term::App(f, args) => {
                self.walk(f).await;
                for a in args {
                    self.walk(a).await;
                }
                self.scope(|s| leaf(t, s))
            }
            _ => self.scope(|s| leaf(t, s)),
        }
    }

    /// The arms of `if c { a } else { b }` appended to `out`, each arm walked in its scope,
    /// the test's premise its position in the walk; whether some state reaches each arm, the
    /// true arm first.
    async fn walk_if(&'m self, c: &'m Term, a: &'m Term, b: &'m Term) -> [bool; 2] {
        let count = self.count.get();
        self.count.set(count + 1);
        let at = FactAddress {
            node: NodeAddress(Vector::unit(Position::root().child(count))),
            keypath: Vector::new(),
        };
        let prem = Premises::one(Premise::Constraint(at));
        let mut reached = [false; 2];
        for (i, (o, arm)) in [(true, a), (false, b)].into_iter().enumerate() {
            let s = self.scope(|s| s.assume(c, o, &prem));
            reached[i] = !s.bottom;
            self.out.borrow_mut().push(Arm {
                guard: c.to_string(),
                outcome: o,
                scope: s.clone(),
            });
            self.inner.borrow_mut().push(s);
            self.walk(arm).await;
            self.inner.borrow_mut().pop();
        }
        reached
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
                let p = self.walk_value(e).await;
                let u = self.scope(|s| s.bind(x, p, e));
                self.walk(b).await;
                self.scope(|s| s.unbind(u));
            }
            Term::If(c, a, b) => _ = self.walk_if(c, a, b).await,
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

/// Whether `p` has a class other than all integers, or than the one value its interval is.
fn classed(p: &Product) -> bool {
    match &p.cell.congruence.element {
        Congruence::Class { modulus, .. } if *modulus == Num::ONE => false,
        Congruence::Class { modulus, residue } if *modulus == Num::ZERO => {
            p.ints().bounds() != Some((&End::Fin(residue.clone()), &End::Fin(residue.clone())))
        }
        _ => true,
    }
}

/// The length of the longest run of integers `ints` leaves out between its ends, 0 for one
/// interval or none. In O(p) for its `p` pieces.
fn hole_gap(ints: &IntervalSet) -> Int {
    let mut most = Int::ZERO;
    for w in ints.pieces().windows(2) {
        if let (End::Fin(a), End::Fin(b)) = (&w[0].1, &w[1].0) {
            let run = &(&Int::from(b) - &Int::from(a)) - &Int::ONE;
            if run > most {
                most = run;
            }
        }
    }
    most
}

/// The greatest integer of `ints` at or below `z`, if any, in O(log p) for its `p` pieces.
fn snap_down(ints: &IntervalSet, z: &Int) -> Option<Int> {
    let v = End::Fin(Num::from(z));
    let pieces = ints.pieces();
    let (_, hi) = pieces.get(pieces.partition_point(|(lo, _)| *lo <= v).checked_sub(1)?)?;
    Some(match hi {
        End::Fin(h) if *hi < v => Int::from(h),
        _ => z.clone(),
    })
}

/// The least integer of `ints` at or above `z`, if any, in O(log p) for its `p` pieces.
fn snap_up(ints: &IntervalSet, z: &Int) -> Option<Int> {
    let v = End::Fin(Num::from(z));
    let pieces = ints.pieces();
    let (lo, _) = pieces.get(pieces.partition_point(|(_, hi)| *hi < v))?;
    Some(match lo {
        End::Fin(l) if *lo > v => Int::from(l),
        _ => z.clone(),
    })
}

/// Whether the integers of `p` are other than one interval with no class. Such a name keeps a
/// tree of difference constraints from projection by shortest paths
/// ([`conjuncts::Blocks::differences_only`]) when the potential holds with no gap at it, as
/// after a projection of every block, which empties the potential; otherwise its holes count
/// only past that gap ([`Scope::off_paths`]). A class of modulus 0, a single value, counts only
/// where the interval is that value.
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

/// A pendant of a part ([`Scope::project_by_pendants`]): `s·x + σ·w + k == 0`, or `>= 0`, for `w`
/// its form, a linear term of the other names with its first coefficient positive.
struct Pendant {
    x: Arc<str>,
    s: i8,
    sigma: i8,
    k: Num,
    eq: bool,
    form: Lin,
}

/// `e + v`.
fn shift(e: &End, v: &Num) -> End {
    match e {
        End::Fin(a) => End::Fin(a + v),
        e => e.clone(),
    }
}

/// `{a·v + b : v in set}` for `a` one or minus one.
fn affine(set: &IntervalSet, a: i8, b: &Num) -> IntervalSet {
    set.lift1(|(lo, hi)| {
        if a > 0 {
            vec![(shift(lo, b), shift(hi, b))]
        } else {
            vec![(shift(&-hi, b), shift(&-lo, b))]
        }
    })
}

impl Pendant {
    /// The values of the form at which some value of `x` in `ints`, one interval, holds.
    fn allows(&self, ints: &IntervalSet) -> IntervalSet {
        let Some((lo, hi)) = ints.bounds() else {
            return IntervalSet::empty();
        };
        if self.eq {
            // σ·w == -k - s·x.
            return affine(
                ints,
                -self.sigma * self.s,
                &-&(&Num::from(self.sigma as i64) * &self.k),
            );
        }
        // σ·w >= -k - s·x for some x: σ·w >= -k - max(s·x).
        let most = if self.s > 0 { hi.clone() } else { -lo };
        let bound = shift(&-&most, &-&self.k);
        if self.sigma > 0 {
            IntervalSet::range(bound, End::PosInf)
        } else {
            IntervalSet::range(End::NegInf, -&bound)
        }
    }

    /// The values of `x` at which some value of the form in `f` holds.
    fn takes(&self, f: &IntervalSet) -> IntervalSet {
        if self.eq {
            // x == -s·σ·w - s·k.
            return affine(
                f,
                -self.s * self.sigma,
                &-&(&Num::from(self.s as i64) * &self.k),
            );
        }
        let Some((lo, hi)) = f.bounds() else {
            return IntervalSet::empty();
        };
        // s·x >= -k - σ·w for some w: s·x >= -k - max(σ·w).
        let most = if self.sigma > 0 { hi.clone() } else { -lo };
        let bound = shift(&-&most, &-&self.k);
        if self.s > 0 {
            IntervalSet::range(bound, End::PosInf)
        } else {
            IntervalSet::range(End::NegInf, -&bound)
        }
    }
}

/// The number of disjunctions `t`, a conjunct of a part, adds to its projection, when known
/// to be at most one: a constraint none, a disjunction of constraints and conjunctions of
/// constraints one, `!(t == 0)` one.
fn one_disjunction(t: &Formula) -> Option<usize> {
    let con = |f: &Formula| match f {
        Formula::Con(_) => true,
        Formula::Not(n) => matches!(&**n, Formula::Con(c) if c.rel == Rel::Ge),
        _ => false,
    };
    match t {
        f if con(f) => Some(0),
        Formula::Not(n) if matches!(&**n, Formula::Con(_)) => Some(1),
        Formula::Or(gs)
            if gs.iter().all(|g| match g {
                Formula::And(hs) => hs.iter().all(con),
                g => con(g),
            }) =>
        {
            Some(1)
        }
        _ => None,
    }
}

/// The top-level conjuncts of `part`, each once and in an order of their own: each constraint
/// divided by the greatest common divisor of its coefficients ([`Con::reduced`], so `2t == 0`
/// is `t == 0`, `2t == 1` is `false` and `2t + 1 >= 0` is `t >= 0`); an equation and its
/// negation, `t == 0` and `-t == 0`, are one, written with the lesser of `t` and `-t`, and so
/// inside a negation; `t >= 0` and `-t >= 0` together are `t == 0`; and a conjunct held
/// twice is held once. So the conjuncts, which names are pendants and which disjunctions are
/// counted ([`Scope::project_by_pendants`]) do not depend on how an equal set of them is
/// written (items PROJECT-each-canon and PROJECT-canon-gcd). In time O(n log n) for n
/// conjuncts.
fn distinct_conjuncts(part: &Formula) -> BTreeSet<Formula> {
    let unsigned = |c: &Con| {
        let neg = c.lin.times(-1);
        Formula::Con(Con {
            lin: if neg < c.lin { neg } else { c.lin.clone() },
            rel: Rel::Eq,
        })
    };
    // The constraint reduced, an equation unsigned.
    let row = |c: &Con| match c.reduced() {
        Some(r) => match &r {
            Formula::Con(e) if e.rel == Rel::Eq => unsigned(e),
            _ => r,
        },
        None if c.rel == Rel::Eq => unsigned(c),
        None => Formula::Con(c.clone()),
    };
    let mut tops: BTreeSet<Formula> = BTreeSet::new();
    let mut stack = vec![part];
    while let Some(f) = stack.pop() {
        match f {
            Formula::And(gs) => stack.extend(gs.iter()),
            Formula::Con(c) => match row(c) {
                // `2t == 1` is `false`, and so is the whole conjunction, however written.
                r @ Formula::Or(_) => return BTreeSet::from([r]),
                r => {
                    tops.insert(r);
                }
            },
            Formula::Not(n) if matches!(&**n, Formula::Con(c) if c.rel == Rel::Eq) => {
                let Formula::Con(c) = &**n else {
                    unreachable!("an equation")
                };
                // `!(2t == 1)` is `!false`, which holds everywhere and is no conjunct.
                if let r @ Formula::Con(_) = row(c) {
                    tops.insert(Formula::Not(presburger::Shared::new(r)));
                }
            }
            f => {
                tops.insert(f.clone());
            }
        }
    }
    // Each `t >= 0` whose `-t >= 0` is held too, as `t == 0`.
    let mut out = BTreeSet::new();
    for f in &tops {
        if let Formula::Con(c) = f
            && c.rel == Rel::Ge
        {
            let neg = Formula::Con(Con {
                lin: c.lin.times(-1),
                rel: Rel::Ge,
            });
            if tops.contains(&neg) {
                out.insert(unsigned(c));
                continue;
            }
        }
        out.insert(f.clone());
    }
    out
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
