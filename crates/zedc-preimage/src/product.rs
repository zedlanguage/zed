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
use std::sync::{Arc, Mutex, MutexGuard, OnceLock, PoisonError, Weak};

use num_bigint::BigInt;
use zed_kernel::frames::{Deep, Stack};
use zed_kernel::poly::roots::{Roots, term_roots};
use zed_kernel::print;
use zed_kernel::provenance::{FactAddress, NodeAddress, Position, Vector};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Prim, Shared, Term, Value, World};

use super::address::Address;
use super::holes;
use super::images;
use super::loops;
use super::preimage::{
    Classes, Demand, Domains, LetIn, LetPa, Lets, Listed, Shift, TermBounds, follow_own,
    let_narrowing, let_summary, preimage_listed, relations, witness,
};
use super::spans::Spans;
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
use zedc_presburger::presburger::{self, Atom, Con, Factor, Formula, Lin, Rel};
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
///
/// Complexity tradeoff: naive version, the domains held by value, so an insertion into a
/// scope's map copies O(log n) chunks of up to 16 products each, every product deep:
/// O(s log n) for products of size s, about 70 KB a binding. Used: products behind an `Arc`,
/// so the copied path shares them, O(log n) pointer copies a binding (COMPLEXITY.md row
/// PA-bind-cost: a block of 4,000 bindings 1,201M to 733M instructions). Tradeoffs: one more
/// indirection on each read, and a change to a product another holds copies it once
/// (`Arc::make_mut`).
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

    /// Whether no value has this element once its domains are reduced
    /// ([`Product::reduce_domains`]): its type is empty, or holds integers alone while its
    /// interval or its class holds none, which the reduction carries into the type.
    fn empties(&self) -> bool {
        self.is_empty()
            || ((self.ints().is_empty() || self.cell.congruence.element == Congruence::Bottom)
                && self.ty.element.subtype(&Type::int()))
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

    /// The product with each entry's premises without those of `drop` ([`Premises::without`]),
    /// sharing its domains when no entry rests on one of them.
    fn without(&self, drop: &[Premises]) -> Product {
        let d = &**self;
        let ps = [
            &d.cell.ints.premises,
            &d.cell.congruence.premises,
            &d.cell.finite.premises,
            &d.cell.float.premises,
            &d.cell.length.premises,
            &d.ty.premises,
            &d.time.premises,
        ];
        let kept = ps.map(|p| p.without(drop));
        if ps.iter().zip(&kept).all(|(a, b)| a.same(b)) {
            return self.clone();
        }
        let [ints, congruence, finite, float, length, ty, time] = kept;
        let mut p = self.clone();
        let q = &mut *p;
        q.cell.ints.premises = ints;
        q.cell.congruence.premises = congruence;
        q.cell.finite.premises = finite;
        q.cell.float.premises = float;
        q.cell.length.premises = length;
        q.ty.premises = ty;
        q.time.premises = time;
        p
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

type Products = imbl::OrdMap<Arc<str>, Product>;

/// Products with a persistent affine-path representation and an exact ordinary-map view.
#[derive(Clone, Debug, Default)]
pub struct NameProducts {
    base: Products,
    paths: imbl::OrdMap<Arc<str>, (Arc<str>, Int)>,
    ranges: imbl::OrdMap<Arc<str>, PathRange>,
    relation: Option<RelationMark>,
    view: Option<Arc<OnceLock<Products>>>,
    blocker: Option<Arc<Formula>>,
    /// A difference test `b >= a + gap` that moved no end when it came, between two names on
    /// different paths, kept as (a, b, gap) until a later test moves an end of `a` or `b`
    /// or puts them on one path (`NameProducts::pending_holds`).
    pending: Option<(Arc<str>, Arc<str>, Int)>,
    /// The pendant leaves ([`PendantRow`]), each with its row: a leaf's product is its base
    /// product met with what its row allows at its hub's upper end.
    pendants: imbl::OrdMap<Arc<str>, PendantRow>,
}

/// The row `(hub - leaf >= gap && leaf >= start) || leaf <= low`, with `low < start`, of a
/// leaf no other conjunct mentions ([`Scope::extend_pendant`]). With `H` the hub's upper end,
/// the leaf's values the row allows are `(-inf, low]` and `[start, H - gap]`: a value at most
/// `low` holds with every value of the hub, and one in `[start, H - gap]` with `H`. The leaf
/// keeps a value at most `low` (checked when the row is admitted, and its base product is not
/// written after), so every value of the hub keeps a witness and the row narrows no hub.
#[derive(Clone, PartialEq, Debug)]
struct PendantRow {
    hub: Arc<str>,
    low: Int,
    start: Int,
    gap: Int,
}

impl PendantRow {
    /// The upper end `H - gap` of the leaf's values in the row's first case, for the hub's
    /// upper end `H` (`inf` when it has none), when that case has values: it is at least
    /// `start`.
    fn cap(&self, hub: &IntervalSet) -> Option<End> {
        let cap = match hub.bounds()? {
            (_, End::Fin(h)) => End::Fin(Num::from(&(&Int::from(h) - &self.gap))),
            (_, e) => e.clone(),
        };
        (cap >= End::Fin(Num::from(&self.start))).then_some(cap)
    }

    /// The leaf's values the row allows where the hub's integers are `hub`: `(-inf, low]`,
    /// and `[start, H - gap]` when it is not empty ([`PendantRow::cap`]).
    fn allowed(&self, hub: &IntervalSet) -> IntervalSet {
        let low = (End::NegInf, End::Fin(Num::from(&self.low)));
        match self.cap(hub) {
            Some(cap) => {
                IntervalSet::from_pieces(vec![low, (End::Fin(Num::from(&self.start)), cap)])
            }
            None => IntervalSet::from_pieces(vec![low]),
        }
    }
}

/// A directed path of names: the interval they share in the root's coordinates, its head and
/// tail, its size, and the head's own upper end and the tail's own lower end when a bound
/// moved them alone (`NameProducts::bound`), in the same coordinates.
#[derive(Clone, PartialEq, Debug)]
struct PathRange {
    lo: End,
    hi: End,
    head: Arc<str>,
    tail: Arc<str>,
    size: usize,
    head_hi: Option<End>,
    tail_lo: Option<End>,
    /// A test from a member back to an earlier one closed a cycle (`NameProducts::link`).
    /// Every point with all members at one value of the shared interval satisfies it, so
    /// the members keep the shifted interval; an own end of the head or the tail would pass
    /// through the cycle to the other members, so a closed path takes none.
    closed: bool,
}

impl PathRange {
    /// The interval of the member `n`, in the root's coordinates.
    fn of(&self, n: &str) -> (End, End) {
        let mut lo = self.lo.clone();
        let mut hi = self.hi.clone();
        if *self.tail == *n
            && let Some(c) = &self.tail_lo
        {
            lo = lo.max(c.clone());
        }
        if *self.head == *n
            && let Some(c) = &self.head_hi
        {
            hi = hi.min(c.clone());
        }
        (lo, hi)
    }

    /// The range in coordinates `k` above these.
    fn shifted(self, k: &Int) -> PathRange {
        PathRange {
            lo: offset_end(&self.lo, k),
            hi: offset_end(&self.hi, k),
            head_hi: self.head_hi.map(|e| offset_end(&e, k)),
            tail_lo: self.tail_lo.map(|e| offset_end(&e, k)),
            ..self
        }
    }
}

fn offset_end(e: &End, k: &Int) -> End {
    match e {
        End::Fin(n) => End::Fin(Num::from(&(&Int::from(n) + k))),
        e => e.clone(),
    }
}

impl NameProducts {
    // Complexity tradeoff: naive version, each difference test `b >= a + gap` on a chain is
    // propagated by the solver to every name on it, Theta(n) products written per test and
    // Theta(n^2) over a chain of n tests (on main the s4 chain, cycles and raise allocate 23
    // to 26 times the bytes at 8n). Used: names joined by such tests into one directed path
    // keep one interval in the coordinates of the path's root, and each name keeps its offset
    // to its parent, so a name's bounds are the root's interval shifted by the sum of offsets
    // to the root. This is the weighted union-find (a union-find whose links carry an offset, the
    // "potential" of the name) with union by size: Galler and Fischer, "An improved
    // equivalence algorithm", Communications of the ACM 7(5), 1964; Tarjan, "Efficiency of a
    // good but not linear set union algorithm", Journal of the ACM 22(2), 1975. There is no
    // path compression, since it writes on a read and these maps are persistent and shared
    // between scope versions; union by size alone keeps every parent path O(log n) long. A
    // link of a path's tail to another's head, or a bound on a path's head or tail, edits
    // O(1) entries of persistent maps, O(log n); reading one name, O(log² n); the whole exact
    // map (`Deref`), O(n log² n), built once per version and shared by its clones. A test
    // is admitted only when the dominance check of `link` shows every member keeps the
    // shifted root interval exactly; any other test, or any write through `DerefMut`,
    // materializes the map and runs the solver as before, so no answer changes. The plan's
    // method (the solver on every test) is kept for those. Tradeoffs: a reader that takes
    // the whole map after every test pays O(n log² n) each time (`Scope::get` and
    // [`NameProducts::read`] do not); the checker's scopes (lazy, names bound to
    // themselves, premises on every test) are not admitted yet. Measured, instructions at
    // 8n over n with the deferred [`Relation`]: s4 chain raise 8.3, cycles 7.8 (Forward),
    // open chain 8.4 (Forward); bytes 8.0 to 8.9, against 23.0 to 26.1 on main.
    /// The product of `name`, built alone when it is on a path and the exact map is not built:
    /// O(log² n), where reading it through the map would build the whole map.
    pub fn read(&self, name: &str) -> Option<std::borrow::Cow<'_, Product>> {
        use std::borrow::Cow;
        if !self.paths.contains_key(name) && !self.pendants.contains_key(name) {
            return self.base.get(name).map(Cow::Borrowed);
        }
        if let Some(view) = self.view.as_ref().and_then(|v| v.get()) {
            return view.get(name).map(Cow::Borrowed);
        }
        self.product(name).map(Cow::Owned)
    }

    /// Membership reads need no product materialization.
    pub fn contains_key(&self, name: &str) -> bool {
        self.base.contains_key(name)
    }

    /// The number of names, `O(1)`: every path member is in the base map.
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Whether there are no names.
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// The names, in order, without their products.
    pub fn keys(&self) -> impl Iterator<Item = &Arc<str>> {
        self.base.keys()
    }

    /// Names whose product may differ between `since` and `self`, each once or more, among
    /// all names: those whose base entries differ, and, when the two have different paths or
    /// ranges, each of `vars` on a path in either. Any name not listed has the same product in
    /// both. Lazy, so a reader that stops after a few pays for those.
    // Complexity tradeoff: naive version, the diff of the two exact maps (`Deref`), which
    // builds each version's map, O(n log² n) for a scope of n names, once per scope version
    // (WALK-read-image-n2). Used: the diff of the base maps, which skips the parts the two
    // share, and the members of `vars` on a path, O(k log n) for k of them when the paths
    // moved. The plan's method was to take the changes from the entries of the paths a test
    // writes; those entries name the roots that moved, but a root's members are not listed
    // (a union-find keeps parents only), and every member of a moved root changes, so the
    // inputs are checked instead: a list of members per root would cost O(n log n) on every
    // link of two large paths, and a reader still resets each input whose root moved.
    pub fn changed<'a>(
        &'a self,
        since: &'a NameProducts,
        vars: &'a imbl::OrdSet<Arc<str>>,
    ) -> impl Iterator<Item = &'a Arc<str>> + 'a {
        let moved = self.moved_since(since);
        let on_paths = (vars.iter()).filter(move |v| {
            moved
                && (self.paths.contains_key(*v)
                    || since.paths.contains_key(*v)
                    || self.pendants.contains_key(*v)
                    || since.pendants.contains_key(*v))
        });
        crate::images::changed(&since.base, &self.base).chain(on_paths)
    }

    /// Whether a name's product may differ between `since` and `self` other than through its
    /// base entry: the paths, their ranges or the pendant rows differ. A pendant leaf follows
    /// its hub, which is on a path. O(1).
    fn moved_since(&self, since: &NameProducts) -> bool {
        !(self.paths.ptr_eq(&since.paths)
            && self.ranges.ptr_eq(&since.ranges)
            && self.pendants.ptr_eq(&since.pendants))
    }

    /// Whether some product is not its base entry: a name on a path or a pendant leaf.
    fn implicit(&self) -> bool {
        !self.paths.is_empty() || !self.pendants.is_empty()
    }

    fn root(&self, name: &str) -> Option<(Arc<str>, Int, &PathRange)> {
        let (mut n, _) = self.paths.get_key_value(name)?;
        let mut off = Int::from(0);
        loop {
            if let Some(r) = self.ranges.get(n) {
                return Some((n.clone(), off, r));
            }
            let (parent, k) = self.paths.get(n)?;
            off = &off + k;
            n = parent;
        }
    }

    fn product(&self, name: &str) -> Option<Product> {
        let mut p = self.base.get(name)?.clone();
        if let Some((_, off, r)) = self.root(name) {
            let (lo, hi) = r.of(name);
            p.meet_ints(
                IntervalSet::range(offset_end(&lo, &off), offset_end(&hi, &off)),
                &Premises::new(),
            );
            while p.reduce_domains() {}
        } else if let Some(row) = self.pendants.get(name) {
            let hub = self.product(&row.hub)?;
            p.meet_ints(row.allowed(hub.ints()), &Premises::new());
            while p.reduce_domains() {}
        }
        Some(p)
    }

    fn view(&self) -> &Products {
        if !self.implicit() {
            return &self.base;
        }
        self.view
            .as_ref()
            .expect("implicit bounds have an exact-map cache")
            .get_or_init(|| {
                let mut out = self.base.clone();
                for n in self.paths.keys().chain(self.pendants.keys()) {
                    let p = self.product(n).expect("a path member is in the base map");
                    if self.base.get(n) != Some(&p) {
                        out.insert(n.clone(), p);
                    }
                }
                out
            })
    }

    fn materialize(&mut self) {
        if self.implicit() {
            self.base = self.view().clone();
            self.paths.clear();
            self.ranges.clear();
            self.pendants.clear();
            self.relation = None;
            self.view = None;
            self.pending = None;
        }
    }

    /// Puts `x` in the map with product `p`, or takes it out (`None`). When `x` is on no path
    /// the paths are kept: the exact map of the new version is the old one's with that one
    /// entry, so a built map is updated in O(log n), and one not built is left to be built
    /// when read. A path member is first materialized with every path.
    // Complexity tradeoff: naive version, the write goes through `DerefMut`, which materializes
    // every path, O(n log² n), and drops them, so the next difference test runs the solver:
    // the checker binds each name a test reads just before the test (walk.rs `Ck::with_bound`),
    // and no test was admitted after the first. Used: one entry of the base map, and of the
    // built map when there is one, O(log n) (item ST-walk-checker-admit).
    fn set_fresh(&mut self, x: &Arc<str>, p: Option<Product>) {
        if self.paths.contains_key(x) || self.pendants.contains_key(x) {
            self.materialize();
        }
        if let Some(view) = &mut self.view {
            let built = view.get().map(|v| match &p {
                Some(p) => v.update(x.clone(), p.clone()),
                None => v.without(x),
            });
            *view = Arc::new(built.map_or_else(OnceLock::new, OnceLock::from));
        }
        match p {
            Some(p) => _ = self.base.insert(x.clone(), p),
            None => _ = self.base.remove(x),
        }
    }

    /// The exact map when it costs nothing to read: the base map when no name is on a path,
    /// or the map of this version when it was built.
    fn built(&self) -> Option<&Products> {
        if !self.implicit() {
            return Some(&self.base);
        }
        self.view.as_ref().and_then(|v| v.get())
    }

    /// Whether `relation` is the one the last admission onto the paths left: each of its
    /// conjuncts since the first link was admitted ([`Scope::extend_path`]). O(1).
    fn on_paths(&self, relation: &Relation) -> bool {
        self.relation.as_ref().is_some_and(|m| relation.at(m))
    }

    fn member(&mut self, n: &Arc<str>) -> Option<()> {
        if self.paths.contains_key(n) {
            return Some(());
        }
        // A pendant leaf's base entry is not its product, and a path would take it as one.
        if self.pendants.contains_key(n) {
            return None;
        }
        let p = self.base.get(n)?;
        if p.ty.element != Type::int()
            || classed(p)
            || listed(p).is_some()
            || p.cell.ints.element != Bounds::ints(p.ints().clone())
        {
            return None;
        }
        let (lo, hi) = p.ints().only()?;
        if lo >= hi {
            return None;
        }
        self.paths.insert(n.clone(), (n.clone(), Int::from(0)));
        self.ranges.insert(
            n.clone(),
            PathRange {
                lo: lo.clone(),
                hi: hi.clone(),
                head: n.clone(),
                tail: n.clone(),
                size: 1,
                head_hi: None,
                tail_lo: None,
                closed: false,
            },
        );
        Some(())
    }

    /// Links the tail of one directed path to the head of another by b >= a + gap, the test
    /// holding under `prem`.
    fn link(&mut self, a: &Arc<str>, b: &Arc<str>, gap: &Int, prem: &Premises) -> Option<bool> {
        self.member(a)?;
        self.member(b)?;
        let (ra, oa, left) = self.root(a)?;
        let left = left.clone();
        let (rb, ob, right) = self.root(b)?;
        let right = right.clone();
        let shift = &(&oa + gap) - &ob;
        // An own end of `a` or `b` would pass to the names the link puts after `a` or before
        // `b`, which their shared interval cannot hold.
        if left.tail_lo.is_some() || right.head_hi.is_some() {
            return None;
        }
        if ra == rb {
            return self.close(a, b, &shift);
        }
        if a != &left.tail || b != &right.head {
            return self.hold(a, b, gap);
        }
        let rlo = offset_end(&right.lo, &-&shift);
        let rhi = offset_end(&right.hi, &-&shift);
        if left.lo < rlo || left.hi < rhi {
            return self.hold(a, b, gap);
        }
        // A link that changes no bound needs no implicit product state.
        if left.lo == rlo && left.hi == rhi {
            return self.hold(a, b, gap);
        }
        // The test's own meet in `Scope::narrow` moves b's lower end when left.lo > rlo and
        // a's upper end when left.hi > rhi, and only a meet that moves an end adds the test's
        // premises (zedc-lattice `Entry::meet`); the names the reduction then moves keep their
        // own premises (`Scope::reduce` meets each with `p.premises()`). So only a and b rest
        // on `prem`.
        if left.lo > rlo {
            self.rest_on(b, prem);
        }
        if left.hi > rhi {
            self.rest_on(a, prem);
        }
        let lo = left.lo;
        let hi = rhi;
        if lo >= hi {
            return None;
        }
        let range = PathRange {
            lo,
            hi,
            head: left.head,
            tail: right.tail,
            size: left.size + right.size,
            head_hi: left.head_hi,
            tail_lo: right.tail_lo.map(|e| offset_end(&e, &-&shift)),
            closed: left.closed || right.closed,
        };
        if left.size >= right.size {
            self.ranges.remove(&rb);
            self.paths.insert(rb, (ra.clone(), shift));
            self.ranges.insert(ra, range);
        } else {
            let range = range.shifted(&shift);
            self.ranges.remove(&ra);
            self.paths.insert(ra, (rb.clone(), -&shift));
            self.ranges.insert(rb, range);
        }
        self.view = Some(Arc::new(OnceLock::new()));
        Some(false)
    }

    /// Closes the path of `a` and `b` by `b >= a + gap`, `shift` being `gap` less what the path
    /// already proves of `b - a`: admitted only as a back edge from the tail to the head with
    /// no own end, and then empty when `shift` is positive (a cycle of positive weight) and
    /// otherwise redundant, since every point with all members at one value of the shared
    /// interval satisfies it. The path is marked closed, so that it takes no own end.
    fn close(&mut self, a: &Arc<str>, b: &Arc<str>, shift: &Int) -> Option<bool> {
        let (root, _, r) = self.root(a)?;
        if a != &r.tail || b != &r.head || r.head_hi.is_some() || r.tail_lo.is_some() {
            return None;
        }
        let r = PathRange {
            closed: true,
            ..r.clone()
        };
        self.ranges.insert(root, r);
        Some(shift.is_positive())
    }

    /// Keeps `b >= a + gap` aside, between names on two paths, when it moves no end of either
    /// (`NameProducts::slack`) and no other test is kept aside: the scope's products are then
    /// still the exact projections (see `pending`).
    // Complexity tradeoff (ST-walk-orders): naive version, such a test ran the solver, and its
    // conjunct, between two names on no path, blocked every later test from the paths: the
    // s4 cycles assumed in reverse order start with the closing test, and every later test
    // ran the solver, Theta(n) each and Theta(n²) in all (measured 35 to 65 at 8n over n).
    // Used: the test is kept aside, O(log² n), and checked after each later test the paths
    // admit, O(log² n): while a and b are on two paths the test is their one link, so the
    // pair of paths with it forms a tree of difference constraints, in which a bound
    // propagates only along the test, and a test that moves no end of a or b moves nothing
    // (on difference constraints as shortest paths: Bellman, "On a routing problem",
    // Quarterly of Applied Mathematics 16(1), 1958; Shostak, "Deciding linear inequalities
    // by computing loop residues", JACM 28(4), 1981). When a later test puts a and b on one
    // path, the test is admitted only as the back edge of `close`. Any other case
    // materializes and runs the solver as before. Tradeoff: one test aside at a time; with
    // two, a cycle can pass through both, which the one-hop check does not see.
    fn hold(&mut self, a: &Arc<str>, b: &Arc<str>, gap: &Int) -> Option<bool> {
        if self.pending.is_some() || !self.slack(a, b, gap)? {
            return None;
        }
        self.pending = Some((a.clone(), b.clone(), gap.clone()));
        // `link` may have put a and b on paths of their own; their products are unchanged.
        if self.view.is_none() {
            self.view = Some(Arc::new(OnceLock::new()));
        }
        Some(false)
    }

    /// Whether `b >= a + gap` moves no end of `a` or `b`, these being on two paths: `a`'s
    /// lower end plus `gap` is at most `b`'s, and so is its upper end. `None` on one path.
    fn slack(&self, a: &Arc<str>, b: &Arc<str>, gap: &Int) -> Option<bool> {
        let ends = |n: &Arc<str>| {
            let (root, off, r) = self.root(n)?;
            let (lo, hi) = r.of(n);
            Some((root, offset_end(&lo, &off), offset_end(&hi, &off)))
        };
        let ((ra, alo, ahi), (rb, blo, bhi)) = (ends(a)?, ends(b)?);
        if ra == rb {
            return None;
        }
        Some(offset_end(&alo, gap) <= blo && offset_end(&ahi, gap) <= bhi)
    }

    /// After a test the paths admitted, whether the test kept aside (`hold`) still moves no
    /// end, or now closes a path (`close`): `Some(bottom)`, or `None` when it would move an
    /// end, and the scope must then run the solver.
    fn pending_holds(&mut self) -> Option<bool> {
        let Some((a, b, gap)) = self.pending.clone() else {
            return Some(false);
        };
        if let Some(slack) = self.slack(&a, &b, &gap) {
            return slack.then_some(false);
        }
        let (_, oa, _) = self.root(&a)?;
        let (_, ob, _) = self.root(&b)?;
        let bottom = self.close(&a, &b, &(&(&oa + &gap) - &ob))?;
        self.pending = None;
        Some(bottom)
    }

    /// Bounds `n` below (`lower`) or above by `value`, the test holding under `prem`: on the
    /// path's shared interval when the bound passes to every member (a lower bound on the
    /// head, an upper bound on the tail), or as the head's own upper end or the tail's own
    /// lower end, which pass to no other member, since no member lies before the head or after
    /// the tail. A bound on a member between them is refused, and so is one that leaves the
    /// shared interval a single value.
    // Complexity tradeoff (item ST-walk-checker-admit): naive version, own ends refused. The
    // checker reads `b` of `a || b` under `!a`, and `!(x0 >= k)` on the head of a chain
    // `x0 <= x1 <= ...` was refused, so each such row materialized every path, O(n log² n),
    // and ran the solver, Theta(n): Theta(n²) over n rows (s4 raise, 2.6e9 instructions at
    // n = 128 on main, 9.0e9 with the paths and no own ends). Used: the head's own upper end
    // and the tail's own lower end, a field of the path's range, O(log n). Tradeoff: a path
    // with an own end is not linked further (`NameProducts::link`), since the link would
    // pass the end on to the names it adds.
    fn bound(&mut self, n: &Arc<str>, lower: bool, value: &Int, prem: &Premises) -> Option<bool> {
        self.member(n)?;
        let (root, off, r) = self.root(n)?;
        let mut r = r.clone();
        let end = End::Fin(Num::from(&(value - &off)));
        let (lo, hi) = r.of(n);
        let moved = if lower { end > lo } else { end < hi };
        if n == if lower { &r.head } else { &r.tail } {
            if lower {
                r.lo = r.lo.max(end);
            } else {
                r.hi = r.hi.min(end);
            }
            if r.lo == r.hi {
                return None;
            }
        } else if r.closed {
            return None;
        } else if lower && n == &r.tail {
            r.tail_lo = Some(lo.max(end));
        } else if !lower && n == &r.head {
            r.head_hi = Some(hi.min(end));
        } else {
            return None;
        }
        if moved {
            self.rest_on(n, prem);
        }
        let empty = |(lo, hi): (End, End)| lo > hi;
        let bottom = r.lo > r.hi || empty(r.of(&r.head)) || empty(r.of(&r.tail));
        self.ranges.insert(root, r);
        self.view = Some(Arc::new(OnceLock::new()));
        Some(bottom)
    }

    /// Adds `prem` to the premises of `n`'s integers, an end of which a test has just moved:
    /// O(1) for the premises (`Premises::extend`) and one persistent map edit, O(log n).
    fn rest_on(&mut self, n: &Arc<str>, prem: &Premises) {
        if !prem.is_empty()
            && let Some(p) = self.base.get_mut(n)
        {
            p.cell.ints.premises.extend(prem);
            self.view = Some(Arc::new(OnceLock::new()));
        }
    }
}

impl std::ops::Deref for NameProducts {
    type Target = Products;
    fn deref(&self) -> &Products {
        self.view()
    }
}

impl std::ops::DerefMut for NameProducts {
    fn deref_mut(&mut self) -> &mut Products {
        self.materialize();
        &mut self.base
    }
}

impl PartialEq for NameProducts {
    fn eq(&self, other: &Self) -> bool {
        self.view() == other.view()
    }
}

impl From<Products> for NameProducts {
    fn from(base: Products) -> Self {
        Self {
            base,
            ..Self::default()
        }
    }
}

impl FromIterator<(Arc<str>, Product)> for NameProducts {
    fn from_iter<I: IntoIterator<Item = (Arc<str>, Product)>>(it: I) -> Self {
        Self::from(it.into_iter().collect::<Products>())
    }
}

impl<'a> IntoIterator for &'a NameProducts {
    type Item = (&'a Arc<str>, &'a Product);
    type IntoIter = <&'a Products as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.view().into_iter()
    }
}

/// The relation of a scope: a conjunction, and the conjuncts of tests that
/// `Scope::extend_path` and `Scope::extend_threshold` admitted since, held apart until the
/// conjunction is read.
// Complexity tradeoff: naive version, each admitted test is added to the conjunction at once,
// which updates its persistent indexes (the set, the tightest constraint per term, the users of
// each name, the blocks): O(log n) a test, and about 90 of 100 allocator calls of an admitted
// test on a chain at n = 8 and 140 of 155 at n = 512 (allocator calls, measured in the
// cross-review of item ST-walk-implicit), which set the ratio at 8n. Used: an
// admitted conjunct is pushed on a persistent list, O(1) and one allocation; the first read adds
// the list to the conjunction it started from, oldest first, with the same `and` calls, so every
// read sees the same conjunction (O(k log n) once for k pending conjuncts). The built
// conjunction is cached in a cell that clones share, so one version is built once however many
// copies read it. The list is the persistent stack of Okasaki, "Purely Functional Data
// Structures", Cambridge University Press, 1998, ch. 2. Tradeoffs: the cost moves to the first
// reader (the solver on a refused test, `join`, `PartialEq`, the dump); a scope that is read
// after every test pays O(k log n) per read, as main did per test. Measured, instructions at
// 8n over n: s4 chain raise 10.3 without the list and 8.3 with it; cycle of weight 1
// (Forward) 10.5 and 7.8; open chain (Forward) 11.5 and 8.4.
#[derive(Clone, Debug, Default)]
pub struct Relation {
    base: Conjuncts,
    pending: Option<Arc<Pending>>,
    built: Arc<OnceLock<Conjuncts>>,
}

/// The admitted conjuncts not yet in the conjunction, latest first.
#[derive(Debug)]
struct Pending {
    f: Formula,
    rest: Option<Arc<Pending>>,
}

// Dropped as a loop: the default drop of an `Arc<Pending>` drops the next in turn, one stack
// frame each, and a list of about 65,000 overflowed a 2 MiB stack (TEST-bench-move-l0139).
// Each node held only here is taken apart with `Arc::into_inner`, which gives it back only to
// the last holder, so a list shared with another relation stops at the first shared node.
// O(k) for k nodes, as the recursion was, with O(1) stack.
impl Drop for Pending {
    fn drop(&mut self) {
        let mut next = self.rest.take();
        while let Some(p) = next {
            next = Arc::into_inner(p).and_then(|mut p| p.rest.take());
        }
    }
}

/// A relation's conjunction and pending list, by identity: the relation is the same while
/// nothing was added or written in place since.
type RelationMark = (imbl::OrdSet<Arc<Formula>>, Option<Arc<Pending>>);

impl Relation {
    /// Holds `f` apart, to be added at the next read.
    fn defer(&mut self, f: Formula) {
        let rest = self.pending.take();
        self.pending = Some(Arc::new(Pending { f, rest }));
        self.built = Arc::default();
    }

    fn mark(&self) -> RelationMark {
        (self.base.set().clone(), self.pending.clone())
    }

    /// Whether this is the relation `m` marked.
    fn at(&self, m: &RelationMark) -> bool {
        self.base.set().ptr_eq(&m.0)
            && match (&self.pending, &m.1) {
                (None, None) => true,
                (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                _ => false,
            }
    }

    /// States the sides on which `name` is bounded and whether it keeps its tree from shortest
    /// paths ([`Conjuncts::bound`], [`Conjuncts::gapped`]), for a name no conjunct mentions, as
    /// a fresh binding's: to the conjunction and, when built, to the built one, leaving the
    /// pending conjuncts pending. Those records are read when a conjunct of `name` comes, and
    /// none of the pending ones mentions it, so adding them later gives the conjunction the
    /// fold would.
    // Complexity tradeoff (item ST-walk-checker-admit): naive version, the write through
    // `DerefMut`, which folds the pending conjuncts in, O(k log n) for k of them; the checker
    // binds a name before each test, so a chain of n admitted tests with a binding at each
    // folded Θ(n²) conjuncts (the s4 chain with `w_i = y + x_i`: 15 folds of 15 down to 1
    // conjuncts at n = 16). Used: the records set in the conjunction and in the built one,
    // O(log n) each.
    fn state_fresh(&mut self, name: &Arc<str>, below: bool, above: bool, gapped: bool) {
        let state = |c: &mut Conjuncts| {
            c.bound(name, below, above);
            c.gapped(name, gapped);
        };
        state(&mut self.base);
        if self.pending.is_some() {
            self.built = Arc::new(match self.built.get() {
                Some(c) => {
                    let mut c = c.clone();
                    state(&mut c);
                    OnceLock::from(c)
                }
                None => OnceLock::new(),
            });
        }
    }

    fn build(&self) -> Conjuncts {
        let mut fs = Vec::new();
        let mut at = self.pending.as_deref();
        while let Some(p) = at {
            fs.push(&p.f);
            at = p.rest.as_deref();
        }
        let mut c = self.base.clone();
        for f in fs.into_iter().rev() {
            c.and(f.clone());
        }
        c
    }
}

impl std::ops::Deref for Relation {
    type Target = Conjuncts;
    fn deref(&self) -> &Conjuncts {
        match self.pending {
            None => &self.base,
            Some(_) => self.built.get_or_init(|| self.build()),
        }
    }
}

impl std::ops::DerefMut for Relation {
    fn deref_mut(&mut self) -> &mut Conjuncts {
        if self.pending.is_some() {
            self.base = std::ops::Deref::deref(self).clone();
            self.pending = None;
            self.built = Arc::default();
        }
        &mut self.base
    }
}

impl PartialEq for Relation {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl From<Conjuncts> for Relation {
    fn from(base: Conjuncts) -> Self {
        Self {
            base,
            ..Self::default()
        }
    }
}

impl std::fmt::Display for Relation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (**self).fmt(f)
    }
}

/// A small affine expression, without substitution or solver state.
fn path_lin(t: &Term) -> Option<Lin> {
    match t {
        Term::Var(n) => Some(Lin::atom(Atom::Sym(n.clone()))),
        Term::Lit(Value::Int(n)) => Some(Lin::constant(*n)),
        Term::Prim(p, args) if args.len() == 2 => {
            let literal = |t: &Term| matches!(t, Term::Lit(Value::Int(_)));
            let offset = literal(&args[0]) || literal(&args[1]);
            let difference = *p == Prim::Sub && args.iter().all(|t| matches!(t, Term::Var(_)));
            if !offset && !difference {
                return None;
            }
            let a = path_lin(&args[0])?;
            let b = path_lin(&args[1])?;
            match p {
                Prim::Add => Some(a.plus(&b)),
                Prim::Sub => Some(a.minus(&b)),
                _ => None,
            }
        }
        _ => None,
    }
}

fn path_con(t: &Term, outcome: bool) -> Option<Con> {
    let Term::Prim(p, args) = t else {
        return None;
    };
    if args.len() != 2 || !matches!(p, Prim::Ge | Prim::Le) {
        return None;
    }
    let a = path_lin(&args[0])?;
    let b = path_lin(&args[1])?;
    let mut lin = if *p == Prim::Ge {
        a.minus(&b)
    } else {
        b.minus(&a)
    };
    if !outcome {
        lin = lin.times(-1).minus(&Lin::constant(1));
    }
    Some(Con { lin, rel: Rel::Ge })
}

/// The names in scope with their products, the linear relation among them, and the written
/// constraints that hold. Each part is held in persistent maps, so that a case of a nest
/// copies the scope in O(1), and the join of two cases and the reduction of a scope cost the
/// parts that differ, found by the maps' difference, and not the whole scope.
#[derive(Clone, PartialEq, Debug)]
pub struct Scope {
    /// Exact products. Plain scopes use a persistent map; admitted difference paths keep
    /// translated bounds, with an exact map view on dereference. `get` reads one product.
    /// Mutation materializes first, so ordinary map readers and writers remain exact.
    pub names: NameProducts,
    /// The relation the integer names meet, with no auxiliary variable.
    pub relation: Relation,
    /// The written constraints that hold, a test and its negations by content address (each
    /// held as its canonical term, [`Address::term`]), each with its free names.
    pub written: imbl::OrdMap<Address, Vec<Arc<str>>>,
    /// The addresses of the written constraints on each name.
    written_by: Uses<Address>,
    /// The tests narrowed by joining two cases or more, kept so that a later test that leaves
    /// no value in one of their cases narrows by them again ([`Scope::narrow_kept_again`]):
    /// those the relation does not hold, and those it holds that have a case fixing a name.
    kept: KeptTests,
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
    /// `…::narrowing_by_many_refused_tests_scales`, `…::keeping_many_refusals_scales`,
    /// `…::the_join_of_arms_with_many_refused_tests_and_its_warnings_scale`. COMPLEXITY.md rows
    /// S18 (the solver) and S28 (this report). A complete solution would decide every question
    /// (see `presburger`).
    pub refusals: imbl::OrdMap<Refused, Kept>,
    /// Each question of [`Scope::refusals`] under each name of the scope its constraint
    /// mentions, by the name's binding: its name in the scope, which is `x@k` for a binder
    /// elaboration renamed, so an inner `x` that shadows an outer `x` has its own entry. Kept
    /// with it by [`Scope::refuse`] and the join: so the questions behind a read of m names are
    /// found in O(m log k) among k questions, and not by reading each question
    /// ([`Scope::refused_on`]).
    refused_by: imbl::OrdMap<Arc<str>, imbl::OrdSet<Refused>>,
    /// Each name a `let` of the walk bound, with the order of its binding and, for a function,
    /// its lambda: a test that calls a function is closed over it before its preimage is taken
    /// ([`Scope::close`]). Shared between the scopes of a walk's arms, not copied.
    bindings: imbl::OrdMap<Arc<str>, Binding>,
    /// The order of each name's binding ([`Orders`]).
    orders: Orders,
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
    /// Whether this scope is a case of a test being narrowed ([`Scope::cases`]), which is
    /// joined with the other cases and never shown: a constraint of the case that joins a
    /// group of linked constraints makes no part due ([`Block::outer`]).
    in_case: bool,
    /// The entries of [`Block::bounds`] the two-name rule of [`Block::reframe`] has projected
    /// for on this path of tests: each is projected for once.
    spent: imbl::OrdSet<BoundsKey>,
    /// The ends a test of one name gave each name, the upper one `true`, each the tightest
    /// such a test gave on this path: every state of the scope holds them, and the relation
    /// need not, since a test of one name narrows only the name's product. [`Scope::stated`]
    /// states them where its relation alone would lose them; an end the scope derived from
    /// the relation is not among them, since the relation gives it again.
    direct: imbl::OrdMap<(Arc<str>, bool), Num>,
    gaps: LowerGaps,
    /// The names whose members an obligation's equation listed as its integer roots
    /// ([`Scope::zero_reached`]): a written constraint that gives neither `true` nor `false`
    /// at such a member is kept in `root_failures`.
    rooted: imbl::OrdSet<Arc<str>>,
    /// Each root of an obligation's equation at which a written constraint gave neither
    /// `true` nor `false` (DESIGN.md sec:constraints, QUESTIONS A81).
    pub root_failures: imbl::OrdSet<RootFailure>,
}

/// The tests of a scope whose cases were joined ([`Scope::join_kept`]), by their content
/// addresses, with the names each reads and the triggers each is kept under, by name. The
/// join keeps only what the cases share: after `(x % 2 == 1 && y >= 0) || y <= -5`, which
/// has no relation, `x` is any integer and `y` in `-20..=-5` or `0..=20`, so `x % 2 == 0`
/// alone does not say that the first case is gone. A trigger does. A test the relation
/// holds is kept for the points of its cases alone ([`Watch::Points`]).
#[derive(Clone, PartialEq, Debug, Default)]
struct KeptTests {
    tests: imbl::OrdMap<Address, KeptTest>,
    by: Uses<Address>,
    triggers: imbl::OrdMap<Arc<str>, Triggers>,
    /// The tests with a case that fixes the name, by name ([`KeptTest::points`]).
    fixed: Uses<Address>,
}

/// A test of [`KeptTests`], giving `true`: the names it reads, the premises it was assumed
/// under, and its triggers, each with the name it reads.
#[derive(Clone, PartialEq, Debug)]
struct KeptTest {
    test: Term,
    free: Vec<Arc<str>>,
    premises: Premises,
    triggers: Vec<(Arc<str>, Trigger)>,
    /// For each case, the names it fixes to one value and the join does not, with their
    /// values: a written constraint on those names may give `false` there
    /// ([`Scope::written_dead`]), as it would in the case had it come first.
    points: Vec<Vec<(Arc<str>, Value)>>,
}

/// What a kept test is watched by ([`Scope::join_kept`]).
#[derive(Clone, Copy, PartialEq, Debug)]
enum Watch {
    /// The triggers and the points of its cases: a test the linear relation does not hold,
    /// so nothing else finds a case that a later test leaves with no value.
    Cases,
    /// The points of its cases alone: a test the linear relation holds, whose cases' ends,
    /// classes and holes the relation's projection reads, but not a written constraint at a
    /// point a case fixes, which lies outside the relation (`x * y == x` after `(x == 3 && y
    /// == 0) || x <= -5`).
    Points,
}

/// When a case of a kept test holds no value, by the product of one name: the case's own
/// product of the name, narrower than the join's, meets the name's product in no value.
#[derive(Clone, PartialEq, Debug)]
enum Trigger {
    /// The name's least value is above this, the case's greatest.
    Above(Num),
    /// The name's greatest value is below this, the case's least.
    Below(Num),
    /// The name's class and this one, `residue mod modulus`, share no value.
    Class(Num, Num),
    /// The name has no member from the first to the second, the case's least and greatest,
    /// both inside the join's ends: a hole the name's ends do not show.
    Inside(Num, Num),
}

/// The triggers on one name, each with the addresses of the tests kept under it: those of the
/// ends in the order of their values, so that a move of an end finds the triggers it passes
/// as a range, and the spans of `Inside` in a tree that finds those inside a hole.
#[derive(Clone, PartialEq, Debug, Default)]
struct Triggers {
    above: imbl::OrdMap<Num, imbl::OrdSet<Address>>,
    below: imbl::OrdMap<Num, imbl::OrdSet<Address>>,
    classes: imbl::OrdMap<(Num, Num), imbl::OrdSet<Address>>,
    inside: Spans,
}

impl Triggers {
    fn is_empty(&self) -> bool {
        self.above.is_empty()
            && self.below.is_empty()
            && self.classes.is_empty()
            && self.inside.is_empty()
    }
}

/// Adds `k` to the set of `key` in `m`.
fn add_to<K: Ord + Clone>(m: &mut imbl::OrdMap<K, imbl::OrdSet<Address>>, key: &K, k: &Address) {
    m.entry(key.clone()).or_default().insert(k.clone());
}

/// Takes `k` from the set of `key` in `m`, and the set from `m` when it is left empty.
fn take_from<K: Ord + Clone>(m: &mut imbl::OrdMap<K, imbl::OrdSet<Address>>, key: &K, k: &Address) {
    if let Some(s) = m.get_mut(key) {
        s.remove(k);
        if s.is_empty() {
            m.remove(key);
        }
    }
}

impl KeptTests {
    /// Keeps `t`, in place of a test of the same address.
    fn keep(&mut self, t: KeptTest) {
        let k = Address::of(&t.test);
        self.forget(&k);
        for n in &t.free {
            self.by.add(n, &k);
        }
        for (n, _) in t.points.iter().flatten() {
            self.fixed.add(n, &k);
        }
        for (n, g) in &t.triggers {
            let e = self.triggers.entry(n.clone()).or_default();
            match g {
                Trigger::Above(v) => add_to(&mut e.above, v, &k),
                Trigger::Below(v) => add_to(&mut e.below, v, &k),
                Trigger::Class(m, r) => add_to(&mut e.classes, &(m.clone(), r.clone()), &k),
                Trigger::Inside(l, h) => e.inside.insert(l, h, &k),
            }
        }
        self.tests.insert(k, t);
    }

    /// Takes the test of address `k` out, with its triggers.
    fn forget(&mut self, k: &Address) -> Option<KeptTest> {
        let t = self.tests.remove(k)?;
        for n in &t.free {
            self.by.remove(n, k);
        }
        for (n, _) in t.points.iter().flatten() {
            self.fixed.remove(n, k);
        }
        for (n, g) in &t.triggers {
            let Some(e) = self.triggers.get_mut(n) else {
                continue;
            };
            match g {
                Trigger::Above(v) => take_from(&mut e.above, v, k),
                Trigger::Below(v) => take_from(&mut e.below, v, k),
                Trigger::Class(m, r) => take_from(&mut e.classes, &(m.clone(), r.clone()), k),
                Trigger::Inside(l, h) => e.inside.remove(l, h, k),
            }
            if e.is_empty() {
                self.triggers.remove(n);
            }
        }
        Some(t)
    }

    /// Adds to `out` the tests a case of which `p`, the product of `n` now, leaves with no
    /// value: by its ends, and when `class_moved`, by its class.
    // Complexity tradeoff: naive, each test that reads `n` narrowed again when `n` moves,
    // Θ(k) narrowings for k tests on `n`, Θ(k·m) for m moves (61 times the bytes at 8n,
    // `split_moved_often_scales`, with that method). Used: the ends' triggers in the order
    // of their values, so a move of an end takes the triggers it passes as a range,
    // O(log k + f) for f of them, each passed once since a name's ends move only inward as
    // tests narrow it; the classes are each looked at only when the name's class moves,
    // which along one line of tests is a refinement, at most about log2 of the width of the
    // name's range times, O(c) for c classes then. A case left empty inside the name's ends
    // by a hole: naive, each case's span looked at after each move, Θ(k) a move; used, the
    // members `before` had and `p` lacks (`IntervalSet::lost_to`, O(d log p + r) for the d
    // paths of the shared tree that differ and r pieces taken out), and for each piece the
    // spans inside the run of non-members around it that reach into it
    // ([`Spans::within`], O((f + 1) log k)): a span found there lost its last member to this
    // move, so each is found once.
    fn dead(
        &self,
        n: &str,
        p: &Product,
        before: Option<&Product>,
        class_moved: bool,
        out: &mut BTreeSet<Address>,
    ) {
        let (Some(e), Some((lo, hi))) = (self.triggers.get(n), p.ints().bounds()) else {
            return;
        };
        if let Some(q) = before.filter(|_| !e.inside.is_empty()) {
            let fin = |v: &End| match v {
                End::Fin(v) => Some(v.clone()),
                _ => None,
            };
            for (a, b) in q.ints().lost_to(p.ints()) {
                // The greatest member below the piece and the least above it: none of the
                // name is between them.
                let after = p.ints().piece_at_or_below(&a).and_then(|(_, h)| fin(h));
                let next = p.ints().piece_at_or_above(&b).and_then(|(l, _)| fin(l));
                e.inside
                    .within(after.as_ref(), fin(&b).as_ref(), next.as_ref(), out);
            }
        }
        if let End::Fin(lo) = lo {
            for (_, s) in e.above.range(..lo.clone()) {
                out.extend(s.iter().cloned());
            }
        }
        if let End::Fin(hi) = hi {
            let after = (
                std::ops::Bound::Excluded(hi.clone()),
                std::ops::Bound::Unbounded,
            );
            for (_, s) in e.below.range(after) {
                out.extend(s.iter().cloned());
            }
        }
        if class_moved {
            let c = &p.cell.congruence.element;
            for ((m, r), s) in &e.classes {
                if Congruence::new(m.clone(), r.clone()).meet(c) == Congruence::Bottom {
                    out.extend(s.iter().cloned());
                }
            }
        }
    }

    /// The tests both kept and `other` keep: a test one side lacks may fail where that
    /// side's states are. Of a test both keep, with triggers that differ, this side's.
    fn join(&self, other: &KeptTests) -> KeptTests {
        let mut out = self.clone();
        for d in self.tests.diff(&other.tests) {
            if let DiffItem::Remove(k, _) = d {
                out.forget(k);
            }
        }
        out
    }
}

/// The triggers of a test whose non-empty cases are `cases`, joined in `joined`, on the names
/// of `free`: for each name and case, each end and class of the case's product of the name
/// that is narrower than the joined product's, and the span of a case inside both of the
/// joined product's ends. On a test of one name, its classes alone: the join of intervals is
/// their union, so the ends and the holes lose nothing.
fn case_triggers(cases: &[Scope], free: &[Arc<str>], joined: &Scope) -> Vec<(Arc<str>, Trigger)> {
    let mut out = Vec::new();
    for x in free {
        let p = joined.get(x);
        let Some((lo, hi)) = p.ints().bounds() else {
            continue;
        };
        for c in cases {
            let b = c.get(x);
            if free.len() > 1
                && let Some((l, h)) = b.ints().bounds()
            {
                if let End::Fin(v) = h
                    && h < hi
                {
                    out.push((x.clone(), Trigger::Above(v.clone())));
                }
                if let End::Fin(v) = l
                    && l > lo
                {
                    out.push((x.clone(), Trigger::Below(v.clone())));
                }
                // Inside both ends, so that only a hole empties it before an end passes it.
                if l > lo
                    && h < hi
                    && let (End::Fin(l), End::Fin(h)) = (l, h)
                {
                    out.push((x.clone(), Trigger::Inside(l.clone(), h.clone())));
                }
            }
            if let Congruence::Class { modulus, residue } = &b.cell.congruence.element
                && *modulus > Num::ONE
                && b.cell.congruence.element != p.cell.congruence.element
            {
                out.push((x.clone(), Trigger::Class(modulus.clone(), residue.clone())));
            }
        }
    }
    out
}

/// For each of `cases`, the names of `free` (sorted) it fixes to one value that `joined` does
/// not fix, with the values ([`KeptTest::points`]); empty when no case fixes one. `start` is
/// the scope the cases were narrowed from.
// Complexity tradeoff: naive, as before ST-relation-case-written, each name of the test read
// in each case, O(c·v) for c cases and v names: Θ(d²) for a chain of d nests, which
// `case_list` makes one list of about d cases over about 2d names (`deep_condition`'s chain of
// accounts, 18.1 times the work at 8n). Used: the cases are made one from the next on one
// work stack, so a case shares most of its persistent maps with the one before it; walking
// them in order, a name is read again only where the two differ (`images::changed`, which
// skips the parts they share), or, when the paths, their ranges or the pendant rows moved,
// for the names of the test on a path or pendant, as `NameProducts::changed` does. A pendant
// leaf whose hub moved alone is not read again, as there: its base keeps two values at most
// `low` ([`PendantRow`]), so it fixes no value while pendant. O(v log n) at the start, then
// O((Σ δ + p·m) log n + P) for δ the entries consecutive cases differ in, m the cases whose
// paths moved, p the names of the test on a path or pendant and P the points given.
fn case_points(
    start: &Scope,
    cases: &[Scope],
    free: &[Arc<str>],
    joined: &Scope,
) -> Vec<Vec<(Arc<str>, Value)>> {
    let is_free = |n: &Arc<str>| free.binary_search(n).is_ok();
    let mut pathed: BTreeSet<Arc<str>> = (free.iter())
        .filter(|x| start.names.paths.contains_key(*x) || start.names.pendants.contains_key(*x))
        .cloned()
        .collect();
    // The names of the test the case before fixes and `joined` leaves open, with the values.
    let mut fixed: BTreeMap<Arc<str>, Value> = BTreeMap::new();
    let mut prev = &start.names;
    let mut out = Vec::with_capacity(cases.len());
    for c in cases {
        let now = &c.names;
        let mut check: BTreeSet<Arc<str>> = crate::images::changed(&prev.base, &now.base)
            .filter(|n| is_free(n))
            .cloned()
            .collect();
        let entered = crate::images::changed(&prev.paths, &now.paths)
            .chain(crate::images::changed(&prev.pendants, &now.pendants));
        for n in entered.filter(|n| is_free(n)) {
            pathed.insert(n.clone());
            check.insert(n.clone());
        }
        if now.moved_since(prev) {
            check.extend(pathed.iter().cloned());
        }
        for n in check {
            match c.get(&n).value() {
                Some(v) if joined.get(&n).value().is_none() => {
                    fixed.insert(n, v.clone());
                }
                _ => {
                    fixed.remove(&n);
                }
            }
        }
        out.push(fixed.iter().map(|(n, v)| (n.clone(), v.clone())).collect());
        prev = now;
    }
    if out.iter().all(Vec::is_empty) {
        return Vec::new();
    }
    out
}

/// A name's `let` binding in a [`Scope`]; the order of its binding is in [`Scope::orders`].
#[derive(Clone, PartialEq, Debug)]
struct Binding {
    /// The lambda the name is bound to, when it is one.
    function: Option<Shared>,
    /// The summary of the integer the name is bound to, over its inputs ([`View::summary`]).
    summary: Lazy,
    /// The term of the integer the name is bound to, read when a test narrows the name and
    /// it has no summary that holds ([`Scope::through_terms`]).
    term: Option<Shared>,
}

/// The summary a binding keeps ([`Scope::summarize`]), made the first time it is read
/// ([`Lazy::get`]), in the scope the name was bound in, cut to the parts a summary reads
/// ([`Scope::basis`]). Shared by the copies of the binding, so it is made once.
///
/// Complexity tradeoff: made at each binding, as before PA-walk-nest-cost, a summary costs the
/// size of the bound term, so `d` blocks each bound inside the one before (`let z = (let y =
/// .. in ..) in ..`) cost `Θ(d²)` though no test reads them. Made when read, a binding no test
/// reads costs `O(1)` beside a copy in `O(1)` of the scope's persistent maps, which the binding
/// keeps until its summary is made; the summaries made are the same, made in the same scopes.
/// Trigger: the residual is a nest in which each bound name is read by a test, such as
/// `let z = (let y = .. in if y > 0 ..) in if z > 0 ..`: each read summary still costs its
/// whole bound term, `Θ(d²)` for `d` levels (measured in COMPLEXITY.md row PA-walk-nest-cost). Test of
/// the fixed case: `l01_39_reduced_product::if_shortcut::one_pass_and_transfer_scale_on_deep_nests`;
/// a deep chain is made and dropped without recursion in
/// `l01_39_reduced_product::if_shortcut::a_deep_chain_of_bindings_is_walked_and_dropped`.
/// A complete solution would make a block's summary from those of its parts, bottom up.
#[derive(Clone)]
struct Lazy(Arc<Mutex<Making>>);

enum Making {
    /// Not read yet: the bound term, the scope it was bound in, and its free names once
    /// found.
    Pending {
        e: Shared,
        basis: Basis,
        free: Option<BTreeSet<Arc<str>>>,
    },
    Made(Option<Arc<Held>>),
}

/// The parts of the scope a [`Lazy`] summary is made in that a summary reads
/// ([`View::summarize_free`]), each a copy in `O(1)` of a persistent map or a number. A chain
/// of bindings keeps a chain of these, each holding the bindings before it, so one is dropped
/// by a loop on its thread rather than by recursion down the chain.
struct Basis(Option<Box<Parts>>);

struct Parts {
    // The scope's names as they were, an O(1) copy that shares the exact-map cache of that
    // version ([`NameProducts::view`]): with difference paths, the map is built only when the
    // summary is made, not at every binding (item ST-walk-checker-admit).
    names: NameProducts,
    bindings: imbl::OrdMap<Arc<str>, Binding>,
    orders: Orders,
}

impl Parts {
    /// The parts as a summary reads them ([`View`]), of a scope some state reaches
    /// ([`Scope::summarizes`]).
    fn view(&self) -> View<'_> {
        View {
            names: &self.names,
            bindings: &self.bindings,
            orders: &self.orders,
            bottom: false,
        }
    }
}

thread_local! {
    /// The bases waiting to be dropped by the loop of a [`Basis`] drop further up the stack,
    /// and whether one is running.
    static DROPPING: (std::cell::Cell<bool>, RefCell<Vec<Parts>>) =
        const { (std::cell::Cell::new(false), RefCell::new(Vec::new())) };
}

impl Drop for Basis {
    fn drop(&mut self) {
        let Some(s) = self.0.take() else { return };
        // At thread exit the queue is gone and the scope is dropped where it is.
        let _ = DROPPING.try_with(|(running, queue)| {
            if running.get() {
                queue.borrow_mut().push(*s);
                return;
            }
            running.set(true);
            let mut next = Some(*s);
            while let Some(s) = next {
                drop(s);
                next = queue.borrow_mut().pop();
            }
            running.set(false);
        });
    }
}

/// The parts of a [`Scope`] the summaries of its bindings read, borrowed from a scope
/// ([`Scope::view`]) or from the [`Parts`] a [`Lazy`] summary keeps, so that a summary made
/// when first read builds no scope.
#[derive(Clone, Copy)]
struct View<'a> {
    names: &'a imbl::OrdMap<Arc<str>, Product>,
    bindings: &'a imbl::OrdMap<Arc<str>, Binding>,
    orders: &'a Orders,
    bottom: bool,
}

impl View<'_> {
    /// [`Scope::get`].
    fn get(&self, name: &str) -> Product {
        if self.bottom {
            return Product::bottom();
        }
        self.names.get(name).cloned().unwrap_or_else(Product::top)
    }

    /// The summary of `e`, of free names `free`, in this scope ([`Scope::summarize`]).
    fn summarize_free(&self, e: &Term, free: &BTreeSet<Arc<str>>) -> Option<Arc<Held>> {
        let (inputs, lets, widest) = self.inputs_and_lets(free, false);
        let s = let_summary(e, &inputs, lets)?;
        let made = Made::Scope(self.names.clone());
        Some(Held::new(s, made, self.orders.clone(), widest))
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
    ///
    /// Complexity tradeoff: naive version, each input of the summary checked at each read,
    /// O(k) a read, Θ(k²) for k reads of summaries over k inputs (1,680 leaves set at k = 40,
    /// 103,040 at k = 320). Used: the tree of the last read updated at the names that differ,
    /// O(m log k) for m differences (158 and 1,278; COMPLEXITY.md row PA-walk-multi).
    /// Tradeoffs: memory, one read per summary id kept in `Reads` for the life of the scope's
    /// copies, never freed during a walk (row PA-bind-cost); a lock per read; when the
    /// differences reach the inputs the read is made afresh, at the naive cost.
    fn holds(&self, held: &Arc<Held>) -> bool {
        // The names whose products or orders differ between the scope of `r` and `s`.
        fn here<'a>(r: &'a HeldRead, s: View<'a>) -> impl Iterator<Item = &'a Arc<str>> + 'a {
            let names = images::changed(&r.names, s.names);
            names.chain(images::changed(&r.sum, s.orders))
        }
        let vars = held.summary.vars();
        let limit = vars.len().min(self.names.len());
        let leaf = |v: &Arc<str>, q: &Product| held.leaf(self.orders, v, q);
        let mut last = held.last();
        // Complexity tradeoff: naive version, a summary over one input is read from the last
        // read too, by the differences of up to four pairs of persistent maps, about 6,000
        // instructions each on the 1,000 names of the fee test, and these reach the one input
        // at the second difference, so the tree is then made afresh anyway. Used: a summary
        // over one input is read afresh at once, one lookup, `O(log n)` as a walk to the first
        // difference is, and the same tree, whose shape the keys fix; about 28,000
        // instructions a binding fewer (COMPLEXITY.md row PA-bind-cost). Test:
        // `l01_39_reduced_product::deep_let::the_arms_of_a_deep_block_scale`.
        let tree = if vars.len() == 1 {
            None
        } else {
            match &last.held {
                Some(r) => images::updated(&r.tree, here(r, *self), vars, self.names, limit, leaf),
                None => (held.widest.as_ref().and_then(Weak::upgrade)).and_then(|base| {
                    let (Made::Scope(was), Made::Scope(now)) = (&base.made, &held.made) else {
                        return None;
                    };
                    let reads = base.last();
                    let r = reads.held.as_ref()?;
                    let inputs = (base.summary.vars().diff(vars)).map(|d| match d {
                        imbl::ordset::DiffItem::Add(v) | imbl::ordset::DiffItem::Remove(v) => v,
                    });
                    let changed = (inputs.chain(images::changed(was, now)))
                        .chain(images::changed(&base.orders, &held.orders))
                        .chain(here(r, *self));
                    images::updated(&r.tree, changed, vars, self.names, limit, leaf)
                }),
            }
        }
        .unwrap_or_else(|| images::fresh(vars, self.names, leaf));
        let holds = images::total(&tree).fails == 0 && images::len(&tree) == vars.len();
        last.held = Some(images::Read {
            names: self.names.clone(),
            sum: self.orders.clone(),
            tree,
        });
        holds
    }

    /// The held summary of the integer `x` is bound to, made if it was not ([`Lazy::get`]),
    /// when it has one and it holds ([`View::holds`]).
    fn summary(&self, x: &Arc<str>) -> Option<Arc<Held>> {
        let held = self.bindings.get(x)?.summary.get()?;
        self.holds(&held).then_some(held)
    }

    /// The integer names of `free`, as inputs over their integers, or, when bound by a `let`
    /// with a summary that holds ([`View::summary`]), as names read through it, and the
    /// summary with the most inputs among these. With `all`, for a test, which narrows
    /// the inputs of each summary too ([`let_narrowing`]), a summary over two or more inputs
    /// is read through the tree of its terms' bounds ([`View::term_read`]), its inputs not
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
    ) -> (Domains, Lets, Option<Weak<Held>>) {
        debug_assert!(
            !(all && self.bottom),
            "a test read in a scope no state reaches"
        );
        let int = Type::int();
        let mut inputs = Domains::new();
        let mut lets = Lets::new();
        let mut widest: Option<(usize, Arc<Held>)> = None;
        for n in free {
            let p = self.get(n);
            if !self.names.contains_key(n) || !p.ty.element.subtype(&int) {
                continue;
            }
            match self.summary(n) {
                Some(held) => {
                    let k = held.summary.vars().len();
                    let mut read = None;
                    if all && k > 1 {
                        read = Some(Arc::new(self.term_read(&held)) as _);
                    } else if all || k == 1 {
                        for v in held.summary.vars() {
                            inputs.insert(v.clone(), self.get(v).ints().clone());
                        }
                    }
                    lets.insert(
                        n.clone(),
                        LetIn {
                            summary: held.summary.clone(),
                            ints: p.ints().clone(),
                            read,
                        },
                    );
                    if widest.as_ref().is_none_or(|(w, _)| k > *w) {
                        widest = Some((k, held));
                    }
                }
                None => _ = inputs.insert(n.clone(), p.ints().clone()),
            }
        }
        (inputs, lets, widest.map(|(_, held)| Arc::downgrade(&held)))
    }

    /// The inputs of the summary `held`, as a test reads them here: each input's
    /// integers, and the bounds of the summary's term of each ([`LetPa::term_bounds`]) in a
    /// tree found from that of the last test of the summary by setting the inputs whose
    /// products differ between the two scopes ([`images::updated`]), or afresh when there is
    /// none or the differences are as many as the inputs ([`images::fresh`]). Costs the lesser
    /// of the differences and the inputs, times `O(log k)` for `k` inputs: `k` tests of one
    /// name, each narrowing a few names, cost `O(k log k)`, where reading the inputs cost
    /// `O(k)` a test (item PA-letpre-linear). The summary holds here ([`View::holds`]), so
    /// the scope has each of its inputs.
    ///
    /// Complexity tradeoff: naive version, each test of a name over k inputs builds the
    /// domains of all k, bounds each term and meets each input, O(k) a test and Θ(k²) for k
    /// tests (3,200 term bounds at k = 40, 204,800 at k = 320). Used: this tree of the terms'
    /// bounds, updated at the inputs that changed, and `Tx::invert_sep` inverting only the
    /// terms wider than the slack (`Sums::wants`), each found in O(log k), so a test costs the
    /// inputs it narrows (COMPLEXITY.md row PA-letpre-linear). Tradeoffs: one tree kept per
    /// summary, that of its last test (`Held::last`); a term the inversion does not read as a
    /// whole (an end at an end of `i128`, pieces with a gap) is always inverted, so such terms
    /// cost what they did; results are the same as reading every input (checked on 800 random
    /// sums).
    fn term_read(&self, held: &Held) -> images::TermRead<Product> {
        let vars = held.summary.vars();
        let limit = vars.len().min(self.names.len());
        let leaf = |v: &Arc<str>, q: &Product| held.summary.term_bounds(v, q.ints());
        let mut last = held.last();
        let tree = (last.bounds.as_ref())
            .and_then(|r| {
                let changed = images::changed(&r.names, self.names);
                images::updated(&r.tree, changed, vars, self.names, limit, leaf)
            })
            .unwrap_or_else(|| images::fresh(vars, self.names, leaf));
        last.bounds = Some(images::Read {
            names: self.names.clone(),
            sum: (),
            tree: tree.clone(),
        });
        images::TermRead {
            names: self.names.clone(),
            vars: vars.clone(),
            tree,
            ints: Product::ints,
        }
    }
}

impl Lazy {
    /// Whether the summary reads no name but `n`, made or not.
    fn reads_only(&self, n: &Arc<str>) -> bool {
        match &*self.lock() {
            Making::Pending { e, .. } => matches!(&**e, Term::Var(m) if m == n),
            Making::Made(held) => held
                .as_ref()
                .is_none_or(|h| h.summary.vars().iter().all(|v| v == n)),
        }
    }

    fn made(held: Option<Arc<Held>>) -> Lazy {
        Lazy(Arc::new(Mutex::new(Making::Made(held))))
    }

    fn pending(e: &Shared, basis: Parts) -> Lazy {
        Lazy(Arc::new(Mutex::new(Making::Pending {
            e: e.clone(),
            basis: Basis(Some(Box::new(basis))),
            free: None,
        })))
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Making> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// The summary, made first when it was not. The summaries of the names its term reads are
    /// made before it, those they read before them, and so on, by a loop over a stack rather
    /// than by recursion; each is made once.
    fn get(&self) -> Option<Arc<Held>> {
        let mut todo = vec![self.clone()];
        while let Some(top) = todo.last().cloned() {
            let mut m = top.lock();
            let Making::Pending { e, basis, free } = &mut *m else {
                todo.pop();
                continue;
            };
            let s = basis
                .0
                .as_deref()
                .expect("a pending summary keeps its parts");
            let free = free.get_or_insert_with(|| stage::free(e));
            let waiting: Vec<Lazy> = (free.iter())
                .filter(|n| s.names.contains_key(n))
                .filter_map(|n| s.bindings.get(n))
                .filter(|b| matches!(*b.summary.lock(), Making::Pending { .. }))
                .map(|b| b.summary.clone())
                .collect();
            if waiting.is_empty() {
                let held = s.view().summarize_free(e, free);
                *m = Making::Made(held);
                todo.pop();
            } else {
                drop(m);
                todo.extend(waiting);
            }
        }
        match &*self.lock() {
            Making::Made(held) => held.clone(),
            Making::Pending { .. } => unreachable!("made above"),
        }
    }
}

impl PartialEq for Lazy {
    /// Whether both have a summary or both have none; the summaries are caches, equal in every
    /// binding, as [`Held`] is.
    fn eq(&self, other: &Lazy) -> bool {
        self.get().is_some() == other.get().is_some()
    }
}

impl fmt::Debug for Lazy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("..")
    }
}

/// The order of each name's binding in a [`Scope`]: a binding made later has a larger one. A
/// map of its own, apart from the bindings, so that a summary keeps the orders it was made
/// with ([`Held`]) and not the bindings, which keep summaries in turn.
type Orders = imbl::OrdMap<Arc<str>, u64>;

/// The summary of the value of a `let` ([`LetPa`]) as its binding keeps it, with what it was
/// made over: it holds while each input it reads is the binding it was and that input's
/// integers lie within those it was made over ([`Scope::holds`]). A cache, equal in every
/// binding, as [`Reduced`] is.
///
/// It keeps its own last reads ([`LastReads`]), so that they are freed with it, when the last
/// binding that holds it is unbound or dropped (item PA-read-cache-free). They were kept in a
/// map by a number of each summary, shared by every copy of the scope and never emptied, so a
/// walk held every read it had made: 6.5 MB for 1,000 blocks walked one after another, 54.8 MB
/// for 8,000, left in the scope it was given
/// (`deep_let::the_walk_of_blocks_one_after_another_holds_the_bytes_of_one_block`).
struct Held {
    summary: LetPa,
    /// The integers of the inputs when it was made.
    made: Made,
    /// The orders of the bindings when it was made.
    orders: Orders,
    /// The held summary with the most inputs among those of the names the value reads, whose
    /// read the first read of this one starts from ([`Scope::holds`]). Weak, so that it is
    /// freed with its own binding: a chain of summaries each holding the one before would be
    /// freed only with the last, and freed recursively, one frame per summary. It was made
    /// before this one, so a lock of its reads taken while this one's is held ([`Scope::holds`])
    /// always goes from a later summary to an earlier one, and two such locks never wait on
    /// each other.
    widest: Option<Weak<Held>>,
    /// What this summary read where it was last read, and what a test last read of it.
    last: Mutex<LastReads>,
}

/// The integers of the inputs of a [`Held`] summary when it was made.
enum Made {
    /// Those of the names of the scope it was made in, all its inputs among them.
    Scope(imbl::OrdMap<Arc<str>, Product>),
    /// Those given with it ([`Scope::bind_summarized`]).
    Given(Domains),
}

impl Held {
    fn new(summary: LetPa, made: Made, orders: Orders, widest: Option<Weak<Held>>) -> Arc<Held> {
        Arc::new(Held {
            summary,
            made,
            orders,
            widest,
            last: Mutex::default(),
        })
    }

    /// The last reads of this summary, locked.
    fn last(&self) -> MutexGuard<'_, LastReads> {
        self.last.lock().unwrap_or_else(PoisonError::into_inner)
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

/// What one summary read: the scope's names, the orders of the scope's bindings, and the tree
/// of its inputs.
type HeldRead = images::Read<Orders, Products>;

/// What a test last read of one summary: the scope's names, and the tree of the bounds of the
/// summary's terms over the inputs there ([`View::term_read`]).
type BoundsRead = images::Read<(), Products, TermBounds>;

/// The last reads of a [`Held`] summary, in whichever copy of the scope they were made: what
/// it read in the scope of its last read ([`HeldRead`]), from which the next read is found
/// ([`Scope::holds`]), and what a test last read of it ([`BoundsRead`]). A read finds the same
/// whichever earlier read it starts from.
#[derive(Default)]
struct LastReads {
    held: Option<HeldRead>,
    bounds: Option<BoundsRead>,
}

/// The names of the scope a copy last emptied ([`Scope::empty_if_bottom`]), each the bottom,
/// with the orders of its bindings then.
struct Emptying {
    orders: Orders,
    names: imbl::OrdMap<Arc<str>, Product>,
}

/// Whether each name of a scope no state reaches is already the bottom
/// ([`Scope::empty_if_bottom`]): a cache, equal in every scope, so that the arms a walk shows
/// below a test no state passes empty the names once and not once each; and the names a
/// copy of the scope last emptied ([`Emptying`]), shared by the copies, from which the next
/// emptying is found.
#[derive(Clone, Default)]
struct Emptied(bool, Arc<Mutex<Option<Emptying>>>);

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
    /// A sequence of fresh-leaf rows certified not to change any product.
    extension: Option<Arc<Extension>>,
    projection: Option<Projection>,
    enumeration: Option<Enumeration>,
    /// Each block as its last projection left it ([`Block::update`]), and the blocks whose
    /// part each key is (a free conjunct at a hub is a part of each wide block at the hub,
    /// under one key): a part whose record is taken away or changed outside its block's
    /// projection ([`Seen::drop_part`]) is due at the block's next projection
    /// ([`Block::forgot`]), since only a change of its conjuncts or names would otherwise
    /// make it due. Each block is shared, so that a copy of an entry, as a path copy of the
    /// persistent map makes for each entry of a node it changes, costs a reference count and
    /// not the block's twenty fields (item PERF-seen-blocks-arc).
    // Complexity tradeoff: a `Block` held by value was cloned with each entry a path copy
    // copies, up to 16 a node, each clone about twenty reference counts and 360 bytes of node;
    // behind an `Arc` an entry is one pointer, and a block is cloned only where it is changed
    // in place (`Seen::drop_part`, `Arc::make_mut`) or brought up to date (`Block::update`,
    // which makes a new block from the kept one as before). The order is unchanged, O(log b)
    // per keep for `b` kept blocks; the constant drops. COMPLEXITY.md C44.
    blocks: imbl::OrdMap<BlockId, Arc<Block>>,
    owners: imbl::OrdMap<PartKey, imbl::OrdSet<BlockId>>,
    /// Each class's bound on its leaf, as [`Scope::leaf_bound_stays`] last found it
    /// ([`LeafBound`]).
    bounds: imbl::OrdMap<conjuncts::Class, LeafBound>,
    /// The leaves of the stars, ordered by their products ([`Order`]), in an eager scope.
    order: Order,
}

/// A lower-end witness for all rows added after independent unary bounds. The snapshots make
/// the certificate invalid after any other change, including a direct public-field edit.
enum Extension {
    Certified {
        hub: Arc<str>,
        used: imbl::OrdSet<Arc<str>>,
        names: imbl::OrdMap<Arc<str>, Product>,
        relation: RelationMark,
    },
    /// A conjunct preventing an independent starting product. Remember it so a rejected
    /// extension does not scan the unary bounds again at every later test.
    Coupled(Arc<Formula>),
}

impl Extension {
    fn certified(&self) -> bool {
        matches!(self, Self::Certified { .. })
    }
}

impl Seen {
    /// Makes the part of key `key` due at the next projection of each kept block that holds
    /// it, once its record is taken away or changed outside the blocks' projections.
    ///
    /// Complexity tradeoff: naive version, the kept blocks forgotten and made anew at their
    /// next projection, O(k log k) for `k` parts each, at each join whose sides projected a
    /// part with other constraints, as two cases of a test that each add one among the hubs
    /// of a star. Used: the part alone noted as due in each block that holds it
    /// ([`Block::forgot`]), O(s log k) for `s` such blocks. Tradeoffs: a block's owner entry
    /// for the key stays while the block keeps the part, so a later record taken away finds
    /// the block too; the entry of a block that no longer holds the part is removed when
    /// found, so each entry is passed over once after its part goes. COMPLEXITY.md row C26.
    fn drop_part(&mut self, key: &PartKey) {
        let Some(ids) = self.owners.get(key) else {
            return;
        };
        // Complexity tradeoff: the key's formula is shared, O(1), where it was copied, O(t) in
        // its t terms, for each part dropped. COMPLEXITY.md C41.
        let at: PartAt = (matches!(*key.0, Formula::Con(_)), key.0.clone());
        let mut gone: Vec<BlockId> = Vec::new();
        for b in ids {
            match self.blocks.get_mut(b) {
                Some(block) if block.parts.contains_key(&at) => {
                    // Complexity tradeoff: copy on write, the one block changed is cloned
                    // when another scope shares it, O(1) in its persistent fields, where a
                    // path copy of the map cloned every block of the node. COMPLEXITY.md C44.
                    Arc::make_mut(block).forgot.insert(at.clone());
                }
                _ => gone.push(*b),
            }
        }
        if gone.is_empty() {
            return;
        }
        if let Some(ids) = self.owners.get_mut(key) {
            for b in &gone {
                ids.remove(b);
            }
            if ids.is_empty() {
                self.owners.remove(key);
            }
        }
    }

    /// Forgets every kept block, once records of parts are taken away or changed wholesale.
    fn drop_blocks(&mut self) {
        self.blocks = imbl::OrdMap::new();
        self.owners = imbl::OrdMap::new();
    }
}

/// The bound a class's conjuncts give its leaf ([`Scope::core_leaf_bound`]), with what it was
/// found from: the free conjuncts at each hub, the names' products, the names the conjuncts
/// mention and their constraints together. While those free conjuncts and the products of
/// those names stay, the bound stays, and a conjunct added among the hubs that is not a
/// constraint adds one part, whose bound met with this one is the class's new bound.
#[derive(Clone)]
struct LeafBound {
    free: imbl::OrdMap<Arc<str>, imbl::OrdSet<Arc<Formula>>>,
    names: imbl::OrdMap<Arc<str>, Product>,
    mentioned: imbl::OrdSet<Arc<str>>,
    base: Arc<Formula>,
    bound: IntervalSet,
}

/// The leaves of the stars of an eager scope ([`Conjuncts::star`]), each family's
/// ([`conjuncts::family`]) ordered by the ends of its leaves' products, so that a move of a
/// hub projects only the stars whose leaf the family's bound now cuts ([`Scope::moved_blocks`]).
/// A star of one hub has no class in the relation; here its conjuncts with the leaf written
/// [`conjuncts::LEAF`] are its class. A class's bound on its leaf is its family's moved by
/// the class's constant ([`Order::place`]), so each leaf is keyed by the ends of its product
/// less that shift, and the leaves a bound `[l, u]` of the family cuts are those of key below
/// `l` at one end and above `u` at the other. A leaf whose star was not projected in this scope
/// as it is now ([`Order::projected`]) is keyed by the two infinities, so every bound cuts it.
/// Brought up to date from the relation and names it last saw by their differences
/// ([`Order::sync`]); persistent, so a copy of the scope shares it.
#[derive(Clone, Default)]
struct Order {
    relation: Option<Conjuncts>,
    names: imbl::OrdMap<Arc<str>, Product>,
    of: imbl::OrdMap<Arc<str>, Placed>,
    low: imbl::OrdMap<conjuncts::Class, imbl::OrdSet<(End, Arc<str>)>>,
    high: imbl::OrdMap<conjuncts::Class, imbl::OrdSet<(End, Arc<str>)>>,
    /// The families with a leaf, at each of their hubs.
    at: Uses<conjuncts::Class>,
    /// The conjuncts of each leaf's star when an eager projection of it last ended without a
    /// question refused: the star's projection onto its hubs then holds of their products, and
    /// goes on holding as they narrow, so only a change of its leaf can change it
    /// ([`Conjuncts::star`]).
    projected: imbl::OrdMap<Arc<str>, imbl::OrdSet<Arc<Formula>>>,
}

/// A leaf's place in [`Order`]: its family and the ends of its product less the shift of its
/// class's bound from the family's.
#[derive(Clone)]
struct Placed {
    family: conjuncts::Class,
    lo: End,
    hi: End,
}

impl Order {
    /// Places again each leaf whose star, class or product changed since the last call, in
    /// O(c log n) for `c` changes, the persistent maps' differences skipping what they share.
    fn sync(&mut self, relation: &Conjuncts, names: &imbl::OrdMap<Arc<str>, Product>) {
        let mut touched: BTreeSet<Arc<str>> = BTreeSet::new();
        match &self.relation {
            None => touched.extend(relation.stars().keys().cloned()),
            Some(old) => {
                for d in old.stars().diff(relation.stars()) {
                    let (DiffItem::Add(x, _)
                    | DiffItem::Remove(x, _)
                    | DiffItem::Update { new: (x, _), .. }) = d;
                    touched.insert(x.clone());
                }
                for d in old.classes_of().diff(relation.classes_of()) {
                    let (DiffItem::Add(x, _)
                    | DiffItem::Remove(x, _)
                    | DiffItem::Update { new: (x, _), .. }) = d;
                    touched.insert(x.clone());
                }
                for d in old.set().diff(relation.set()) {
                    let (imbl::ordset::DiffItem::Add(g) | imbl::ordset::DiffItem::Remove(g)) = d;
                    touched.extend(conjuncts::names(g));
                }
            }
        }
        for d in self.names.diff(names) {
            let (DiffItem::Add(x, _)
            | DiffItem::Remove(x, _)
            | DiffItem::Update { new: (x, _), .. }) = d;
            touched.insert(x.clone());
        }
        for x in &touched {
            self.place(relation, names, x);
        }
        self.relation = Some(relation.clone());
        self.names = names.clone();
    }

    /// Notes that the star of `x` was projected, `refused` when a question was refused in
    /// it, and places `x` again.
    fn mark(
        &mut self,
        relation: &Conjuncts,
        names: &imbl::OrdMap<Arc<str>, Product>,
        x: &Arc<str>,
        refused: bool,
    ) {
        match relation.star(x) {
            Some(b) if !refused => {
                let gs = relation.blocks().members(b).cloned().collect();
                self.projected.insert(x.clone(), gs);
            }
            _ => _ = self.projected.remove(x),
        }
        self.place(relation, names, x);
    }

    /// Puts `x` in its family's order as the relation and names have it, or takes it out
    /// when it is no leaf. In O(log n), and O(s log s) for a star of one hub of `s` conjuncts.
    fn place(
        &mut self,
        relation: &Conjuncts,
        names: &imbl::OrdMap<Arc<str>, Product>,
        x: &Arc<str>,
    ) {
        self.unplace(x);
        let Some(b) = relation.star(x) else {
            self.projected.remove(x);
            return;
        };
        let leaf = Atom::Sym(Arc::from(conjuncts::LEAF));
        let class: conjuncts::Class = match relation.class_of(x) {
            Some(c) => c.clone(),
            None => {
                let mut gs: Vec<Arc<Formula>> = relation
                    .blocks()
                    .members(b)
                    .map(|g| Arc::new(g.map_cons(&|c| leaf_written(c, x, &leaf))))
                    .collect();
                gs.sort_unstable();
                gs.into()
            }
        };
        let family = conjuncts::family(&class);
        // The class `a·#leaf + t + k >= 0` of its family `a·#leaf + t >= 0`, `a` one or minus
        // one, bounds its leaf by the family's bound moved by `-a·k`.
        let shift = match &*class {
            [g] if family != class
                && let Formula::Con(c) = &**g
                && let Some(a) = c.lin.terms.get(&leaf) =>
            {
                -&(&Num::from(a) * &Num::from(&c.lin.constant))
            }
            _ => Num::ZERO,
        };
        let projected =
            (self.projected.get(x)).is_some_and(|gs| relation.blocks().members(b).eq(gs.iter()));
        let less = |e: &End| match e {
            End::Fin(v) => End::Fin(v - &shift),
            e => e.clone(),
        };
        // A name out of scope is the top, and an empty product is cut by every bound.
        let (lo, hi) = match names.get(x).and_then(|p| p.ints().bounds()) {
            Some((lo, hi)) if projected => (less(lo), less(hi)),
            _ => (End::NegInf, End::PosInf),
        };
        if !self.low.contains_key(&family) {
            for h in family_hubs(&family) {
                self.at.add(&h, &family);
            }
        }
        (self.low.entry(family.clone()).or_default()).insert((lo.clone(), x.clone()));
        (self.high.entry(family.clone()).or_default()).insert((hi.clone(), x.clone()));
        self.of.insert(x.clone(), Placed { family, lo, hi });
    }

    /// Takes `x` out of its family's order, in O(log n).
    fn unplace(&mut self, x: &Arc<str>) {
        let Some(p) = self.of.remove(x) else {
            return;
        };
        let key = (p.lo, x.clone());
        if let Some(s) = self.low.get_mut(&p.family) {
            s.remove(&key);
            if s.is_empty() {
                self.low.remove(&p.family);
                for h in family_hubs(&p.family) {
                    self.at.remove(&h, &p.family);
                }
            }
        }
        let key = (p.hi, x.clone());
        if let Some(s) = self.high.get_mut(&p.family) {
            s.remove(&key);
            if s.is_empty() {
                self.high.remove(&p.family);
            }
        }
    }
}

/// The names but the leaf that a class or family mentions: its hubs.
fn family_hubs(f: &conjuncts::Class) -> BTreeSet<Arc<str>> {
    f.iter()
        .flat_map(|g| conjuncts::names(g))
        .filter(|n| &**n != conjuncts::LEAF)
        .collect()
}

/// Constraint `c` with the name `x` written `leaf`.
fn leaf_written(c: &Con, x: &str, leaf: &Atom) -> Formula {
    let terms = (c.lin.terms.iter())
        .map(|(a, k)| match a {
            Atom::Sym(n) if &**n == x => (leaf.clone(), k.clone()),
            _ => (a.clone(), k.clone()),
        })
        .collect();
    Formula::Con(Con {
        lin: Lin {
            terms,
            constant: c.lin.constant.clone(),
        },
        rel: c.rel,
    })
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

/// The names in components, ranked so that every edge from one component to another goes to a
/// higher rank, with a value of each name at which every difference constraint within one
/// component holds, each edge's weight lowered by the gap of the name it enters: under it no
/// edge has a negative reduced weight within a component, and every cycle lies within one, so
/// a Dijkstra search on the rank of a name's component first and its reduced distance second
/// finds the bounds of a tree of blocks projected by shortest paths ([`Scope::shortest`]). A
/// component holds each strongly connected component of the edges, and may hold more: an edge
/// that goes leaves its components as they were. It holds at every edge of the relation as of
/// its last projection, except the edges of names it lacks: each edge added is put in it at
/// the next projection, whichever way its tree is projected ([`Scope::repair`]), and a
/// projection of every block ([`Due::All`]) empties it. A cache, equal in every scope, and
/// checked at every edge it is read at.
///
/// A name's gap is the length of the longest run of integers its interval leaves out between
/// its ends ([`hole_gap`]); the potential holds with the gap in `gap`, which is at least the
/// name's own unless the relation records the name as keeping its tree from shortest paths
/// ([`Conjuncts::gapped`], [`Scope::sync_bounds`]). Every cycle `C` of edges, which lies in
/// one component, then has a weight of at least the sum of the gaps of its names, which is
/// what makes shortest paths with holes the projection ([`Scope::shortest`]).
///
/// Complexity tradeoff: naive version, one value for every name with the potential holding at
/// every edge, as before item PRODUCT-lin-rows; built edge by edge it ends with no slack along
/// a chain, so each edge made heavier or gap raised lowered every name below it, O(k) a test
/// and O(k²) for `k` tests on a chain or a ladder, used for nothing when no bound moves. Used:
/// the value holds within each component alone, and the components keep a topological order
/// (Pearce and Kelly, "A dynamic topological sort algorithm for directed acyclic graphs", ACM
/// JEA 11, 2006): an edge to a later component costs O(1), an edge within one or a gap raised
/// searches that component alone, and an edge against the order searches the components ranked
/// between its ends from both ends in step, the one that ends first moving what it found, and
/// merging those on a cycle ([`reorder`]), so that it costs the components moved; the ranks
/// are an order-maintenance list, which gives a rank between two neighbors ([`Potential::rank_after`]),
/// and a merge reads the edge ends of the components it moves, never those of the largest
/// ([`merge`]). A new name with an edge back to a component joins it rather than taking a
/// component of its own ([`put_in`]). Tradeoffs: a component is never split when an
/// edge goes, so a join that keeps the side whose edges closed cycles leaves the components
/// larger than the strongly connected ones, and a later search of one reads all of it; an edge
/// against the order costs the components the search that ends first finds, O(n) at worst for
/// one edge.
/// Tests: `l01_39_reduced_product::linked::if_statements_joined_one_after_another_on_a_linked_chain_take_time_near_their_number`,
/// `…::if_statements_on_skip_links_of_a_chain_take_time_near_their_number`,
/// `…::if_statements_that_put_a_hole_in_a_ladder_between_rungs_are_linear`,
/// `…::a_ladder_grown_by_k_if_statements_is_linear`,
/// `…::holes_put_in_a_ladder_built_first_are_linear`,
/// `…::a_chain_linked_from_a_source_made_later_is_linear`,
/// `…::a_chain_put_in_against_the_order_reads_only_what_it_moves`,
/// `l01_39_reduced_product::scaling::a_join_keeps_the_equalities_of_its_sides_and_scales`.
/// COMPLEXITY.md S25, S25b.
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
    /// Each name's component, for each name with a value.
    comp: imbl::OrdMap<Arc<str>, u64>,
    /// Each component; no two share a rank.
    parts: imbl::OrdMap<u64, Component>,
    /// Each component by its rank, the inverse of their ranks.
    order: imbl::OrdMap<i64, u64>,
    /// The number of the next component.
    next: u64,
}

impl Potential {
    /// The gap the edges into `n` are lowered by.
    fn gap_of(&self, n: &str) -> Int {
        self.gap.get(n).cloned().unwrap_or(Int::ZERO)
    }

    /// The rank of component `c`, one of `parts`.
    fn rank(&self, c: u64) -> i64 {
        self.parts[&c].rank
    }

    /// Records that `u` and `v`, with values, are the ends of an edge, which goes between
    /// components unless they share one ([`Component::ends`]).
    fn link(&mut self, u: &Arc<str>, v: &Arc<str>) {
        let (Some(&cu), Some(&cv)) = (self.comp.get(u), self.comp.get(v)) else {
            return;
        };
        if cu == cv {
            return;
        }
        for (c, n) in [(cu, u), (cv, v)] {
            if let Some(p) = self.parts.get_mut(&c) {
                p.ends.insert(n.clone());
            }
        }
    }

    /// The component of `n`, which the potential lacks unless it has a value.
    fn comp_of(&self, n: &str) -> Result<u64, Fall> {
        self.comp.get(n).copied().ok_or(Fall::Potential)
    }

    /// Gives `n`, new to the potential, the value `at` and a component of its own, ranked
    /// before every other with `first`, after every other otherwise.
    fn fresh(&mut self, n: &Arc<str>, at: (Int, i64), first: bool) {
        self.at.insert(n.clone(), at);
        self.comp.insert(n.clone(), self.next);
        let part = Component {
            rank: 0,
            names: imbl::OrdSet::unit(n.clone()),
            ends: imbl::OrdSet::new(),
        };
        self.parts.insert(self.next, part);
        let after = if first { None } else { self.last() };
        self.rank_after(self.next, after);
        self.next += 1;
    }

    /// Gives `n`, new to the potential, the value `at` in component `c`, one of `parts`.
    fn enter(&mut self, n: &Arc<str>, at: (Int, i64), c: u64) {
        self.at.insert(n.clone(), at);
        self.comp.insert(n.clone(), c);
        if let Some(p) = self.parts.get_mut(&c) {
            p.names.insert(n.clone());
        }
    }

    /// Takes `n` out of the potential and out of its component, which is dropped once empty.
    fn leave(&mut self, n: &Arc<str>) {
        self.at.remove(n);
        let Some(c) = self.comp.remove(n) else {
            return;
        };
        if let Some(p) = self.parts.get_mut(&c) {
            p.names.remove(n);
            p.ends.remove(n);
            if p.names.is_empty() {
                let r = p.rank;
                self.parts.remove(&c);
                self.order.remove(&r);
            }
        }
    }

    /// The greatest rank given, if any.
    fn last(&self) -> Option<i64> {
        self.order.get_max().map(|&(r, _)| r)
    }

    /// Gives component `c`, one of `parts` and with no rank in `order`, the rank `r`, free.
    fn set_rank(&mut self, c: u64, r: i64) {
        self.order.insert(r, c);
        if let Some(p) = self.parts.get_mut(&c) {
            p.rank = r;
        }
    }

    /// Takes component `c`, one of `parts`, out of `order`, to be ranked again.
    fn unrank(&mut self, c: u64) {
        self.order.remove(&self.rank(c));
    }

    /// Gives component `c`, one of `parts`, the rank `r`, free or its own.
    fn rerank(&mut self, c: u64, r: i64) {
        self.unrank(c);
        self.set_rank(c, r);
    }

    /// Gives component `c`, one of `parts` and with no rank in `order`, a rank right after
    /// `after`, or before every other with none, from `0..RANKS`: the middle one of those
    /// between `after` and the next rank given, or at an end with none beyond it at most
    /// [`END_STEP`] from the rank there; when none is free, the components of the
    /// smallest range of `2^i` ranks aligned at a multiple of `2^i` around `after` that holds
    /// at most `1.6^i` components, `c` counted, take ranks spread evenly over it (Bender, Cole,
    /// Demaine, Farach-Colton and Zito, "Two simplified algorithms for maintaining order in a
    /// list", ESA 2002). Returns the number of other components ranked again.
    // Complexity tradeoff: naive version, the ranks of the components after `after` each
    // raised by one, O(n log n) a rank given, and ranks of `i64` given only before the first
    // or after the last (as before item PERF-pk-one-sided), O(1) but unable to put a component
    // between two. Used: O(log n) amortized components ranked again for each rank given, each
    // O(log n) in `order`, O(log² n) amortized; a range is counted half by half as it doubles,
    // so counting costs the components of the range taken. Tradeoff: with more than
    // `1.6^62` (about 4.5 * 10^12) components the range of all ranks is taken whatever it
    // holds, and the bound no longer holds. Test
    // `product::tests::ranks_given_in_one_place_scale`.
    // Method chosen (PERF-pk-one-sided, against its plan row): the row named Dietz and
    // Sleator ("Two algorithms for maintaining order in a list", STOC 1987), whose two-level
    // list ranks O(1) amortized components again for each rank given, so each costs
    // O(log n) here with `order` a B-tree. This is the one-level list of Bender et al., a
    // simplification of the first of those algorithms, which ranks O(log n) amortized
    // components again: O(log² n) amortized in all, one factor of log n more, for one level
    // and no tag lists to keep. Measured: about 1.24 log₂ n components ranked again for each
    // rank given, 8,000 to 64,000 components. The two-level list is the repair should ranks
    // given dominate a profile.
    fn rank_after(&mut self, c: u64, after: Option<i64>) -> usize {
        let a = after.unwrap_or(-1);
        let b = self.order.range(a + 1..).next().map_or(RANKS, |(&r, _)| r);
        if b - a >= 2 {
            // Complexity tradeoff: naive version, the middle rank at an end too, so ranks
            // given one after another after the last halve the ranks left each time and run
            // out after 61, and from then on each such rank ranks a range again: in a run of
            // `put_in` the components made last were ranked again O(log n) times each,
            // O(log² n) a component, where below 61 components none was, so `rank_after`
            // grew 62 times from 32 to 256 tests of the chain raise in reverse (`xst::s4`).
            // Used: at an end with no rank beyond it, a step of `min(gap / 2, END_STEP)` from
            // the rank there, O(log n) for the one insert into `order`; 2^29 ranks in a row
            // fit at one end before a range is ranked again, and ranks put between two of
            // them still halve 32 times. COMPLEXITY.md row ST-chain-raise-reverse-log; test
            // `product::tests::ranks_given_one_after_another_at_an_end_rank_no_other_again`.
            let r = match (after, b) {
                (Some(_), RANKS) => a + ((b - a) / 2).min(END_STEP),
                (None, b) if b < RANKS => b - ((b - a) / 2).min(END_STEP),
                _ => a + (b - a) / 2,
            };
            self.set_rank(c, r);
            return 0;
        }
        // The smallest range of `2^i` ranks around `at` sparse enough, counted half by half.
        let at = a.max(0);
        let mut base = at;
        let mut held = usize::from(self.order.contains_key(&at));
        let mut level = 0;
        while level < 62 {
            level += 1;
            let half = 1i64 << (level - 1);
            let wider = at & !((half << 1) - 1);
            let other = if wider == base {
                base + half..base + 2 * half
            } else {
                wider..base
            };
            held += self.order.range(other).count();
            base = wider;
            if (held + 1) as f64 <= 1.6f64.powi(level) {
                break;
            }
        }
        let size = 1i64 << level;
        let mut range: Vec<(i64, u64)> = self
            .order
            .range(base..base + size)
            .map(|(&r, &d)| (r, d))
            .collect();
        let place = range.partition_point(|&(r, _)| r <= a);
        range.insert(place, (RANKS, c));
        for &(r, _) in &range {
            self.order.remove(&r);
        }
        let step = size / range.len() as i64;
        for (k, &(_, d)) in range.iter().enumerate() {
            self.set_rank(d, base + k as i64 * step);
        }
        range.len() - 1
    }
}

/// The ranks a component of a [`Potential`] may take: `0..RANKS`.
const RANKS: i64 = 1 << 62;

/// The step between ranks given one after another at an end of a [`Potential`]'s order
/// ([`Potential::rank_after`]).
const END_STEP: i64 = 1 << 32;

/// A strongly connected component of the edges of a [`Potential`], or several merged.
#[derive(Clone)]
struct Component {
    /// Its place in the order of the components.
    rank: i64,
    /// Its names.
    names: imbl::OrdSet<Arc<str>>,
    /// Its names at an edge to or from another component, and maybe names no longer at one,
    /// which a search that reads their edges drops ([`reorder`]): a search of the order then
    /// reads the edges of these alone, not of every name of a large component.
    ends: imbl::OrdSet<Arc<str>>,
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

/// An edge between two components of a [`Potential`]: its tail, its head and its value.
type CompEdge = (Arc<str>, Arc<str>, (Int, i64));

/// A name in the queue of [`Scope::bound_pass`], by the rank of its component, then its label
/// less its potential.
type Queued = Reverse<((i64, Int), Arc<str>)>;

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
    // Complexity tradeoff: naive version, the conjuncts mentioning `name` are read and those
    // of blocks apart from the forest skipped, O(d log n) for `d` conjuncts, so a hub of k
    // stars, each a block apart, cost O(k log n) per projection by shortest paths at each test
    // on it, O(k² log n) over k tests (13 to 30 s for 1024 tests in a row on the hubs of 5000
    // stars, against 0.28 s used). Used: the forest's conjuncts at `name` alone
    // (`Blocks::in_forest`), O(e log n) for its `e` conjuncts in the forest, kept at O(log n)
    // per name each time a conjunct moves into or out of the forest. Test
    // `l01_39_reduced_product::scaling::tests_on_the_hubs_of_many_stars_in_an_eager_scope_scale`;
    // COMPLEXITY.md row C49.
    for g in blocks.in_forest(name) {
        if !blocks.of(g).is_some_and(|b| blocks.tree(b) == t) {
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
/// tree `t` of the forest ([`Potential`]). A name `pot` lacks takes a value and a component of
/// its own from an edge only when every edge at it is among `added`, ranked before the
/// components of its edge's other end when it is the edge's tail and after them when it is
/// its head. An edge between components ranked in its direction needs nothing; one against
/// that order reorders the components or merges those on a cycle it closes ([`reorder`]); one
/// within a component is put in by a search of that component alone. `Ok(Some(u))` when an
/// edge closes a cycle of negative weight, and `Err` when the search reads a name `pot` lacks,
/// an edge of negative reduced weight, an edge against the order, or a cycle negative only
/// with the gaps; `pot` is then to be dropped.
fn put_in(
    relation: &Conjuncts,
    t: BlockId,
    added: &BTreeSet<Arc<Formula>>,
    pending: &[(Arc<Formula>, bool, Edge)],
    pot: &mut Potential,
) -> Result<Option<Arc<str>>, Fall> {
    // A name the potential lacks may take a value from an edge added only when every edge
    // at it was added: those are put in after.
    let new_name = |n: &Arc<str>| -> Result<Vec<(Arc<Formula>, bool, Edge)>, Fall> {
        let edges = tree_edges(relation, t, n);
        let all_added = edges
            .iter()
            .all(|(g, _, e)| e.from.is_none() || e.to.is_none() || added.contains(g));
        if all_added {
            Ok(edges)
        } else {
            Err(Fall::Potential)
        }
    };
    // A new name `n` that takes its value from an edge from or to component `c` joins `c`
    // when another of its edges, to be put in after, goes back to `c`, for the two close a
    // cycle; it takes a component of its own otherwise.
    // Complexity tradeoff: naive version, a component of its own, which the edge back then
    // merges into `c` after a search of the order that reads the edges of the ends of `c`,
    // O(d) for a hub of `d` edges in `c`, O(d²) for a hub of `d` equalities each to a new name
    // (`l01_39_reduced_product::scaling::a_join_keeps_the_equalities_of_its_sides_and_scales`).
    // Used: the edges of `n`, read already, are looked at for one back to `c`, O(e log n) for
    // its `e` edges.
    let place = |pot: &mut Potential,
                 n: &Arc<str>,
                 at: (Int, i64),
                 c: u64,
                 head: bool,
                 edges: &[(Arc<Formula>, bool, Edge)]| {
        let back = edges.iter().any(|(_, _, e)| {
            let (near, far) = if head {
                (&e.from, &e.to)
            } else {
                (&e.to, &e.from)
            };
            near.as_ref() == Some(n) && far.as_ref().is_some_and(|f| pot.comp.get(f) == Some(&c))
        });
        if back {
            pot.enter(n, at, c);
        } else {
            pot.fresh(n, at, !head);
        }
    };
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
        // Each round puts the edge in, or merges the components on a cycle it closes, or finds
        // a cycle of weight 0 through it, whose edges are then tied; the edge is then put in
        // again.
        'round: loop {
            let w = pair_weight(&pot.tied, &pot.gap, g, *back, e);
            let gamma = match (pot.at.get(u).cloned(), pot.at.get(v).cloned()) {
                (None, None) => {
                    new_name(u)?;
                    let edges = new_name(v)?;
                    pot.fresh(u, zero.clone(), true);
                    let c = pot.comp_of(u)?;
                    place(pot, v, w, c, true, &edges);
                    break 'round;
                }
                (Some(pu), None) => {
                    let edges = new_name(v)?;
                    let c = pot.comp_of(u)?;
                    place(pot, v, pair_plus(&pu, &w), c, true, &edges);
                    break 'round;
                }
                (None, Some(pv)) => {
                    let edges = new_name(u)?;
                    let c = pot.comp_of(v)?;
                    place(pot, u, pair_minus(&pv, &w), c, false, &edges);
                    break 'round;
                }
                (Some(pu), Some(pv)) => pair_minus(&pair_plus(&pu, &w), &pv),
            };
            let (cu, cv) = (pot.comp_of(u)?, pot.comp_of(v)?);
            if cu != cv {
                if pot.rank(cu) < pot.rank(cv) || !reorder(relation, t, &waiting, pot, cu, cv)? {
                    break 'round;
                }
                continue 'round;
            }
            if gamma >= zero {
                break 'round;
            }
            // Each name of the component whose potential falls falls by the least reduced
            // distance from `v` below zero; the new values are kept apart until the search
            // ends, so that the old ones check the edges read. Each name reached keeps the
            // edge it was last reached by, so that a cycle found can be followed back. An edge
            // to another component is only checked to go to a higher rank: every cycle through
            // the new edge lies in its component.
            let mut fall: BTreeMap<Arc<str>, (Int, i64)> =
                BTreeMap::from([(v.clone(), gamma.clone())]);
            let mut via: BTreeMap<Arc<str>, (Arc<str>, Arc<Formula>, bool)> = BTreeMap::new();
            let mut heap = BinaryHeap::from([Reverse((gamma, v.clone()))]);
            let mut new: BTreeMap<Arc<str>, (Int, i64)> = BTreeMap::new();
            while let Some(Reverse((gs, s))) = heap.pop() {
                if new.contains_key(&s) || fall.get(&s) != Some(&gs) {
                    continue;
                }
                let ps = pot.at.get(&s).ok_or(Fall::Potential)?;
                let to_s = pair_plus(ps, &gs);
                for (h, hb, f) in tree_edges(relation, t, &s) {
                    let (Some(from), Some(x)) = (&f.from, &f.to) else {
                        continue;
                    };
                    if *from != s || new.contains_key(x) || waiting.contains(&(h.clone(), hb)) {
                        continue;
                    }
                    let cx = pot.comp_of(x)?;
                    if cx != cu {
                        if pot.rank(cx) < pot.rank(cu) {
                            return Err(Fall::Potential);
                        }
                        continue;
                    }
                    let px = pot.at.get(x).ok_or(Fall::Potential)?;
                    let fw = pair_weight(&pot.tied, &pot.gap, &h, hb, &f);
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
                            let mut weight = &gx.0 + &pot.gap_of(u);
                            let mut at = s.clone();
                            weight = &weight + &pot.gap_of(&at);
                            while let Some((before, _, _)) = via.get(&at) {
                                at = before.clone();
                                weight = &weight + &pot.gap_of(&at);
                            }
                            return if weight < Int::ZERO {
                                Ok(Some(u.clone()))
                            } else {
                                Err(Fall::Potential)
                            };
                        }
                        // A cycle of weight 0: the edge, the one into `u`, and those
                        // back to `v`.
                        pot.tied.insert((g.clone(), *back));
                        pot.tied.insert((h, hb));
                        let mut at = s.clone();
                        while let Some((before, k, kb)) = via.get(&at) {
                            pot.tied.insert((k.clone(), *kb));
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
                pot.at.insert(s, ps);
            }
            break 'round;
        }
        pot.link(u, v);
    }
    Ok(None)
}

/// Restores the order of the components of the potential `pot` of tree `t` of the forest
/// after an edge from component `cu` to component `cv`, ranked before it, was put in, the
/// edges `waiting` not yet (Pearce and Kelly, one side): a search forward from `cv` and one
/// backward from `cu`, both within the components ranked from `cv` to `cu`, run in step, one
/// conjunct each in turn, and the first to finish decides. When the forward one finishes, the
/// components it found, `cv` among them, move in their order to just after `cu`: each edge
/// out of them goes to one of them or to a component ranked after `cu`, so every edge goes up
/// the order again. When the backward one finishes, those it found move likewise to just
/// before `cv`. When the search found the end it goes towards, the edge closes a cycle: the
/// components it found that reach that end lie on it ([`on_cycle`]), and are merged into one
/// ([`merge`]) that takes the rank of that end, the others moving past it as above; whether
/// there were any, so that the edge is then put in within the merged one. The names the
/// search reads at no edge to another component leave the components' ends. `Err` when a
/// search reads a name the potential lacks or an edge against the order.
// Complexity tradeoff: naive version, both searches to the end, as Pearce and Kelly, the
// components then taking the ranks they held: O(m log n) for the `m` edges at the ends of the
// components ranked between the edge's ends that either search reaches, so a chain whose
// every edge is put in against the order, one search reaching one component and the other
// all `i` before it, read `i` components for the `i`th edge, O(n²) for `n` edges (1,766,
// 5,204 and 18,598 components read at n = 64, 128 and 256, item PERF-pk-one-sided). Used:
// the searches in step stop when either ends, O(m log n) for the `m` edges at the ends of the
// components the one that ends first reaches (the other reads at most one conjunct more), and
// the components found move to new ranks between two neighbors, which an order-maintenance
// list gives in O(log² n) amortized each ([`Potential::rank_after`]). Tradeoff: the ranks
// are no longer reused, so a move costs the relabeling of a range now and then. Tests
// `l01_39_reduced_product::linked::a_chain_put_in_against_the_order_reads_only_what_it_moves`
// and the tests of [`Potential`]; COMPLEXITY.md S25b.
fn reorder(
    relation: &Conjuncts,
    t: BlockId,
    waiting: &BTreeSet<(Arc<Formula>, bool)>,
    pot: &mut Potential,
    cu: u64,
    cv: u64,
) -> Result<bool, Fall> {
    let window = (pot.rank(cv), pot.rank(cu));
    let mut idle: Vec<Arc<str>> = Vec::new();
    let (forward, found, links) = {
        let mut ahead = Search::new(relation, t, waiting, pot, window, cv, true);
        let mut behind = Search::new(relation, t, waiting, pot, window, cu, false);
        let done = loop {
            if ahead.step(&mut idle)? {
                break ahead;
            }
            if behind.step(&mut idle)? {
                break behind;
            }
        };
        (done.forward, done.seen, done.links)
    };
    // The end the search went towards, which the components found move past.
    let far = if forward { cu } else { cv };
    let mut moved: Vec<u64> = found.iter().copied().collect();
    let merged = found.contains(&far);
    let anchor = if merged {
        let cycle = on_cycle(links, far);
        moved.retain(|c| !cycle.contains(c));
        let rank = pot.rank(far);
        let keep = merge(relation, t, waiting, pot, &cycle);
        pot.rerank(keep, rank);
        keep
    } else {
        far
    };
    moved.sort_unstable_by_key(|&c| pot.rank(c));
    for &c in &moved {
        pot.unrank(c);
    }
    if forward {
        let mut at = pot.rank(anchor);
        for c in moved {
            pot.rank_after(c, Some(at));
            at = pot.rank(c);
        }
    } else {
        for c in moved {
            let before = pot
                .order
                .range(..pot.rank(anchor))
                .next_back()
                .map(|(&r, _)| r);
            pot.rank_after(c, before);
        }
    }
    drop_idle(pot, idle);
    Ok(merged)
}

/// The components of a search of [`reorder`] that lie on a cycle with the edge just put in:
/// those found that reach `far`, the end the search went towards, along the links it followed,
/// each the component found and the one it was found from. In O(k log k) for `k` links.
fn on_cycle(links: Vec<(u64, u64)>, far: u64) -> BTreeSet<u64> {
    let mut from: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for (d, c) in links {
        from.entry(d).or_default().push(c);
    }
    let mut on = BTreeSet::from([far]);
    let mut stack = vec![far];
    while let Some(d) = stack.pop() {
        for &c in from.get(&d).into_iter().flatten() {
            if on.insert(c) {
                stack.push(c);
            }
        }
    }
    on
}

/// Takes the names `idle`, found at no edge to another component, out of their components'
/// ends ([`Component::ends`]).
fn drop_idle(pot: &mut Potential, idle: Vec<Arc<str>>) {
    for x in idle {
        if let Some(c) = pot.comp.get(&x).copied()
            && let Some(p) = pot.parts.get_mut(&c)
        {
            p.ends.remove(&x);
        }
    }
}

/// A search of [`reorder`] in the potential `pot` of tree `t` of the forest, one conjunct at a
/// step: the components ranked within `window`, both ends included, that its start reaches
/// along the edges, or against them when not `forward`, the edges `waiting` and the edge just
/// put in, against the order, left out. Only the edges at each component's ends are read
/// ([`Component`]); the component at the far end of the window is not searched from, for no
/// edge goes on from it within the window.
struct Search<'a> {
    relation: &'a Conjuncts,
    t: BlockId,
    waiting: &'a BTreeSet<(Arc<Formula>, bool)>,
    pot: &'a Potential,
    window: (i64, i64),
    forward: bool,
    /// The components found.
    seen: BTreeSet<u64>,
    /// The components found and not yet read.
    stack: Vec<u64>,
    /// Each edge followed: the component found and the one it was found from.
    links: Vec<(u64, u64)>,
    /// The component being read and its ends not yet read.
    reading: Option<(
        u64,
        imbl::ordset::Iter<'a, Arc<str>, imbl::shared_ptr::DefaultSharedPtr>,
    )>,
    /// The end being read, its conjuncts not yet read, and whether one went to another
    /// component.
    end: Option<(&'a Arc<str>, ForestAt<'a>, bool)>,
}

/// The conjuncts of the forest at a name (`Conjuncts::in_forest`).
type ForestAt<'a> = Box<dyn Iterator<Item = &'a Arc<Formula>> + 'a>;

impl<'a> Search<'a> {
    fn new(
        relation: &'a Conjuncts,
        t: BlockId,
        waiting: &'a BTreeSet<(Arc<Formula>, bool)>,
        pot: &'a Potential,
        window: (i64, i64),
        start: u64,
        forward: bool,
    ) -> Search<'a> {
        Search {
            relation,
            t,
            waiting,
            pot,
            window,
            forward,
            seen: BTreeSet::from([start]),
            stack: vec![start],
            links: Vec::new(),
            reading: None,
            end: None,
        }
    }

    /// Takes the search one step on: a component, an end of it or a conjunct at that end
    /// read, an end with no edge to another component added to `idle`. `Ok(true)` once the
    /// search has ended. In O(log n) and O(1) amortized allocations.
    fn step(&mut self, idle: &mut Vec<Arc<str>>) -> Result<bool, Fall> {
        let pot = self.pot;
        let Some((c, ends)) = &mut self.reading else {
            let Some(c) = self.stack.pop() else {
                return Ok(true);
            };
            // No edge goes on within the window from the component at its far end, which may
            // be a large one with a hub: it is not read.
            let far = if self.forward {
                self.window.1
            } else {
                self.window.0
            };
            if pot.rank(c) != far {
                self.reading = Some((c, pot.parts[&c].ends.iter()));
            }
            return Ok(false);
        };
        let c = *c;
        let Some((x, conjuncts, linked)) = &mut self.end else {
            match ends.next() {
                Some(x) => {
                    self.end = Some((x, Box::new(self.relation.blocks().in_forest(x)), false))
                }
                None => self.reading = None,
            }
            return Ok(false);
        };
        let x: &Arc<str> = x;
        let Some(g) = conjuncts.next() else {
            if !*linked {
                idle.push(x.clone());
            }
            self.end = None;
            return Ok(false);
        };
        let blocks = self.relation.blocks();
        if !blocks.of(g).is_some_and(|b| blocks.tree(b) == self.t) {
            return Ok(false);
        }
        let Some((e, back)) = conjuncts::edges(g) else {
            return Ok(false);
        };
        let rc = pot.rank(c);
        let (lo, hi) = self.window;
        for (e, back) in std::iter::once((e, false)).chain(back.map(|e| (e, true))) {
            let (Some(a), Some(b)) = (&e.from, &e.to) else {
                continue;
            };
            let other = if a == x { b } else { a };
            *linked |= pot.comp.get(other) != Some(&c);
            let (near, far) = if self.forward { (a, b) } else { (b, a) };
            if near != x || self.waiting.contains(&(g.clone(), back)) {
                continue;
            }
            let d = pot.comp_of(far)?;
            let rd = pot.rank(d);
            if d == c || !(lo..=hi).contains(&rd) {
                continue;
            }
            // Within the window an edge goes on in the search's direction, but for the edge
            // just put in, from the window's last component to its first.
            if (rd > rc) != self.forward {
                if (rc, rd) == if self.forward { (hi, lo) } else { (lo, hi) } {
                    continue;
                }
                return Err(Fall::Potential);
            }
            self.links.push((d, c));
            if self.seen.insert(d) {
                self.stack.push(d);
            }
        }
        Ok(false)
    }
}

/// Merges the components `cycle` of the potential `pot` of tree `t` of the forest, each on a
/// cycle with an edge just put in, into the largest of them, which it returns. Each is first
/// given a shift, in the order of their ranks, the least reduced weight below zero of the
/// edges into it from those before with their shifts, the edges `waiting` left out: every
/// edge between them but the new one goes up the order, so the potential, each component
/// moved by its shift, holds at each of them. The shifts less the largest one's are applied,
/// so that its names keep their values. In O(m log n) for the `m` edges at the ends of all
/// but the largest component and their names, of `n` names.
// Complexity tradeoff: the names of the smaller components move into the largest and take
// the shifts, and the edges between the components are read at the ends of the smaller ones
// alone, so a name is read and moved only into a component at least twice the size of its
// own, O(log n) times in all; naive version, all into the first and each shifted, O(n) a
// merge, and the ends of the largest read at each merge, O(d) for a hub of `d` edges in it,
// O(n²) for a chain of `n` equalities, each closing a cycle with the component of those
// before (`l01_39_reduced_product::scaling::a_join_keeps_the_equalities_of_its_sides_and_scales`).
fn merge(
    relation: &Conjuncts,
    t: BlockId,
    waiting: &BTreeSet<(Arc<Formula>, bool)>,
    pot: &mut Potential,
    cycle: &BTreeSet<u64>,
) -> u64 {
    let mut order: Vec<u64> = cycle.iter().copied().collect();
    order.sort_unstable_by_key(|&c| pot.rank(c));
    let keep = *order
        .iter()
        .max_by_key(|&&c| pot.parts[&c].names.len())
        .expect("a cycle has a component");
    // The edges between the components, each with its tail, its head and its weight, by the
    // component of its head; each has an end outside the largest, so only the ends of the
    // others are read, each edge once, from its head unless that is in the largest.
    let mut into: BTreeMap<u64, Vec<CompEdge>> = BTreeMap::new();
    for &c in &order {
        if c == keep {
            continue;
        }
        for x in &pot.parts[&c].ends {
            for (g, back, e) in tree_edges(relation, t, x) {
                let (Some(a), Some(b)) = (&e.from, &e.to) else {
                    continue;
                };
                let (Some(&ca), Some(&cb)) = (pot.comp.get(a), pot.comp.get(b)) else {
                    continue;
                };
                if ca == cb
                    || !(b == x || cb == keep)
                    || !cycle.contains(&ca)
                    || !cycle.contains(&cb)
                    || waiting.contains(&(g.clone(), back))
                {
                    continue;
                }
                let w = pair_weight(&pot.tied, &pot.gap, &g, back, &e);
                into.entry(cb).or_default().push((a.clone(), b.clone(), w));
            }
        }
    }
    let zero = (Int::ZERO, 0i64);
    let mut shift: BTreeMap<u64, (Int, i64)> = BTreeMap::new();
    for &c in &order {
        let mut by = zero.clone();
        for (a, b, w) in into.get(&c).into_iter().flatten() {
            let (Some(sa), Some(pa), Some(pb)) =
                (shift.get(&pot.comp[a]), pot.at.get(a), pot.at.get(b))
            else {
                continue;
            };
            let reduced = pair_minus(&pair_plus(&pair_plus(pa, sa), w), pb);
            if reduced < by {
                by = reduced;
            }
        }
        shift.insert(c, by);
    }
    let base = shift[&keep].clone();
    for c in order {
        if c == keep {
            continue;
        }
        let Some(part) = pot.parts.remove(&c) else {
            continue;
        };
        pot.order.remove(&part.rank);
        let by = pair_minus(&shift[&c], &base);
        for x in &part.names {
            if by != zero
                && let Some(p) = pot.at.get_mut(x)
            {
                *p = pair_plus(p, &by);
            }
            pot.comp.insert(x.clone(), keep);
        }
        if let Some(p) = pot.parts.get_mut(&keep) {
            p.names.extend(part.names);
            p.ends.extend(part.ends);
        }
    }
    keep
}

/// The intervals and classes of a part's names when it was last projected, shared, so that a
/// copy of an entry of [`Scope::projected`], as a path copy of the persistent map makes for
/// each entry of a node it changes, costs a reference count and not the names (item
/// PERF-partkey-arc).
// Complexity tradeoff: a `Vec` here was copied whole with each entry a path copy of the map
// copies, O(m) for a part of m names, so k tests beside a part of k names cost O(k^2) bytes;
// shared, the copy is O(1), and the slice is built once when the part is projected. See
// COMPLEXITY.md C41.
pub type Projected = Arc<[(Arc<str>, IntervalSet, Congruence)]>;

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
/// change until the conjunct left (item ST-projected-stale). The conjunct is shared with the
/// relation that holds it, so that a copy of a key, as a path copy of [`Scope::projected`] or
/// `Seen::owners` makes for each key of a node it changes, costs a reference count and not
/// the constraint's terms (item PERF-partkey-arc). Keys are compared by the formulas they
/// hold, as before.
// Complexity tradeoff: a `Formula` held by value was cloned with each key a path copy copies,
// O(t) for a constraint of t terms (its `Lin` is a `BTreeMap`); behind an `Arc` the copy is
// O(1). Comparing two keys still reads the formulas, O(t) at worst, as before: an id would
// make it O(1) but give an order that differs from the formulas' and so other answers.
// COMPLEXITY.md C41.
pub type PartKey = (Arc<Formula>, Option<Arc<str>>);

/// What a part of the relation was projected with: the equalities among the constraints it is
/// projected with, sorted, and the constraints among them on the terms the part's conjunct
/// compares, as `x - y` in `x - y >= 5 || y - x >= 5` (the box of its terms), or, for the part
/// of the constraints alone, their conjunction. A part is projected again when an equality,
/// or a constraint on one of its terms, joins or leaves them, as `-2 <= x - y <= 2` after the
/// disjunction above, which leaves no value. The constraints also hold each group of linked
/// constraints (`linked`) that holds two variables of the conjunct or more: `n + m <= 14`
/// bounds the points of `m >= 10 || n <= -9` though it is on neither of its terms (item
/// LAZY-hub-coarse, where `n` kept `10` for `4`). A group that holds one variable of the
/// conjunct reaches it only through that variable's interval, which the constraints' own part
/// gives, so a constraint on other names alone does not make a conjunct's part due, and a new
/// constraint costs the parts that hold two variables of its group and not the block's (the walk
/// `v_i + w <= 0 || v_(i+1) - w >= 1` through the shared name `w`). The
/// constraints are shared, as the key is ([`PartKey`]).
// Complexity tradeoff: naive version, `PartWith` materialized a fresh `Vec<Con>` sorted,
// deduped, and wrapped in `Arc<Formula>` at every `Split::with` call, O(m log m) per part and
// O(k^2 log k) across k reframes (`36.4M` instructions in `Split::with` and `7.5M` in
// `Formula::eq` on `persist` at k = 16). Used: `WithCons` keeps a persistent `imbl::OrdSet<Con>`
// per variable-connected group and unions only the groups and term buckets a part reads, sharing
// unchanged B-tree nodes in O(1) and comparing via `ptr_eq` and `imbl::OrdSet::diff` in
// O(1 + d log m) for d differing constraints (Gemini seat's prototype: `split_with` 9560 -> 752, `with_cmp`
// 9032 -> 752 at k = 16). Reference: N. Sarnak and R. E. Tarjan, "Planar point location using
// persistent search trees", Communications of the ACM 29(7), 1986, pp. 669-679.
#[derive(Clone, Debug, Eq)]
pub enum WithCons {
    /// No constraints of the block outside the part.
    None,
    /// The constraints as one formula.
    Base(Arc<Formula>),
    /// The constraints as a persistent set, shared with the other parts of the group.
    Shared(imbl::OrdSet<Con>),
}

impl PartialEq for WithCons {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (WithCons::None, WithCons::None) => true,
            (WithCons::Base(a), WithCons::Base(b)) => Arc::ptr_eq(a, b) || a == b,
            (WithCons::Shared(a), WithCons::Shared(b)) => {
                a.ptr_eq(b) || (a.len() == b.len() && a.diff(b).next().is_none())
            }
            _ => false,
        }
    }
}

/// The equalities and the other constraints of a block that a part is projected with.
pub type PartWith = (Arc<[Con]>, WithCons);

/// Whether a conjunct `g` of a class ([`conjuncts::Class`]) keeps the projection onto its leaf
/// exact ([`Scope::core_leaf_bound`]): a constraint, the negation of a bound, or a conjunct
/// that does not mention the leaf.
fn leaf_literal(g: &Formula) -> bool {
    match g {
        Formula::Con(_) => true,
        Formula::Not(n) => matches!(&**n, Formula::Con(c) if c.rel == Rel::Ge),
        _ => !conjuncts::names(g).iter().any(|n| &**n == conjuncts::LEAF),
    }
}

/// The terms `g` compares ([`unsigned`]).
fn terms(g: &Formula) -> BTreeSet<BTreeMap<Atom, Int>> {
    g.cons().into_iter().map(unsigned).collect()
}

/// The term of `c` with its sign chosen so that its first coefficient is positive: one key for
/// `x - y >= 5` and `y - x >= 5`.
fn unsigned(c: &Con) -> BTreeMap<Atom, Int> {
    if c.lin.terms.values().next().is_some_and(Int::is_negative) {
        c.lin.terms.iter().map(|(a, k)| (a.clone(), -k)).collect()
    } else {
        c.lin.terms.clone()
    }
}

/// The variables the atoms of `atoms` are made of: each name and auxiliary variable, alone or
/// as a factor of a product.
fn factors_of<'a>(atoms: impl IntoIterator<Item = &'a Atom>) -> BTreeSet<Factor> {
    let mut out = BTreeSet::new();
    for a in atoms {
        match a {
            Atom::Sym(n) => {
                out.insert(Factor::Sym(n.clone()));
            }
            Atom::Aux(i) => {
                out.insert(Factor::Aux(*i));
            }
            Atom::Product(x, y) => {
                out.insert(x.clone());
                out.insert(y.clone());
            }
        }
    }
    out
}

/// The variables of `g` ([`factors_of`]).
fn factors(g: &Formula) -> BTreeSet<Factor> {
    factors_of(&g.atoms())
}

/// The constraints among `cons` in groups linked through shared variables (connected
/// components), each group with its variables and constraints, and the group of each
/// variable ([`Split::with`]).
// Complexity tradeoff: union-find by size with path halving over the v variables of the c
// constraints, O((c + v) log v) with the maps, as the rest of `Split::new`.
#[allow(clippy::type_complexity)]
fn linked(cons: &[&Arc<Formula>]) -> (Vec<(BTreeSet<Factor>, Vec<Con>)>, BTreeMap<Factor, usize>) {
    let mut at: BTreeMap<Factor, usize> = BTreeMap::new();
    let mut parent: Vec<usize> = Vec::new();
    let mut size: Vec<usize> = Vec::new();
    fn root(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    let mut seen: Vec<(&Con, usize)> = Vec::new();
    for g in cons {
        let Formula::Con(c) = &***g else {
            continue;
        };
        let mut first: Option<usize> = None;
        for x in factors_of(c.lin.terms.keys()) {
            let next = parent.len();
            let i = *at.entry(x).or_insert(next);
            if i == next {
                parent.push(i);
                size.push(1);
            }
            match first {
                None => first = Some(i),
                Some(f) => {
                    let (a, b) = (root(&mut parent, f), root(&mut parent, i));
                    if a != b {
                        let (big, small) = if size[a] >= size[b] { (a, b) } else { (b, a) };
                        parent[small] = big;
                        size[big] += size[small];
                    }
                }
            }
        }
        if let Some(f) = first {
            seen.push((c, f));
        }
    }
    let mut index: BTreeMap<usize, usize> = BTreeMap::new();
    let mut groups: Vec<(BTreeSet<Factor>, Vec<Con>)> = Vec::new();
    let mut group: BTreeMap<Factor, usize> = BTreeMap::new();
    for (x, i) in at {
        let r = root(&mut parent, i);
        let next = groups.len();
        let k = *index.entry(r).or_insert(next);
        if k == next {
            groups.push((BTreeSet::new(), Vec::new()));
        }
        groups[k].0.insert(x.clone());
        group.insert(x, k);
    }
    for (c, f) in seen {
        let r = root(&mut parent, f);
        groups[index[&r]].1.push(c.clone());
    }
    (groups, group)
}

/// What [`split`] makes each part of a set of conjuncts with: their constraints and the leaf.
/// A block keeps it ([`Block`]), so that a conjunct new to the block gets the part [`split`]
/// would give it without the others being split again.
// Complexity tradeoff: naive version, `Block::reframe` rebuilt `Split::new` from scratch over
// all r constraints (`11.1M` instructions across 124 reframes on `persist` at k = 16) and kept
// each group's constraints in a flat `Vec<Con>`, O(r log r) per reframe. Used: `Split` keeps
// persistent `imbl` maps for `eqs_set`, `on`, `adj`, `groups`, `group`, `base_buckets`, and
// `base_other`, so `Split::update` clones in O(1) and updates the c added or removed
// constraints in O(c log r); the joined `base` is still written again from the buckets and the
// other constraints, O(b + o) for b buckets and o others (at most r), and its names read again
// (row PERF-l139-persist-due). Component splits on edge removal walk `adj` with an explicit
// `visited` set. Proposed by Gemini in round 3 of XR-l139-family; measured with the rest of
// that round's merge (COMPLEXITY.md XR-l139-gemini). References: N. Sarnak and R. E. Tarjan, "Planar point
// location using persistent search trees", Communications of the ACM 29(7), 1986,
// pp. 669-679 (persistent search trees).
#[derive(Clone)]
struct Split {
    /// The equalities among the constraints, in order.
    eqs: Arc<[Con]>,
    eqs_set: imbl::OrdSet<Con>,
    /// The constraints on each term, either sign, which only the other conjuncts read.
    on: imbl::OrdMap<BTreeMap<Atom, Int>, imbl::OrdSet<Con>>,
    /// Variable adjacency counts from constraints, for incremental component maintenance.
    adj: imbl::OrdMap<Factor, BTreeMap<Factor, usize>>,
    /// The constraints linked through shared variables ([`factors`]): each group's variables
    /// and constraints, and the group of each variable ([`Split::with`]).
    groups: imbl::OrdMap<usize, (BTreeSet<Factor>, imbl::OrdSet<Con>)>,
    group: imbl::OrdMap<Factor, usize>,
    next_gid: usize,
    /// Common-intercept two-symbol `Rel::Ge` buckets `(x, y, a, constant)` for [`extreme_base`],
    /// and all other constraints in [`Formula`] order.
    base_buckets: imbl::OrdMap<(Atom, Atom, Int, Int), imbl::OrdSet<Con>>,
    base_other: imbl::OrdSet<Arc<Formula>>,
    eligible_count: usize,
    // Complexity tradeoff: built once per split, O(t) in the t terms of the constraints; the
    // part's key and what it is projected with take a reference to it, O(1), where they took
    // a deep copy each, O(t). COMPLEXITY.md C41.
    /// The constraints together, in the order they came, shared with the [`PartWith`] of their
    /// own part.
    base: Arc<Formula>,
    /// The symbols mentioned by `base`, sorted.
    base_syms: Arc<[Arc<str>]>,
    /// The least constraint, the key of the constraints' own part, shared with the relation.
    least: Option<Arc<Formula>>,
    /// The leaf, when the conjuncts are a star's.
    leaf: Option<Arc<str>>,
}

fn extreme_bucket_key(c: &Con) -> Option<(Atom, Atom, Int, Int)> {
    let mut terms = c.lin.terms.iter();
    match (c.rel, terms.next(), terms.next(), terms.next()) {
        (Rel::Ge, Some((x @ Atom::Sym(_), a)), Some((y @ Atom::Sym(_), _)), None) => {
            Some((x.clone(), y.clone(), a.clone(), c.lin.constant.clone()))
        }
        _ => None,
    }
}

/// Counts a constraint on the factors `fs`, sorted and distinct, into `adj` (`add`) or out of
/// it: each factor with itself, the number of constraints that mention it, and each factor and
/// the next in `fs`, both ways, the number of constraints that link them so. A count that
/// reaches 0 is removed. Returns whether a link between two distinct factors is gone, the only
/// change that can split a group. O(v log n) for v factors of the constraint.
// Complexity tradeoff (FAIL-l139-wide-asum-scaling): naive version, each pair of the factors
// counted, O(v^2 log n) per constraint: 2.4G instructions for one sum over k = 1024 names and
// 166G at 8192 (72 times). Used: the factors of each constraint linked as a path, each to the
// next, O(v log n). The groups read the links only for which factors are connected
// (`Split::remove_one`), and the path of a constraint connects its factors as all its pairs
// do, so every group is the same; a count of the path's links reaches 0 only when the links of
// the factors change, so a removal that leaves the components as they were may still search
// them, and one that splits a group always does. The search walks the paths, O(v + e) for e
// links, at most v - 1 for each constraint where the pairs were v(v - 1) / 2.
fn count_links(
    adj: &mut imbl::OrdMap<Factor, BTreeMap<Factor, usize>>,
    fs: &[Factor],
    add: bool,
) -> bool {
    let mut dropped = false;
    let mut count = |x: &Factor, y: &Factor| {
        if add {
            *adj.entry(x.clone())
                .or_default()
                .entry(y.clone())
                .or_insert(0) += 1;
        } else if let Some(links) = adj.get_mut(x)
            && let Some(k) = links.get_mut(y)
        {
            *k -= 1;
            if *k == 0 {
                links.remove(y);
                dropped |= x != y;
            }
        }
    };
    for (i, x) in fs.iter().enumerate() {
        count(x, x);
        if let Some(y) = fs.get(i + 1) {
            count(x, y);
            count(y, x);
        }
    }
    dropped
}

impl Split {
    /// The context of the constraints `cons`, in the star of leaf `leaf` if any.
    fn new(cons: &[&Arc<Formula>], leaf: Option<&Arc<str>>) -> Split {
        let mut eqs_set = imbl::OrdSet::new();
        let mut on: imbl::OrdMap<BTreeMap<Atom, Int>, imbl::OrdSet<Con>> = imbl::OrdMap::new();
        let mut adj: imbl::OrdMap<Factor, BTreeMap<Factor, usize>> = imbl::OrdMap::new();
        let mut base_buckets: imbl::OrdMap<(Atom, Atom, Int, Int), imbl::OrdSet<Con>> =
            imbl::OrdMap::new();
        let mut base_other: imbl::OrdSet<Arc<Formula>> = imbl::OrdSet::new();
        let mut eligible_count = 0usize;
        let mut seen_g: BTreeSet<&Arc<Formula>> = BTreeSet::new();
        let mut dedup_cons: Vec<&Arc<Formula>> = Vec::with_capacity(cons.len());
        for &g in cons {
            if !seen_g.insert(g) {
                continue;
            }
            dedup_cons.push(g);
            match &**g {
                Formula::Con(c) => {
                    if c.rel == Rel::Eq {
                        eqs_set.insert(c.clone());
                    }
                    on.entry(unsigned(c)).or_default().insert(c.clone());
                    let fs: Vec<Factor> = factors_of(c.lin.terms.keys()).into_iter().collect();
                    count_links(&mut adj, &fs, true);
                    if let Some(key) = extreme_bucket_key(c) {
                        let set = base_buckets.entry(key).or_default();
                        if set.insert(c.clone()).is_none() {
                            eligible_count += 1;
                        }
                    } else {
                        base_other.insert(g.clone());
                    }
                }
                _ => {
                    base_other.insert(g.clone());
                }
            }
        }
        let eqs: Vec<Con> = eqs_set.iter().cloned().collect();
        let (raw_groups, raw_group) = linked(&dedup_cons);
        let next_gid = raw_groups.len();
        let groups: imbl::OrdMap<usize, (BTreeSet<Factor>, imbl::OrdSet<Con>)> = raw_groups
            .into_iter()
            .enumerate()
            .map(|(i, (fs, cs))| (i, (fs, cs.into_iter().collect())))
            .collect();
        let group: imbl::OrdMap<Factor, usize> = raw_group.into_iter().collect();
        let base = Arc::new(extreme_base(&dedup_cons));
        let base_syms: Arc<[Arc<str>]> = syms(&base).into();
        Split {
            eqs: eqs.into(),
            eqs_set,
            on,
            adj,
            groups,
            group,
            next_gid,
            base_buckets,
            base_other,
            eligible_count,
            base,
            base_syms,
            least: dedup_cons.iter().min().map(|&c| c.clone()),
            leaf: leaf.cloned(),
        }
    }

    /// Incrementally updates `self` for `removed` and `added` constraints, reading `cons` only
    /// when fewer than two two-symbol `Rel::Ge` rows remain.
    fn update(
        &self,
        cons: &imbl::OrdSet<Arc<Formula>>,
        removed: &[Arc<Formula>],
        added: &[Arc<Formula>],
    ) -> Split {
        if removed.is_empty() && added.is_empty() {
            return self.clone();
        }
        let mut next = self.clone();
        let mut eqs_changed = false;
        for g in removed {
            next.remove_one(g, &mut eqs_changed);
        }
        for g in added {
            next.add_one(g, &mut eqs_changed);
        }
        if eqs_changed {
            let eqs: Vec<Con> = next.eqs_set.iter().cloned().collect();
            next.eqs = eqs.into();
        }
        next.least = cons.get_min().cloned();
        let base = Arc::new(next.rebuild_base(cons));
        next.base_syms = syms(&base).into();
        next.base = base;
        next
    }

    fn add_one(&mut self, g: &Arc<Formula>, eqs_changed: &mut bool) {
        let Formula::Con(c) = &**g else {
            self.base_other.insert(g.clone());
            return;
        };
        if c.rel == Rel::Eq && self.eqs_set.insert(c.clone()).is_none() {
            *eqs_changed = true;
        }
        self.on.entry(unsigned(c)).or_default().insert(c.clone());
        if let Some(key) = extreme_bucket_key(c) {
            let set = self.base_buckets.entry(key).or_default();
            if set.insert(c.clone()).is_none() {
                self.eligible_count += 1;
            }
        } else {
            self.base_other.insert(g.clone());
        }
        let fs: Vec<Factor> = factors_of(c.lin.terms.keys()).into_iter().collect();
        if fs.is_empty() {
            return;
        }
        count_links(&mut self.adj, &fs, true);
        let mut existing: BTreeSet<usize> = BTreeSet::new();
        let mut fresh: Vec<Factor> = Vec::new();
        for x in &fs {
            match self.group.get(x) {
                Some(&gid) => {
                    existing.insert(gid);
                }
                None => fresh.push(x.clone()),
            }
        }
        let target = if existing.is_empty() {
            let gid = self.next_gid;
            self.next_gid += 1;
            self.groups
                .insert(gid, (BTreeSet::new(), imbl::OrdSet::new()));
            gid
        } else {
            let best = *existing
                .iter()
                .max_by_key(|&&gid| self.groups[&gid].1.len())
                .unwrap();
            for &gid in &existing {
                if gid == best {
                    continue;
                }
                let (old_fs, old_cs) = self.groups.remove(&gid).unwrap();
                for x in &old_fs {
                    self.group.insert(x.clone(), best);
                }
                let dst = self.groups.get_mut(&best).unwrap();
                dst.0.extend(old_fs);
                dst.1 = dst.1.clone().union(old_cs);
            }
            best
        };
        for x in fresh {
            self.group.insert(x.clone(), target);
            self.groups.get_mut(&target).unwrap().0.insert(x);
        }
        self.groups.get_mut(&target).unwrap().1.insert(c.clone());
    }

    fn remove_one(&mut self, g: &Arc<Formula>, eqs_changed: &mut bool) {
        let Formula::Con(c) = &**g else {
            self.base_other.remove(g);
            return;
        };
        if c.rel == Rel::Eq && self.eqs_set.remove(c).is_some() {
            *eqs_changed = true;
        }
        let u_key = unsigned(c);
        if let Some(set) = self.on.get_mut(&u_key) {
            set.remove(c);
            if set.is_empty() {
                self.on.remove(&u_key);
            }
        }
        if let Some(key) = extreme_bucket_key(c) {
            let mut empty_bucket = false;
            if let Some(set) = self.base_buckets.get_mut(&key) {
                if set.remove(c).is_some() {
                    self.eligible_count -= 1;
                }
                empty_bucket = set.is_empty();
            }
            if empty_bucket {
                self.base_buckets.remove(&key);
            }
        } else {
            self.base_other.remove(g);
        }
        let fs: Vec<Factor> = factors_of(c.lin.terms.keys()).into_iter().collect();
        if fs.is_empty() {
            return;
        }
        let Some(&gid) = self.group.get(&fs[0]) else {
            return;
        };
        let edge_dropped = count_links(&mut self.adj, &fs, false);
        self.groups.get_mut(&gid).unwrap().1.remove(c);
        // A variable of `c` that no constraint left mentions leaves the group, O(v log n) for
        // the v variables of `c`, read from the counts `count_links` keeps, where reading every
        // constraint left in the group cost O(g) per constraint gone.
        for x in &fs {
            if self.adj.get(x).is_none_or(|m| !m.contains_key(x)) {
                self.groups.get_mut(&gid).unwrap().0.remove(x);
                self.group.remove(x);
                self.adj.remove(x);
            }
        }
        if self.groups[&gid].0.is_empty() {
            self.groups.remove(&gid);
            return;
        }
        if !edge_dropped {
            return;
        }
        // Check connectivity of the remaining variables in `gid` with an explicit `visited` set.
        // Complexity tradeoff: a search over the group, O(v + e) for its v variables and e
        // links ([`count_links`]), only when a link is gone; the families
        // add constraints to a group of fixed variables, so this does not run in their tests.
        // A fully dynamic connectivity structure (J. Holm, K. de Lichtenberg and M. Thorup,
        // "Poly-logarithmic deterministic fully-dynamic algorithms for connectivity", JACM
        // 48(4), 2001) answers in O(log^2 v) amortized, at a large constant; not needed yet.
        let rem_vars = self.groups[&gid].0.clone();
        let mut visited: BTreeSet<Factor> = BTreeSet::new();
        let mut comps: Vec<BTreeSet<Factor>> = Vec::new();
        for start in &rem_vars {
            if !visited.insert(start.clone()) {
                continue;
            }
            let mut comp = BTreeSet::new();
            comp.insert(start.clone());
            let mut stack = vec![start.clone()];
            while let Some(u) = stack.pop() {
                if let Some(nbrs) = self.adj.get(&u) {
                    for v in nbrs.keys() {
                        if rem_vars.contains(v) && visited.insert(v.clone()) {
                            comp.insert(v.clone());
                            stack.push(v.clone());
                        }
                    }
                }
            }
            comps.push(comp);
        }
        if comps.len() <= 1 {
            return;
        }
        let (_, old_cs) = self.groups.remove(&gid).unwrap();
        let mut new_gids: Vec<usize> = Vec::with_capacity(comps.len());
        for comp in comps {
            let ngid = self.next_gid;
            self.next_gid += 1;
            for x in &comp {
                self.group.insert(x.clone(), ngid);
            }
            self.groups.insert(ngid, (comp, imbl::OrdSet::new()));
            new_gids.push(ngid);
        }
        for rc in old_cs {
            if let Some(first_x) = factors_of(rc.lin.terms.keys()).into_iter().next()
                && let Some(&ngid) = self.group.get(&first_x)
            {
                self.groups.get_mut(&ngid).unwrap().1.insert(rc);
            }
        }
        for ngid in new_gids {
            if self.groups[&ngid].0.is_empty() {
                self.groups.remove(&ngid);
            }
        }
    }

    fn rebuild_base(&self, cons: &imbl::OrdSet<Arc<Formula>>) -> Formula {
        if self.eligible_count < 2 {
            return Formula::and(cons.iter().map(|g| (**g).clone()).collect());
        }
        let mut out: Vec<Formula> = self.base_other.iter().map(|g| (**g).clone()).collect();
        for (_, set) in &self.base_buckets {
            if let (Some(lo), Some(hi)) = (set.get_min(), set.get_max()) {
                if lo != hi {
                    out.push(Formula::Con(hi.clone()));
                }
                out.push(Formula::Con(lo.clone()));
            }
        }
        Formula::and(out)
    }

    /// The part of `g`, a conjunct that is not a constraint: `g` with the constraints, keyed by
    /// `g`, projected with the equalities and the constraints on the terms `g` compares.
    fn part(&self, g: &Arc<Formula>, groups: &Split) -> (PartKey, PartWith, Formula) {
        (
            (g.clone(), self.leaf.clone()),
            self.with(g, groups),
            self.formula(Some(&**g)),
        )
    }

    /// What the part of `g` is projected with ([`Split::part`]): the constraints on the terms
    /// `g` compares, and each group of linked constraints that holds two variables of `g` or
    /// more ([`Split::groups`]). A group that holds two of `g`'s variables relates them, as
    /// `n + m <= 14` relates `n` and `m` in `m >= 10 || n <= -9`, and so can narrow `g`'s
    /// projection while it moves no interval (`n` in -10..=4, where the box of `n + m` alone
    /// leaves -10..=10); a group that holds one of them reaches `g` only through that
    /// variable's interval, which the constraints' own part keeps, and a group that holds none
    /// does not reach it. Item LAZY-hub-coarse.
    // Complexity tradeoff: naive version, every constraint of the block in `with`, so that each
    // constraint added or gone made every part due, O(k) projections for k parts, O(k^2) for k
    // tests on a term no part compares (the walk through a shared name). Used: the groups that
    // hold two of `g`'s variables, found from the group of each, O(v log v) for v variables;
    // persistent `imbl::OrdSet<Con>` union shares group trees in O(1) when a single group holds
    // all constraints (`persist`), avoiding O(m log m) vector sort and dedup. COMPLEXITY.md C52.
    ///
    /// The groups are read from `groups`, the context as it was outside the cases of a test
    /// ([`Block::outer`]), which is `self` but within those cases.
    fn with(&self, g: &Formula, groups: &Split) -> PartWith {
        let mut held: BTreeMap<usize, usize> = BTreeMap::new();
        for x in factors(g) {
            if let Some(&i) = groups.group.get(&x) {
                *held.entry(i).or_insert(0) += 1;
            }
        }
        let mut shared: Option<imbl::OrdSet<Con>> = None;
        for (&i, &k) in &held {
            if k >= 2
                && let Some((_, set)) = groups.groups.get(&i)
                && !set.is_empty()
            {
                shared = Some(match shared {
                    None => set.clone(),
                    Some(acc) => acc.union(set.clone()),
                });
            }
        }
        for t in terms(g) {
            if let Some(on_set) = self.on.get(&t)
                && !on_set.is_empty()
            {
                shared = Some(match shared {
                    None => on_set.clone(),
                    Some(acc) => {
                        if acc.len() >= on_set.len() {
                            let mut a = acc;
                            for c in on_set {
                                a.insert(c.clone());
                            }
                            a
                        } else {
                            acc.union(on_set.clone())
                        }
                    }
                });
            }
        }
        let cons = match shared {
            Some(s) if !s.is_empty() => WithCons::Shared(s),
            _ => WithCons::None,
        };
        (self.eqs.clone(), cons)
    }

    /// The formula projected for the part of `g`, or for the constraints' own part when `g`
    /// is `None`.
    fn formula(&self, g: Option<&Formula>) -> Formula {
        match g {
            Some(g) => Formula::and(vec![g.clone(), (*self.base).clone()]),
            None => (*self.base).clone(),
        }
    }

    /// The constraints' own part, when there are any.
    fn constraints(&self) -> Option<(PartKey, PartWith, Formula)> {
        let least = self
            .least
            .clone()
            .filter(|_| *self.base != Formula::top())?;
        Some((
            (least, self.leaf.clone()),
            (self.eqs.clone(), WithCons::Base(self.base.clone())),
            (*self.base).clone(),
        ))
    }
}

/// Each of `conjuncts` that is not a constraint, with the constraints, and the constraints
/// alone when there are any; each part with its key and what it is projected with, in the
/// star of leaf `leaf` if any.
fn split<'a>(
    conjuncts: impl Iterator<Item = &'a Arc<Formula>>,
    leaf: Option<&Arc<str>>,
) -> Vec<(PartKey, PartWith, Formula)> {
    let (cons, others): (Vec<&Arc<Formula>>, Vec<&Arc<Formula>>) =
        conjuncts.partition(|g| matches!(&***g, Formula::Con(_)));
    let context = Split::new(&cons, leaf);
    let mut parts: Vec<(PartKey, PartWith, Formula)> = others
        .into_iter()
        .map(|g| context.part(g, &context))
        .collect();
    parts.extend(context.constraints());
    parts
}

/// When `g` is a non-empty disjunction of two-symbol `Rel::Ge` rows on the exact same pair of
/// symbols `(u, v)`, returns `(u, v)` (`u < v`).
fn pure_two_sym_pair(g: &Formula) -> Option<(Arc<str>, Arc<str>)> {
    let Formula::Or(arms) = g else {
        return None;
    };
    let mut pair: Option<(Arc<str>, Arc<str>)> = None;
    for arm in arms.iter() {
        let Formula::Con(c) = arm else {
            return None;
        };
        if c.rel != Rel::Ge || c.lin.terms.len() != 2 {
            return None;
        }
        let mut it = c.lin.terms.keys();
        let (Some(Atom::Sym(u)), Some(Atom::Sym(v)), None) = (it.next(), it.next(), it.next())
        else {
            return None;
        };
        match &pair {
            None => pair = Some((u.clone(), v.clone())),
            Some((pu, pv)) if pu == u && pv == v => {}
            Some(_) => return None,
        }
    }
    pair
}

/// Four-bit finiteness mask of the lower and upper interval bounds of `u` and `v` in `names`.
fn finiteness_mask(u: &str, v: &str, names: &imbl::OrdMap<Arc<str>, Product>) -> u8 {
    let mut mask = 0u8;
    for (shift, n) in [(0u8, u), (2u8, v)] {
        if let Some(p) = names.get(n)
            && let Some((lo, hi)) = p.ints().bounds()
        {
            if matches!(lo, End::Fin(_)) {
                mask |= 1 << shift;
            }
            if matches!(hi, End::Fin(_)) {
                mask |= 1 << (shift + 1);
            }
        }
    }
    mask
}

/// Canonical congruence class as observed by linear block projection, [`classed`], and [`gapped`]:
/// any unclassed product — whether `(modulus = 1, residue = 0)` or a singleton interval `[v, v]`
/// with `(modulus = 0, residue = v)` — maps to `(modulus = 1, residue = 0)`, while every classed
/// product preserves `p.cell.congruence.element` unchanged.
// Complexity tradeoff: naive version, `Block::update`, `Scope::reduce_with`, `Scope::project`,
// `Scope::snapshot`, and `join_refreshed` compared raw `p.cell.congruence.element`, so narrowing a
// binary variable `x in [0, 1]` to `1` caused a second form-only wake when reduction refined
// `(modulus = 1, residue = 0)` to `(modulus = 0, residue = 1)` without changing the set of
// integers (Gemini seat, round 3), doubling wake and idle checks across `3k` case arms.
// Used: canonicalize unclassed products via `framed_class` in O(1), matching propagator-event
// subsumption / idempotence in C. Schulte and P. J. Stuckey, "Efficient constraint propagation
// engines", ACM TOPLAS 31(1), Article 2, 2008 (`KeptTests::dead` still reads raw `congruence` directly).
fn framed_class(p: &Product) -> Congruence {
    if !classed(p) {
        Congruence::Class {
            modulus: Num::ONE,
            residue: Num::ZERO,
        }
    } else {
        p.cell.congruence.element.clone()
    }
}

fn same_framed(a: &Product, b: &Product) -> bool {
    a.ints() == b.ints() && framed_class(a) == framed_class(b)
}

fn same_framed_opt(a: Option<&Product>, b: Option<&Product>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => same_framed(x, y),
        (Some(x), None) | (None, Some(x)) => same_framed(x, &Product::top()),
    }
}

/// A part of a block ([`split`]): its key, what it is projected with, its conjunct (`None` for
/// the constraints' own part), and the names the formula projected mentions. The formula is
/// made from the conjunct and the block's constraints when the part is projected
/// ([`Block::formula`]), so that a constraint added or gone changes no part but those on its
/// term ([`Block::reframe`]).
#[derive(Clone)]
struct Part {
    key: PartKey,
    with: PartWith,
    of: Option<Arc<Formula>>,
    names: Vec<Arc<str>>,
    role: Role,
    /// Its entries in [`Block::bounds`] ([`bounds_at`]).
    bounds: Vec<(BoundsKey, Turn)>,
    /// Cached `(u, v, finiteness_mask)` for [`pure_two_sym_pair`] parts to skip invariant
    /// [`bounds_at`] recomputation in O(1) when `split.eqs` is empty.
    pure_two_sym: Option<(Arc<str>, Arc<str>, u8)>,
    /// Its conjunct's atoms and their ends ([`chain_shape`]), when it has that shape.
    chain: Option<Chain>,
}

/// One atom of a disjunction of rows, without its ends: a row `t + c >= 0`, kept as its
/// terms `t`, or two rows `F + b*y + c >= 0` and `F - b*y + c >= 0`, which together mean
/// `F + |b|*|y| + c >= 0`, kept as `F` and `y` (the shape of [`compact_abs`]).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum ChainAtom {
    Row(BTreeMap<Atom, Int>),
    Abs(BTreeMap<Atom, Int>, Atom),
}

/// A disjunction's atoms, sorted, and their ends in the same order: `c` for a row, `|b|`
/// and `c` for an absolute value ([`chain_shape`]).
type Chain = (Arc<Vec<ChainAtom>>, Vec<Int>);

/// The atoms and ends of `g` when `g` is a disjunction of rows `>= 0`, no two of its arms or
/// atoms alike; otherwise `None`. Two arms pair as an absolute value when they have the same
/// constant and their terms differ only in the sign of one coefficient.
///
/// Naive: try every later arm against each arm, O(r^2 t) for r arms of t terms. Used: the
/// arms sorted once by constant and terms, and for each arm and each of its terms the arm
/// with that sign flipped found by binary search, O(r t (t + log r)). A different pairing
/// of arms that could pair two ways only gives another exact form of the same disjunction,
/// so [`chain_below`] stays sound; `None` only leaves the part to [`Scope::idle`]. Read once
/// per part, as it is added.
fn chain_shape(g: &Formula) -> Option<Chain> {
    let Formula::Or(gs) = g else { return None };
    let mut rows = vec![];
    for a in &gs[..] {
        let Formula::Con(c) = a else { return None };
        if c.rel != Rel::Ge {
            return None;
        }
        rows.push(c);
    }
    fn key(c: &Con) -> (&Int, &BTreeMap<Atom, Int>) {
        (&c.lin.constant, &c.lin.terms)
    }
    let mut order: Vec<usize> = (0..rows.len()).collect();
    order.sort_by(|&i, &j| key(rows[i]).cmp(&key(rows[j])));
    if order.windows(2).any(|w| key(rows[w[0]]) == key(rows[w[1]])) {
        return None;
    }
    let mut used = vec![false; rows.len()];
    let mut atoms: Vec<(ChainAtom, Vec<Int>)> = vec![];
    for i in 0..rows.len() {
        if used[i] {
            continue;
        }
        used[i] = true;
        let c = &rows[i].lin;
        let pair = c.terms.iter().find_map(|(y, k)| {
            let mut f = c.terms.clone();
            f.insert(y.clone(), -k);
            let at = order.binary_search_by(|&j| key(rows[j]).cmp(&(&c.constant, &f)));
            let j = order[at.ok()?];
            (!used[j]).then(|| (j, y, k.abs()))
        });
        match pair {
            Some((j, y, k)) => {
                used[j] = true;
                let mut rest = c.terms.clone();
                rest.remove(y);
                atoms.push((ChainAtom::Abs(rest, y.clone()), vec![k, c.constant.clone()]));
            }
            None => atoms.push((ChainAtom::Row(c.terms.clone()), vec![c.constant.clone()])),
        }
    }
    atoms.sort_by(|a, b| a.0.cmp(&b.0));
    if atoms.windows(2).any(|w| w[0].0 == w[1].0) {
        return None;
    }
    let (keys, ends): (Vec<ChainAtom>, Vec<Vec<Int>>) = atoms.into_iter().unzip();
    Some((Arc::new(keys), ends.into_iter().flatten().collect()))
}

/// Whether ends `q` lie at or below ends `p` in every place, for two chains of one key:
/// then the disjunction of `q` implies that of `p` ([`Scope::idle_by_chain`]).
fn chain_below(q: &[Int], p: &[Int]) -> bool {
    q.len() == p.len() && q.iter().zip(p).all(|(a, b)| a <= b)
}

/// What reads a part's conjunct besides its own projection, found once as the part is added.
/// The shapes are disjoint: a threshold row's arms have one name each, an upper disjunction's
/// arms two names with negative coefficients, and a ray's arms the coefficient 1 on the first
/// name, which one arm of a threshold row lacks.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Role {
    /// The constraints' own part.
    Constraints,
    /// A conjunct no aggregate reads; while one is in the block no aggregate holds.
    Other,
    /// A two-name threshold row `x >= a || y <= b` ([`stair_row`]), read by
    /// [`Scope::cover_staircase`].
    Stair,
    /// A disjunction of `p*x + q*y <= c`, p and q positive ([`upper_disjunction`]), read by
    /// [`Scope::cover_staircase`] through [`UpperBounds`].
    Upper,
    /// A disjunction with an integer support x = d + j*y ([`ray_row`]), read by
    /// [`Block::ray_high`].
    Ray,
}

impl Role {
    fn of(g: Option<&Formula>) -> Role {
        match g {
            None => Role::Constraints,
            Some(g) if stair_row(g).is_some() => Role::Stair,
            Some(g) if upper_disjunction(g) => Role::Upper,
            Some(g) if ray_row(g).is_some() => Role::Ray,
            Some(_) => Role::Other,
        }
    }

    /// Whether the threshold aggregate stands for the part while it holds.
    fn stair(self) -> bool {
        matches!(self, Role::Stair | Role::Upper)
    }
}

/// The parts that mention a name, apart by the aggregate that stands for them: those of no
/// aggregate, the threshold rows and upper disjunctions, and the rays. Each part is in one set.
#[derive(Clone, Default)]
struct Users {
    plain: imbl::OrdSet<PartAt>,
    stair: imbl::OrdSet<PartAt>,
    ray: imbl::OrdSet<PartAt>,
}

impl Users {
    fn of_role(&mut self, role: Role) -> &mut imbl::OrdSet<PartAt> {
        match role {
            Role::Constraints | Role::Other => &mut self.plain,
            Role::Stair | Role::Upper => &mut self.stair,
            Role::Ray => &mut self.ray,
        }
    }

    fn is_empty(&self) -> bool {
        self.plain.is_empty() && self.stair.is_empty() && self.ray.is_empty()
    }

    /// The parts but those of the aggregates that hold, in order.
    // Complexity tradeoff: a map of users kept for each of the four ways the two aggregates
    // can hold made each part enter up to four maps per name; one set per aggregate and a
    // merge of at most three sorted sets reads the same parts in the same order, O(u) for u
    // parts, and skips the sets of the aggregates that hold without reading them.
    fn due(&self, stair: bool, ray: bool) -> impl Iterator<Item = &PartAt> {
        // A part has one role, so no part is in two of the sets and the merge gives each once.
        let mut heads = [
            Some(self.plain.iter()),
            (!stair).then(|| self.stair.iter()),
            (!ray).then(|| self.ray.iter()),
        ]
        .map(|set| set.map(|mut it| (it.next(), it)));
        std::iter::from_fn(move || {
            let (head, rest) = heads
                .iter_mut()
                .flatten()
                .filter(|(head, _)| head.is_some())
                .min_by(|a, b| a.0.cmp(&b.0))?;
            std::mem::replace(head, rest.next())
        })
    }
}

/// Where a part stands among its block's parts, in the order [`split`] gives them: the part of
/// each conjunct that is not a constraint, keyed `(false, conjunct)`, in the conjuncts' order,
/// then the constraints' own part, keyed `(true, least constraint)`.
type PartAt = (bool, Arc<Formula>);

/// The parts of a block under each chain key, each with its ends ([`Block::chains`]).
type ChainParts = imbl::OrdMap<Arc<Vec<ChainAtom>>, imbl::OrdSet<(Vec<Int>, PartAt)>>;

/// Top-level conjuncts of a relation projected together: a block of [`Conjuncts::blocks`],
/// with its conjuncts among its hubs when it is a star of two hubs or more
/// ([`Conjuncts::core`]). A scope keeps each block it projects ([`Seen::blocks`]) and brings it
/// up to date at the next projection from what changed since ([`Block::update`]), so that a
/// test costs the parts it adds or whose names it moves, not every part of the block.
#[derive(Clone)]
struct Block {
    /// The block's id when it was made or brought up to date.
    id: BlockId,
    /// Each part ([`PartAt`]).
    parts: imbl::OrdMap<PartAt, Arc<Part>>,
    /// The parts that mention each name, the leaf among them ([`Users`]).
    users: imbl::OrdMap<Arc<str>, Users>,
    /// The parts of each [`Role`] but the constraints' part.
    roles: imbl::OrdMap<Role, imbl::OrdSet<PartAt>>,
    /// The rays, grouped by their two names ([`RayGroup`]).
    rays: imbl::OrdMap<(Arc<str>, Arc<str>), RayGroup>,
    /// The rays' bound held ([`Block::ray_high`]) at the last update or projection; the rays
    /// were not projected one by one then.
    ray_managed: bool,
    /// One ray part carrying the demand to read the rays' bound again.
    ray_due: Option<PartAt>,
    /// What the upper disjunctions give in [`Scope::cover_staircase`] at the staircase and
    /// lower ends of its last call, taking in each upper disjunction as it enters.
    upper_bounds: Option<UpperBounds>,
    /// The least bound the constraints give over the rays of the one ray group
    /// ([`Block::ray_high`]), found at the first call after a ray or constraint leaves and
    /// taking in each ray or constraint as it enters.
    ray_least: OnceLock<RayLeast>,

    /// The threshold rows were solved together at the last keep. Their snapshot is
    /// `names_at`; no individual `Scope::projected` records are needed while this holds.
    stair_managed: bool,
    /// One part carrying the demand to solve the threshold rows again.
    stair_due: Option<PartAt>,
    /// The leaf, when the block is a star ([`Conjuncts::star`]).
    leaf: Option<Arc<str>>,
    /// Each of its conjuncts ([`Conjuncts::core`]), with the number of ways it is one: as a
    /// member, and as a free conjunct at each name of the members.
    core: imbl::OrdMap<Arc<Formula>, usize>,
    /// The conjuncts each of which shows that the core is no threshold-implication component
    /// while it stays ([`Block::unshaped`]).
    unshaped: imbl::OrdSet<Arc<Formula>>,
    /// The constraints among the conjuncts, and their context ([`Block::reframe`]).
    cons: imbl::OrdSet<Arc<Formula>>,
    split: Arc<Split>,
    /// The constraints as they were outside the cases of a test ([`Scope::in_case`]), and
    /// their context, from which the groups of each part's [`PartWith`] are read
    /// ([`Split::with`]). Within the cases of a test a constraint that joins a group makes no
    /// part due (`Block::reframe`); outside them these are `cons` and `split`.
    outer_cons: imbl::OrdSet<Arc<Formula>>,
    outer: Arc<Split>,
    /// The parts of the conjuncts that compare each term ([`unsigned`]), and the number of
    /// conjuncts with a part that mention each name. Each term is shared, so that a path copy
    /// of the map copies a reference count per key and not its terms (item
    /// PERF-block-terms-key).
    // Complexity tradeoff: a term held by value (a `BTreeMap` of its t names) was cloned with
    // each key a path copy of this persistent map copies, O(t) per key, up to 16 keys a node,
    // so k parts added beside a conjunct on a term of k names cost O(k^2); behind an `Arc` a
    // key is copied in O(1). A key is never changed once made, so an `Arc` suffices and a
    // persistent map of the term is not needed. Keys are compared by the terms they hold, as
    // before, so the order of the map is unchanged. COMPLEXITY.md C44.
    terms: imbl::OrdMap<Arc<BTreeMap<Atom, Int>>, imbl::OrdSet<PartAt>>,
    mentions: imbl::OrdMap<Arc<str>, usize>,
    /// The parts of the conjuncts that hold each variable ([`factors`]), so that a constraint
    /// added or gone finds the parts whose group it changes ([`Block::reframe`]).
    // Complexity tradeoff: naive version, each part kept under each pair of its s variables,
    // O(s^2 log k) to add, which a disjunction over the 2d names of a chain of accounts pays
    // at every level (36.4 times the bytes at 8 times the depth). Used: each part under each
    // of its variables, O(s log k). COMPLEXITY.md C52.
    vars: imbl::OrdMap<Factor, imbl::OrdSet<PartAt>>,
    /// The parts of each chain key ([`chain_shape`]), ordered by their ends, so that the
    /// first is the least ([`Scope::idle_by_chain`]).
    chains: ChainParts,
    /// The disjunctions in which a constraint on two names bounds an end of one of them in
    /// every arm ([`bounds_at`]), by the two names, the end and the side of it the constraint
    /// turns from that end, and by how far it may turn ([`Turn`]), so that a case's constraint
    /// finds them by a range of the map ([`Block::reframe`]).
    bounds: imbl::OrdMap<BoundsKey, imbl::OrdMap<Turn, imbl::OrdSet<PartAt>>>,
    /// Threshold parts, grouped by their lower and upper names.
    stairs: imbl::OrdMap<(Arc<str>, Arc<str>), Staircase>,
    /// The parts the two-name rule of [`Block::reframe`] made due at the last update, projected
    /// whatever their records say.
    fired: BTreeSet<PartAt>,
    /// The entries of [`Block::bounds`] the two-name rule of [`Block::reframe`] projected for
    /// at the last update, spent once the block is kept ([`Scope::spent`]).
    spends: Vec<BoundsKey>,
    /// The parts whose records were taken away or changed since the block was kept
    /// ([`Seen::drop_part`]), due at its next projection.
    forgot: imbl::OrdSet<PartAt>,
    /// The members, the number of members that mention each name, whether the block is apart
    /// ([`conjuncts::Blocks::is_apart`]), whether it takes the free conjuncts at its names, and
    /// those conjuncts at each name, as they were at the last projection.
    members: imbl::OrdSet<Arc<Formula>>,
    member_names: imbl::OrdMap<Arc<str>, usize>,
    apart: bool,
    wide: bool,
    free: imbl::OrdMap<Arc<str>, imbl::OrdSet<Arc<Formula>>>,
    /// The names' products at the end of the last projection.
    names_at: imbl::OrdMap<Arc<str>, Product>,
    /// The keys of the parts added since the block was last kept ([`Seen::owners`]).
    added: Vec<PartKey>,
}

impl Block {
    /// Block `b` of `relation`, with the conjuncts among its hubs when it is a star of two
    /// hubs or more ([`Conjuncts::core`]), made from all its conjuncts, with the names'
    /// products `names`.
    fn of(relation: &Conjuncts, b: BlockId, names: &imbl::OrdMap<Arc<str>, Product>) -> Block {
        let blocks = relation.blocks();
        let members = blocks.member_set(b).cloned().unwrap_or_default();
        let mut member_names: imbl::OrdMap<Arc<str>, usize> = imbl::OrdMap::new();
        for g in &members {
            for n in conjuncts::names(g) {
                *member_names.entry(n).or_insert(0) += 1;
            }
        }
        let apart = blocks.is_apart(b);
        let wide = apart && member_names.len() > 2;
        let mut core: imbl::OrdMap<Arc<Formula>, usize> = imbl::OrdMap::new();
        for g in &members {
            *core.entry(g.clone()).or_insert(0) += 1;
        }
        let mut free: imbl::OrdMap<Arc<str>, imbl::OrdSet<Arc<Formula>>> = imbl::OrdMap::new();
        if wide {
            for n in member_names.keys() {
                let set = relation.free_set(n).cloned().unwrap_or_default();
                for g in &set {
                    *core.entry(g.clone()).or_insert(0) += 1;
                }
                free.insert(n.clone(), set);
            }
        }
        let all: BTreeSet<Arc<str>> = core.keys().flat_map(|g| syms(g)).collect();
        let leaf = all.iter().find(|x| relation.star(x) == Some(b)).cloned();
        let cons: imbl::OrdSet<Arc<Formula>> = core
            .keys()
            .filter(|g| matches!(&***g, Formula::Con(_)))
            .cloned()
            .collect();
        let split = Arc::new(Split::new(&cons.iter().collect::<Vec<_>>(), leaf.as_ref()));
        let mut out = Block {
            id: b,
            parts: imbl::OrdMap::new(),
            users: imbl::OrdMap::new(),
            roles: imbl::OrdMap::new(),
            rays: imbl::OrdMap::new(),
            ray_managed: false,
            ray_due: None,
            upper_bounds: None,
            ray_least: OnceLock::new(),

            stair_managed: false,
            stair_due: None,
            leaf,
            core: imbl::OrdMap::new(),
            unshaped: imbl::OrdSet::new(),
            outer_cons: cons.clone(),
            cons,
            outer: split.clone(),
            split,
            terms: imbl::OrdMap::new(),
            mentions: imbl::OrdMap::new(),
            vars: imbl::OrdMap::new(),
            chains: imbl::OrdMap::new(),
            bounds: imbl::OrdMap::new(),
            stairs: imbl::OrdMap::new(),
            fired: BTreeSet::new(),
            spends: Vec::new(),
            forgot: imbl::OrdSet::new(),
            members,
            member_names,
            apart,
            wide,
            free,
            names_at: names.clone(),
            added: Vec::new(),
        };
        for (g, k) in &core {
            out.enter(g, *k);
        }
        out.add_constraints();
        out
    }

    /// Adds the constraints' own part, when there are constraints; returns where it stands.
    fn add_constraints(&mut self) -> Option<PartAt> {
        let (key, with, formula) = self.split.constraints()?;
        let at: PartAt = (true, key.0.clone());
        self.add_part(at.clone(), key, with, None, &formula);
        Some(at)
    }

    /// The formula projected for `part` ([`Part`]).
    fn formula(&self, part: &Part) -> Formula {
        self.split.formula(part.of.as_deref())
    }

    /// Whether `g` shows that a set of conjuncts holding it is no threshold-implication
    /// component ([`threshold::shape`]): an atom of `g` mentions two names, and `g` alone is
    /// none. The hub of a component is a name every atom of two names mentions, so the hubs
    /// `g` allows only narrow as conjuncts come, and each refusal of `shape` is one atom's or
    /// one disjunction's, for a given hub: `g`'s refusal under each hub it allows holds in any
    /// set that holds `g`.
    fn unshaped(g: &Arc<Formula>) -> bool {
        let pair = g.cons().into_iter().any(|c| {
            let syms = c.lin.terms.keys().filter(|a| matches!(a, Atom::Sym(_)));
            syms.count() >= 2
        });
        pair && threshold::shape(std::slice::from_ref(g)).is_none()
    }

    /// Counts `g` `k` more times among the conjuncts, giving it a part when it is new and no
    /// constraint; returns where the new part stands.
    fn enter(&mut self, g: &Arc<Formula>, k: usize) -> Option<PartAt> {
        let count = self.core.entry(g.clone()).or_insert(0);
        *count += k;
        if *count != k {
            return None;
        }
        if Block::unshaped(g) {
            self.unshaped.insert(g.clone());
        }
        if matches!(&**g, Formula::Con(_)) {
            self.cons.insert(g.clone());
            if let Some(least) = self.ray_least.get_mut()
                && let Some(((x, y), group)) = self.rays.iter().next()
            {
                least.take_con(g, x, y, group);
            }
            return None;
        }
        let (key, with, formula) = self.split.part(g, &self.outer);
        let at: PartAt = (false, g.clone());
        self.add_part(at.clone(), key, with, Some(g.clone()), &formula);
        Some(at)
    }

    /// Counts `g` once less among the conjuncts, taking its part away when it is gone.
    fn leave(&mut self, g: &Arc<Formula>) {
        let Some(count) = self.core.get_mut(g) else {
            return;
        };
        *count -= 1;
        if *count > 0 {
            return;
        }
        self.core.remove(g);
        self.unshaped.remove(g);
        if self.cons.remove(g).is_some() {
            self.ray_least.take();
        }
        self.remove_part(&(false, g.clone()));
    }

    /// Adds the part at `at`, projected as `formula`.
    fn add_part(
        &mut self,
        at: PartAt,
        key: PartKey,
        with: PartWith,
        of: Option<Arc<Formula>>,
        formula: &Formula,
    ) {
        let names = syms(formula);
        let role = Role::of(of.as_deref());
        if role != Role::Constraints {
            self.roles.entry(role).or_default().insert(at.clone());
        }
        if role == Role::Upper
            && let (Some(u), Some(g)) = (&mut self.upper_bounds, &of)
        {
            u.take(g);
        }
        if role == Role::Ray
            && let Some((x, y, j, d)) = of.as_ref().and_then(|g| ray_row(g))
        {
            let pair = (x.clone(), y.clone());
            if !self.rays.contains_key(&pair) {
                self.ray_least.take();
            }
            self.rays.entry(pair).or_default().add(&j, &d);
            if let Some(least) = self.ray_least.get_mut() {
                least.take_ray(&self.cons, &x, &y, &j, &d);
            }
        }
        for n in &names {
            let users = self.users.entry(n.clone()).or_default();
            users.of_role(role).insert(at.clone());
        }
        if let Some(g) = &of {
            for t in terms(g) {
                // Complexity tradeoff: one `Arc` allocation per term not yet a key, so that a
                // later path copy of `terms` shares the key, O(1), not O(t). COMPLEXITY.md C44.
                match self.terms.get_mut(&t) {
                    Some(parts) => {
                        parts.insert(at.clone());
                    }
                    None => {
                        self.terms
                            .insert(Arc::new(t), imbl::OrdSet::unit(at.clone()));
                    }
                }
            }
            for n in syms(g) {
                *self.mentions.entry(n).or_insert(0) += 1;
            }
            for x in factors(g) {
                self.vars.entry(x).or_default().insert(at.clone());
            }
            if let Some((x, y, a, b)) = stair_row(g) {
                let tree = self.stairs.entry((x, y)).or_default();
                *tree = tree.insert((b, a));
            }
        }
        let bounds = (of.as_ref()).map_or_else(Vec::new, |g| bounds_at(g, &with, &self.names_at));
        self.index_bounds(&at, &bounds);
        self.added.push(key.clone());
        let pure_two_sym = of.as_deref().and_then(pure_two_sym_pair).map(|(u, v)| {
            let m = finiteness_mask(&u, &v, &self.names_at);
            (u, v, m)
        });
        let chain = of.as_deref().and_then(chain_shape);
        if let Some((k, ends)) = &chain {
            self.chains
                .entry(k.clone())
                .or_default()
                .insert((ends.clone(), at.clone()));
        }
        let part = Part {
            key,
            with,
            of,
            names,
            role,
            bounds,
            pure_two_sym,
            chain,
        };
        self.parts.insert(at, Arc::new(part));
    }

    /// Takes the part at `at` away, if there is one.
    fn remove_part(&mut self, at: &PartAt) {
        let Some(part) = self.parts.remove(at) else {
            return;
        };
        if let Some(set) = self.roles.get_mut(&part.role) {
            set.remove(at);
            if set.is_empty() {
                self.roles.remove(&part.role);
            }
        }
        if part.role == Role::Upper {
            self.upper_bounds = None;
        }
        if part.role == Role::Ray
            && let Some((x, y, j, d)) = part.of.as_ref().and_then(|g| ray_row(g))
        {
            self.ray_least.take();
            let pair = (x, y);
            if let Some(group) = self.rays.get_mut(&pair) {
                group.remove(&j, &d);
                if group.rays.is_empty() {
                    self.rays.remove(&pair);
                }
            }
        }
        for n in &part.names {
            if let Some(us) = self.users.get_mut(n) {
                us.of_role(part.role).remove(at);
                if us.is_empty() {
                    self.users.remove(n);
                }
            }
        }
        if let Some((k, ends)) = &part.chain
            && let Some(set) = self.chains.get_mut(k)
        {
            set.remove(&(ends.clone(), at.clone()));
            if set.is_empty() {
                self.chains.remove(k);
            }
        }
        let Some(g) = &part.of else {
            return;
        };
        for t in terms(g) {
            if let Some(ps) = self.terms.get_mut(&t) {
                ps.remove(at);
                if ps.is_empty() {
                    self.terms.remove(&t);
                }
            }
        }
        for n in syms(g) {
            if let Some(k) = self.mentions.get_mut(&n) {
                *k -= 1;
                if *k == 0 {
                    self.mentions.remove(&n);
                }
            }
        }
        for x in factors(g) {
            if let Some(ps) = self.vars.get_mut(&x) {
                ps.remove(at);
                if ps.is_empty() {
                    self.vars.remove(&x);
                }
            }
        }
        if let Some((x, y, a, b)) = stair_row(g) {
            let key = (x, y);
            if let Some(tree) = self.stairs.get_mut(&key) {
                *tree = tree.remove(&(b, a), false);
                if tree.size() == 0 {
                    self.stairs.remove(&key);
                }
            }
        }
        self.unindex_bounds(at, &part.bounds);
    }

    /// Puts `entries` of the part at `at` in [`Block::bounds`].
    fn index_bounds(&mut self, at: &PartAt, entries: &[(BoundsKey, Turn)]) {
        for (key, turn) in entries {
            let by = self.bounds.entry(key.clone()).or_default();
            by.entry(turn.clone()).or_default().insert(at.clone());
        }
    }

    /// Takes them out again.
    fn unindex_bounds(&mut self, at: &PartAt, entries: &[(BoundsKey, Turn)]) {
        for (key, turn) in entries {
            let Some(by) = self.bounds.get_mut(key) else {
                continue;
            };
            if let Some(ps) = by.get_mut(turn) {
                ps.remove(at);
                if ps.is_empty() {
                    by.remove(turn);
                }
            }
            if by.is_empty() {
                self.bounds.remove(key);
            }
        }
    }

    /// Brings the constraints' context up to date after the constraints on the terms `changed`
    /// were added or are gone ([`Block::cons`]), and adds to `due` each part whose
    /// [`PartWith`] that changes: the constraints' own part, the parts on those terms, and the
    /// parts that hold two variables or more of a group of linked constraints ([`linked`]) that
    /// one of those constraints is in, before or after, found through [`Block::vars`]. The
    /// other parts are projected with what they were ([`PartWith`]) and mention the names
    /// they did, unless the equalities changed, or the constraints gain or lose a name some
    /// conjunct with a part does not mention: then `false`, and the block is to be made anew.
    fn reframe(
        &mut self,
        changed: &BTreeSet<BTreeMap<Atom, Int>>,
        removed_cons: &[Arc<Formula>],
        added_cons: &[Arc<Formula>],
        due: &mut Vec<PartAt>,
        groups: bool,
        spent: &imbl::OrdSet<BoundsKey>,
    ) -> bool {
        let split = self.split.update(&self.cons, removed_cons, added_cons);
        if split.eqs != self.split.eqs {
            return false;
        }
        // A name the constraints mention now and not before, or before and not now, is
        // still mentioned by each conjunct's part when each conjunct mentions it.
        let (then, now) = (&self.split.base_syms, &split.base_syms);
        let constraints = usize::from(self.split.constraints().is_some());
        let conjuncts = self.parts.len() - constraints;
        let kept = |n: &Arc<str>| self.mentions.get(n).copied().unwrap_or(0) == conjuncts;
        let differ = then.iter().filter(|n| now.binary_search(n).is_err());
        if !differ
            .chain(now.iter().filter(|n| then.binary_search(n).is_err()))
            .all(kept)
        {
            return false;
        }
        if let Some((key, _, _)) = self.split.constraints() {
            self.remove_part(&(true, key.0));
        }
        let split = Arc::new(split);
        // The groups each constraint added or gone since the groups were last read was in and
        // is in ([`Split::with`]), when they are read now: outside the cases of a test. Within
        // them, a case's constraint is gone again once the cases are joined, and the parts keep
        // the groups of `outer` (COMPLEXITY.md C52).
        let mut vars: BTreeSet<BTreeSet<Factor>> = BTreeSet::new();
        if groups {
            let mut groups: BTreeSet<(bool, usize)> = BTreeSet::new();
            for d in self.outer_cons.diff(&self.cons) {
                let (imbl::ordset::DiffItem::Add(g) | imbl::ordset::DiffItem::Remove(g)) = d;
                let Some(x) = factors(g).into_iter().next() else {
                    continue;
                };
                groups.extend(self.outer.group.get(&x).map(|&i| (false, i)));
                groups.extend(split.group.get(&x).map(|&i| (true, i)));
            }
            vars = groups
                .into_iter()
                .map(|(now, i)| {
                    let s = if now { &*split } else { &*self.outer };
                    s.groups[&i].0.clone()
                })
                .collect();
            self.outer = split.clone();
            self.outer_cons = self.cons.clone();
        }
        self.split = split;
        due.extend(self.add_constraints());
        let mut on: BTreeSet<PartAt> = changed
            .iter()
            .filter_map(|t| self.terms.get(t))
            .flatten()
            .cloned()
            .collect();
        // The parts that hold two variables of a changed group or more ([`Block::vars`]). Such
        // a part holds a variable of the group other than the one with the most parts, so the
        // parts of the others are read and counted, and a part counted once is due if it also
        // holds that one.
        // Complexity tradeoff: naive version, every part of each variable of the group read,
        // which is O(k) per test for k disjunctions that share one variable with the group
        // (`n` of `n + m <= c` under `n - v_i >= 5 || n + v_i <= -5`), or a lookup of each pair
        // of the group's v variables, O(v^2 log k) per test, with an index of O(s^2) pairs for
        // a part of s variables. Used: the parts of every variable of the group but the one
        // with the most, O((p + v) log k) for the p parts read, with a lookup in the parts of
        // that one for each part read once. Two variables of the group that each have k parts
        // the other lacks still cost O(k) per test (open). COMPLEXITY.md C52.
        for v in vars.iter().filter(|v| v.len() >= 2) {
            let count = |x: &Factor| self.vars.get(x).map_or(0, imbl::OrdSet::len);
            let most = v.iter().max_by_key(|x| count(x));
            let mut read: BTreeMap<&PartAt, usize> = BTreeMap::new();
            for x in v.iter().filter(|&x| Some(x) != most) {
                for at in self.vars.get(x).into_iter().flatten() {
                    *read.entry(at).or_insert(0) += 1;
                }
            }
            let of_most = most.and_then(|x| self.vars.get(x));
            for (at, k) in read {
                if k >= 2 || of_most.is_some_and(|ps| ps.contains(at)) {
                    on.insert(at.clone());
                }
            }
        }
        // Complexity tradeoff: naive versions: main's rule, a part due only when the constraints
        // on its own terms change, 7k + 1 projections for the star `a >= x + y` and k
        // disjunctions `x + j * y >= 1 || x - j * y >= 1`, but coarser ends at seeds 781, 1515
        // and 1820; or the groups read inside the cases of a test too, (3k + 1)(k + 1)
        // projections on that star, O(k^2): each arm adds a constraint to the group of
        // `a >= x + y`, which all k parts hold two variables of, and the join of the arms drops
        // each part's record, since the arms projected it with different constraints. Used: the
        // groups are read only outside the cases, against the constraints when they were last
        // read (`outer_cons`), so a case's constraint, gone again at the join, wakes no part
        // through a group: 7k + 1 projections on the star, as main, O(g log k) per test for the
        // g parts of the changed groups. Lost against reading the groups in the cases: a
        // narrowing a case's constraint reaches only through a group, never wider than main.
        // Waking such parts in a case by a test on their names was measured and is quadratic
        // where main is linear (by shared factor: on `x + j * a >= 1` arms; by pair of names:
        // on staircase parts). COMPLEXITY.md C52.
        // Inside the cases, a case's constraint on two names `u` and `v` reaches the
        // disjunctions on them whose arms it all makes bound an end of `u` or `v` that some arm
        // does not bound alone, with the constraints the part is projected with, found in
        // [`Block::bounds`] ([`bounds_at`]). Projected with the
        // case's constraints, such a part bounds that end in every arm. The end may be finite
        // already: with `0 <= x <= 10` and `0 <= y <= 10`, the disjunction
        // `x <= 1 || (y == 5 && 4 <= x <= 6) || (y >= 10 && x >= 7)` keeps `x` in 0..=10, and
        // its last arm does not bound `x` above alone; in the case `x + y <= 10` that arm is
        // empty and the second gives `x <= 5`, so `x` is in 0..=5 there. Such a part is
        // projected (`fired`), keyed as outside the cases so that the join keeps its record,
        // and the entry of the index the end was found by (the two names, the end and the side
        // of it) is spent on this path of tests ([`Scope::spent`]).
        // Complexity tradeoff: naive version, the parts found projected in each case, O(k) per
        // case when k parts are found and the end stays open, O(k^2) over k tests on the parts
        // `x >= i || y <= -1000 + i` and the tests `x + y <= -j || z >= j`, whose second case
        // never bounds `y`. Used: each entry projected for once on a path of tests, O(log k)
        // per end and direction of a case's constraint, and O(log k + f) for the f parts found
        // the one time, so O(n log n) in all for n parts and constraints, as each part has
        // O(m) entries for its m rows; lost against the naive version: a part that would bound
        // the end again by the same entry in a later test, after a join that dropped the first
        // bound, or after a firing on a finite end that moved nothing. Spending the end itself
        // for both sides and every pair of names lost more: at seed 85, `y`'s lower end spent
        // by `a + 2 * y >= 3` hid the part `x + y >= -1 || x + 3 * z >= -4` from the later
        // `y >= 2 * a - 1`, which bounds it from the other side. COMPLEXITY.md C52,
        // LAZY-hub-finite, LAZY-hub-unsolved.
        if !groups {
            for t in changed {
                for c in self.split.on.get(t).into_iter().flatten() {
                    let Some((u, v, q)) = two_names(c) else {
                        continue;
                    };
                    let (Factor::Sym(un), Factor::Sym(vn)) = (&u, &v) else {
                        continue;
                    };
                    let mut qs = vec![q.clone()];
                    if c.rel == Rel::Eq {
                        qs.push([-&q[0], -&q[1]]);
                    }
                    for end in 0..4u8 {
                        for q in &qs {
                            let q = turned(end, q);
                            // Both coefficients of a constraint on two names are nonzero.
                            if q[1].is_zero() {
                                continue;
                            }
                            let left = q[1].is_positive();
                            let key = (un.clone(), vn.clone(), end, left);
                            if spent.contains(&key) {
                                continue;
                            }
                            let Some(by) = self.bounds.get(&key) else {
                                continue;
                            };
                            let q = Turn(q);
                            let range = if left {
                                (std::ops::Bound::Excluded(q), std::ops::Bound::Unbounded)
                            } else {
                                (std::ops::Bound::Unbounded, std::ops::Bound::Excluded(q))
                            };
                            for (_, ps) in by.range(range) {
                                self.spends.push(key.clone());
                                self.fired.extend(ps.iter().cloned());
                                due.extend(ps.iter().cloned());
                            }
                        }
                    }
                }
            }
        }
        let names_at = self.names_at.clone();
        for at in on {
            let Some(part) = self.parts.get_mut(&at) else {
                continue;
            };
            let Some(g) = &part.of else {
                continue;
            };
            let with = self.split.with(g, &self.outer);
            if with != part.with {
                // Complexity tradeoff: naive version, the entries made again by `bounds_at` at
                // each change of `with`, O(r) for the arm's r rows and their derived rows per
                // part per reframe, O(k^2 r) over `persist`'s k reframes of k parts. Used: a part
                // whose arms are rows on its two names alone, in a block with no equalities, has
                // entries that do not read `with` and read the names only through which of the
                // two names' ends are finite (`bounds_at`, the rule there), so they are kept
                // while that mask holds, O(log n). The part is still due. Gemini seat, round 3.
                if self.split.eqs.is_empty()
                    && let Some((u, v, old_mask)) = &part.pure_two_sym
                    && finiteness_mask(u, v, &names_at) == *old_mask
                {
                    Arc::make_mut(part).with = with;
                    due.push(at);
                    continue;
                }
                // The part's entries in `bounds` read what it is projected with.
                let bounds = bounds_at(g, &with, &names_at);
                let part = Arc::make_mut(part);
                part.with = with;
                if let Some((u, v, m)) = &mut part.pure_two_sym {
                    *m = finiteness_mask(u, v, &names_at);
                }
                let was = (bounds != part.bounds)
                    .then(|| std::mem::replace(&mut part.bounds, bounds.clone()));
                if let Some(was) = was {
                    self.unindex_bounds(&at, &was);
                    self.index_bounds(&at, &bounds);
                }
                due.push(at);
            }
        }
        true
    }

    /// This block brought up to date with `relation` and the names' products `names`, with the
    /// parts that may be due: those new to it and those that mention a name whose product
    /// changed since its last projection, or whose [`PartWith`] a constraint added or gone
    /// changed ([`Block::reframe`]). `None` when it is to be made anew: the equalities or the
    /// names of the constraints changed, or its leaf, its being apart or its taking the free
    /// conjuncts at its names.
    ///
    /// Complexity tradeoff: naive version, the block made again from all its conjuncts at each
    /// projection ([`Block::of`]), each part split, checked and recorded, O(k log k) per test
    /// for `k` parts, O(k² log k) for `k` tests that each add one. Used: the members and the
    /// free conjuncts at the members' names are diffed against those kept, persistent sets
    /// whose diff skips what they share, in O((c + m) log k) for `c` changes and `m` names of
    /// the members of a star (each one's free conjuncts diffed); the names' products changed
    /// since the keep are walked until they outnumber the block's names `u`, then those names
    /// are compared, O(min(c', u) log n) for `c'` such changes and `n` names in all, where
    /// walking every one was O(c' log n), with `c'` growing with the tests on other blocks,
    /// O(k²) in all for `k` stars each checked after each test; a star's leaf is looked up,
    /// O(log n), where diffing all the stars was O(k) for `k` stars made since; a constraint
    /// added or gone makes the constraints' context again, O(r log r) for `r` constraints, and re-keys the parts on its term through an
    /// index of the parts by term, O(t log k) for `t` such parts. Tradeoffs: the block keeps
    /// its parts, indexes of the parts by name and by term and those sets, shared with the
    /// relation and the scope, until the next projection; each part's formula is made when it
    /// is projected, O(r) each time, and not kept; a change of the equalities or of the names
    /// the constraints mention changes every part, so the block is made anew, as before.
    /// COMPLEXITY.md row C26.
    fn update(
        &self,
        relation: &Conjuncts,
        names: &imbl::OrdMap<Arc<str>, Product>,
        groups: bool,
        spent: &imbl::OrdSet<BoundsKey>,
    ) -> Option<(Block, Vec<PartAt>)> {
        let blocks = relation.blocks();
        if blocks.is_apart(self.id) != self.apart {
            return None;
        }
        // A star's block is made with a new id ([`conjuncts::Blocks::detach`]) and its leaf's
        // entry goes only with the block, so no other leaf's star becomes this block.
        if self.apart && self.leaf.as_ref().and_then(|x| relation.star(x)) != Some(self.id) {
            return None;
        }
        let mut next = self.clone();
        next.added = Vec::new();
        next.fired = BTreeSet::new();
        next.spends = Vec::new();
        next.stair_due = None;
        let empty = imbl::OrdSet::new();
        let members = blocks.member_set(self.id).unwrap_or(&empty);
        // Each conjunct's change in count, applied once the block is known to be kept.
        let mut delta: BTreeMap<Arc<Formula>, (usize, usize)> = BTreeMap::new();
        for d in self.members.diff(members) {
            match d {
                imbl::ordset::DiffItem::Add(g) => {
                    for n in conjuncts::names(g) {
                        *next.member_names.entry(n).or_insert(0) += 1;
                    }
                    delta.entry(g.clone()).or_default().0 += 1;
                }
                imbl::ordset::DiffItem::Remove(g) => {
                    for n in conjuncts::names(g) {
                        if let Some(k) = next.member_names.get_mut(&n) {
                            *k -= 1;
                            if *k == 0 {
                                next.member_names.remove(&n);
                            }
                        }
                    }
                    delta.entry(g.clone()).or_default().1 += 1;
                }
            }
        }
        next.members = members.clone();
        if (self.apart && next.member_names.len() > 2) != self.wide {
            return None;
        }
        if self.wide {
            for (n, was) in &self.free {
                if next.member_names.contains_key(n) {
                    continue;
                }
                for g in was {
                    delta.entry(g.clone()).or_default().1 += 1;
                }
                next.free.remove(n);
            }
            for n in next.member_names.keys() {
                let now = relation.free_set(n).unwrap_or(&empty);
                let was = self.free.get(n).unwrap_or(&empty);
                for d in was.diff(now) {
                    let (g, added) = match d {
                        imbl::ordset::DiffItem::Add(g) => (g, true),
                        imbl::ordset::DiffItem::Remove(g) => (g, false),
                    };
                    let at = delta.entry(g.clone()).or_default();
                    if added {
                        at.0 += 1;
                    } else {
                        at.1 += 1;
                    }
                }
                next.free.insert(n.clone(), now.clone());
            }
        }
        // Complexity tradeoff: naive version, each part made due put in a `BTreeSet` as it is
        // found. A node of the set is searched in order, so u parts that fall in one node cost
        // O(u) comparisons each, and two parts of one name differ only deep in their formulas:
        // in `hopb` a case on `x` makes its k disjunctions due at each wake, O(k^2) deep
        // comparisons per wake (15.2M instructions at k = 16, 0.1M at k = 2). Used: the parts
        // pushed on a vector, which is sorted once (a stable sort, which finds the runs each
        // name's users already give in order) and then rid of each part equal to the one
        // before it, O(u log r) comparisons for r runs. The set kept the first of two equal
        // parts and gave them in order; the stable sort and `dedup_by` keep the first and give
        // the same order, so the same parts are due in the same order and no answer changes.
        // Measured (`probe_l139`, hopb, k = 16): 5.9M instructions fewer. Prior work: building
        // a set from a sorted run in one pass, as `BTreeSet::from_iter` does, instead of
        // inserting each element.
        let mut due: Vec<PartAt> = Vec::new();
        // The constraints first, so that a part added after reads them as they are now.
        let mut changed: BTreeSet<BTreeMap<Atom, Int>> = BTreeSet::new();
        let mut removed_cons: Vec<Arc<Formula>> = Vec::new();
        let mut added_cons: Vec<Arc<Formula>> = Vec::new();
        for (g, (added, gone)) in &delta {
            let Formula::Con(c) = &**g else {
                continue;
            };
            let was = next.cons.contains(g);
            for _ in 0..*gone {
                next.leave(g);
            }
            if *added > 0 {
                next.enter(g, *added);
            }
            let now_in = next.cons.contains(g);
            if was != now_in {
                changed.insert(unsigned(c));
                if was {
                    removed_cons.push(g.clone());
                } else {
                    added_cons.push(g.clone());
                }
            }
        }
        // Outside the cases of a test, the groups are read again when they were last read within
        // them ([`Block::outer`]), though no constraint changed since.
        let stale = groups && next.outer_cons.diff(&next.cons).next().is_some();
        if (!changed.is_empty() || stale)
            && !next.reframe(
                &changed,
                &removed_cons,
                &added_cons,
                &mut due,
                groups,
                spent,
            )
        {
            return None;
        }
        let others = delta
            .into_iter()
            .filter(|(g, _)| !matches!(&**g, Formula::Con(_)));
        for (g, (added, gone)) in others {
            for _ in 0..gone {
                next.leave(&g);
            }
            if added > 0 {
                due.extend(next.enter(&g, added));
            }
        }
        let manages = next.manages_stairs(names);
        // Complexity tradeoff: a name change used to enqueue all k threshold rows and write
        // k snapshots per case. The exact aggregate has one snapshot (`names_at`) and one
        // demand. Only ordinary users are walked, O(u log k) for u such users, plus the
        // O((r+1) log k) aggregate query for r base rows. Leaving the handled shape restores
        // every individual row to the ordinary due rule, O(k) on that transition.
        // An aggregate that holds is read again, through one part of its role, when it did
        // not hold before or when anything it reads may have changed. A block an aggregate
        // holds for has two names, so the names are compared in O(1).
        let renewed = |was: bool, next: &Block| {
            !was || !changed.is_empty()
                || !next.added.is_empty()
                || (next.users.keys()).any(|n| !same_framed_opt(self.names_at.get(n), names.get(n)))
        };
        if manages && renewed(self.stair_managed, &next) {
            let first = next.of_role(Role::Stair).next().cloned();
            next.stair_due = first;
            due.extend(next.stair_due.iter().cloned());
        }
        next.stair_managed = manages;
        next.ray_due = None;
        next.ray_managed = next.ray_high(names).is_some();
        if next.ray_managed && renewed(self.ray_managed, &next) {
            let first = next.of_role(Role::Ray).next().cloned();
            next.ray_due = first;
            due.extend(next.ray_due.iter().cloned());
        }
        due.extend(next.released(self.stair_managed, self.ray_managed).cloned());

        // The names whose products changed: the changes since the block was kept while they
        // are no more than its names, else each of its names compared.
        let mut walked = 0;
        for d in self.names_at.diff(names) {
            if let DiffItem::Update {
                old: (_, a),
                new: (_, b),
            } = &d
                && same_framed(a, b)
            {
                continue;
            }
            walked += 1;
            if walked > next.users.len() {
                break;
            }
            let (DiffItem::Add(n, _)
            | DiffItem::Remove(n, _)
            | DiffItem::Update { new: (n, _), .. }) = d;
            due.extend(next.due_users(n).cloned());
        }
        if walked > next.users.len() {
            for n in next.users.keys() {
                if !same_framed_opt(self.names_at.get(n), names.get(n)) {
                    due.extend(next.due_users(n).cloned());
                }
            }
        }
        let forgot = std::mem::take(&mut next.forgot);
        due.extend(forgot);
        due.sort();
        due.dedup_by(|a, b| a.0 == b.0 && a.1.cmp(&b.1).is_eq());
        // A part made due above may be gone since, with its conjunct.
        due.retain(|at| {
            next.parts.get(at).is_some_and(|p| {
                !(manages && p.role.stair()) || next.stair_due.as_ref() == Some(at)
            })
        });
        Some((next, due))
    }

    /// The names the block's parts mention, in order.
    fn names(&self) -> Vec<Arc<str>> {
        self.users.keys().cloned().collect()
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

/// A root of an obligation's equation ([`Scope::zero_reached`]) at which a written constraint
/// gave neither `true` nor `false` (DESIGN.md sec:constraints, QUESTIONS A81): the constraint
/// cannot rule the root out, and the program does not say what it means there. Ordered by
/// name, root and constraint, so that the reports do not depend on the order they were met in.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct RootFailure {
    /// The name the equation is in, as the program writes it.
    pub name: Arc<str>,
    /// The root.
    pub root: i64,
    /// The constraint, as written.
    pub constraint: Arc<str>,
    /// What it gave at the root, as printed.
    pub gave: Arc<str>,
}

/// The sets a refused question left its variables, each by its name in the scope: a set holds
/// every value the question allows the variable and may hold more. For a refused projection
/// they are the bounds the box stage gives the rows (DESIGN step L1.38), and for a refused test
/// the box of its preimage. Empty where the question left no variable such a set: a case of an
/// alternative set aside, or the ends of names with holes.
pub type Kept = Arc<BTreeMap<Arc<str>, IntervalSet>>;

/// `by` with the question `r` under each of `names`, the names of the scope its constraint
/// mentions ([`Scope::refused_by`]), O(n log k) for the n names among k questions.
fn index_refused(
    by: &mut imbl::OrdMap<Arc<str>, imbl::OrdSet<Refused>>,
    r: &Refused,
    names: &[Arc<str>],
) {
    for n in names {
        by.entry(n.clone()).or_default().insert(r.clone());
    }
}

/// Those of `names`, names of a scope, that a constraint printed as `text` mentions: each one
/// whose written name ([`written_name`]) the text holds outside a call
/// ([`presburger::names_in`]). The scope's names keep their bindings apart, as `x` and the
/// `x@k` that shadows it, which the text does not. O(t + n) for a text of length t and n
/// names.
fn mentioned(text: &str, names: impl IntoIterator<Item = Arc<str>>) -> Vec<Arc<str>> {
    let written: std::collections::HashSet<&str> = presburger::names_in(text).into_iter().collect();
    (names.into_iter())
        .filter(|n| written.contains(written_name(n)))
        .collect()
}

/// The names `f` mentions, as the scope holds them, the factors of a product included. O(c log
/// a) for c constraints and a atoms.
fn syms_of(f: &Formula) -> impl Iterator<Item = Arc<str>> {
    let factor = |x: Factor| match x {
        Factor::Sym(n) => Some(n),
        Factor::Aux(_) => None,
    };
    (f.atoms().into_iter())
        .flat_map(move |a| match a {
            Atom::Sym(n) => [Some(n), None],
            Atom::Product(x, y) => [factor(x), factor(y)],
            Atom::Aux(_) => [None, None],
        })
        .flatten()
}

/// The sets of one refused question met twice, each of whose sets holds every value the
/// question allows: their meet for each variable both hold, and the set of a variable only
/// one holds. So the sets kept do not depend on the order the two were met in. O(m log m) in
/// the m variables; `a` itself, shared, when the two are equal.
pub fn kept_meet(a: &Kept, b: &Kept) -> Kept {
    match a == b {
        true => a.clone(),
        false => Arc::new(merged(a, b, IntervalSet::meet, true)),
    }
}

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
    /// The test's `||` alternatives limit each other's ranges in a loop, which the checker
    /// would have to run a number of times that grows with the ranges (DESIGN.md step L1.39,
    /// the class of S4): the checker rejects the test, with this message, instead of warning.
    /// The scope is narrowed as before.
    Looped(Arc<loops::Looped>),
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

/// What a refused question costs the program, which closes the step that says what the scope
/// keeps: the scope is wider than the program's conditions, never narrower.
const SOUND: &str = "so the checker may reject or warn about code here that is correct, and it \
                     does not accept code that is wrong";

impl Refused {
    /// The warning that reports this refusal, with its derivation and its repairs, and the sets
    /// `sets` it left its variables.
    pub fn warning(&self, sets: &Kept) -> Warning {
        let (message, steps, repairs) = self.parts(sets);
        Warning {
            message,
            steps: steps.into_iter().chain(repairs).collect(),
        }
    }

    /// The steps of the derivation of this refusal's warning, without its message and its
    /// repairs, with the sets `sets` it left its variables: what a rejection the refusal may
    /// have caused names of it (DESIGN.md L1.39).
    pub fn derivation(&self, sets: &Kept) -> Vec<String> {
        self.parts(sets).1
    }

    /// The message of this refusal's warning, the steps of its derivation, and its repairs.
    fn parts(&self, sets: &Kept) -> (String, Vec<String>, Vec<String>) {
        let c = &self.constraint;
        let cause = match &self.cause {
            Cause::Solver(r) => r,
            Cause::Looped(l) => {
                return (l.headline.clone(), l.steps.clone(), vec![l.repair.clone()]);
            }
            Cause::Holes { holed, names } => {
                let holed: Vec<String> = holed.iter().map(|n| format!("`{n}`")).collect();
                return (
                    "Cannot find exactly the least and greatest values the conditions here \
                     allow"
                        .to_string(),
                    vec![
                        format!("the constraints `{c}` hold in the scope"),
                        format!(
                            "they join their {names} names both ways in more than one cycle, \
                             and {} of them have holes: {}; the ends of such names are found \
                             exactly when at most two of them have holes",
                            holed.len(),
                            holed.join(", ")
                        ),
                        format!(
                            "the names of the constraints are narrowed one block at a time, and \
                             their ends may be wider than the constraints make them; {SOUND}"
                        ),
                    ],
                    Vec::new(),
                );
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
        let (message, given, asked, kept) = match &self.asked {
            Asked::Test { outcome } => (
                format!("Cannot find exactly which values make `{c}` {outcome}"),
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
                "Cannot find exactly which values meet the conditions here".to_string(),
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
                "Cannot find exactly which values meet one side of a `||` here".to_string(),
                format!("here the conditions `{c}` hold"),
                format!(
                    "the checker could not work out which values one case of an alternative \
                     among them allows (a side of a `||`), so it set that case aside: {cause}"
                ),
                "so the conditions narrow the values of their variables without that case",
            ),
            Asked::Onto(n) => (
                format!("Cannot find exactly which values `{n}` can take here"),
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
        (
            message,
            vec![given, asked, format!("{kept}; {SOUND}")],
            repairs,
        )
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
            relation: Conjuncts::default().into(),
            written: imbl::OrdMap::new(),
            written_by: Uses::default(),
            kept: KeptTests::default(),
            bottom: false,
            emptied: Emptied::default(),
            enumerated: imbl::OrdSet::new(),
            projected: imbl::OrdMap::new(),
            exact,
            exactly: imbl::OrdMap::new(),
            refusals: imbl::OrdMap::new(),
            refused_by: imbl::OrdMap::new(),
            bindings: imbl::OrdMap::new(),
            orders: imbl::OrdMap::new(),
            clock: 0,
            reduced: Reduced::default(),
            seen: Seen::default(),
            potential: Potential::default(),
            lazy: false,
            in_case: false,
            spent: imbl::OrdSet::new(),
            direct: imbl::OrdMap::new(),
            gaps: LowerGaps::default(),
            rooted: imbl::OrdSet::new(),
            root_failures: imbl::OrdSet::new(),
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
    ///
    /// Settling can give a finer product than the eager scope holds: an eager part projected
    /// before a constraint on another term of its names is not due again, and keeps the
    /// coarser product (`Scope::refresh`, seed 22671 of `l01_39_reduced_product::lazy`).
    pub fn lazy(mut self) -> Scope {
        self.lazy = true;
        self
    }

    /// The stars of the leaves among `names` that are stale ([`Scope::lazy`]), as the
    /// blocks to project. None while every conjunct of the relation is a unary bound or was
    /// admitted onto the names' paths ([`NameProducts`]): a path's members are already the
    /// projection of its conjuncts, which the solver would give again, and a unary bound
    /// makes no star.
    // Complexity tradeoff (item ST-walk-checker-admit): naive version, the stars of the test's
    // names read from the relation, which adds the admitted conjuncts held apart (O(k log n)
    // for k of them, `Relation`), and each due part projected by the solver, which takes every
    // name off its path (O(n log² n)): Theta(n²) over n tests of a chain in the checker's lazy
    // scopes. Used: the relation still at the mark of the paths' last admission
    // (`Scope::extend_path`, which refuses a link while the relation holds more than unary
    // bounds) gives none, O(1). Tradeoff: a part admitted onto a path is not recorded as
    // projected, so once the names leave their paths it is projected by the solver once.
    fn stale<'a>(&self, names: impl IntoIterator<Item = &'a Arc<str>>) -> Vec<BlockId> {
        if self.names.on_paths(&self.relation) {
            return Vec::new();
        }
        let mut seen: BTreeSet<BlockId> = BTreeSet::new();
        let mut out = Vec::new();
        for x in names {
            let Some(b) = self.relation.star(x) else {
                continue;
            };
            if !seen.insert(b) {
                continue;
            }
            if !self.block(&self.relation, b).1.is_empty() {
                out.push(b);
            }
        }
        out
    }

    /// Block `b` of `relation` ([`Block`]), the one kept from the last projection brought up
    /// to date when there is one ([`Block::update`]), with its parts that are due in order: those
    /// new or not projected with their names' intervals and classes as they are now.
    fn block(&self, relation: &Conjuncts, b: BlockId) -> (Block, Vec<PartAt>) {
        let kept = self.seen.blocks.get(&b).filter(|k| k.id == b);
        let (mut block, maybe) =
            match kept.and_then(|k| k.update(relation, &self.names, !self.in_case, &self.spent)) {
                Some(found) => found,
                None => {
                    let block = Block::of(relation, b, &self.names);
                    let all = block.parts.keys().cloned().collect();
                    (block, all)
                }
            };
        block.ray_managed = block.ray_high(&self.names).is_some();
        let due: Vec<PartAt> = maybe
            .into_iter()
            .filter(|at| {
                let p = &block.parts[at];
                if block.ray_managed && p.role == Role::Ray && block.ray_due.as_ref() != Some(at) {
                    return false;
                }

                block.stair_due.as_ref() == Some(at)
                    || block.ray_due.as_ref() == Some(at)
                    || block.fired.contains(at)
                    || (!self.is_projected(&p.key, &p.with, &p.names)
                        && !self.puncture_idle(&block, &p.key.0))
            })
            .collect();
        (block, due)
    }

    /// Keeps `block` as its projection left it, with the names' products as they are now.
    fn keep(&mut self, mut block: Block) {
        block.names_at = self.names.view().clone();
        for w in std::mem::take(&mut block.spends) {
            self.spent.insert(w);
        }
        for key in std::mem::take(&mut block.added) {
            self.seen.owners.entry(key).or_default().insert(block.id);
        }
        // Complexity tradeoff: the block goes behind an `Arc` once, one allocation, so the path
        // copy this insert makes copies pointers, not blocks. COMPLEXITY.md C44.
        self.seen.blocks.insert(block.id, Arc::new(block));
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
    ///
    /// Complexity tradeoff: naive version, each stale leaf's star projected alone, one
    /// projection per leaf, O(leaves × size of a star's core). Used: one projection per class
    /// whose other names, interval and class match, and a meet per further leaf, O(classes ×
    /// core + leaves × log classes), the classes in an ordered map local to the call.
    /// Tradeoffs: memory for each class's names before and the leaf's interval after, until
    /// the call ends; a leaf whose names or interval differ, or whose projection the solver
    /// refused in part, is projected alone as before, so no answer changes. COMPLEXITY.md
    /// row C37.
    pub fn settle<'a>(&mut self, names: impl IntoIterator<Item = &'a Arc<str>>) {
        if !self.lazy || self.bottom {
            return;
        }
        let blocks = self.stale(names);
        self.settle_blocks(blocks, false);
    }

    /// Before a join ([`Scope::join`]), brings the stars of the leaves among `names` to the
    /// product their present core gives: settles them in a lazy scope; in an eager one,
    /// projects again each star's block that holds exactly one conjunct that is not a
    /// constraint, as well as its due parts. Each such conjunct `g` is projected as `g` met
    /// with the block's constraints, and its part is due only when the constraints on the
    /// terms `g` compares, or those terms' products, changed (`Scope::is_projected`). A
    /// constraint added later on another term of the block's names then leaves `g`'s
    /// projection made with the old constraints, which holds but is coarser than `g`
    /// projected with the new ones. With leaves `a >= n && a >= -m` and `g` = `m + n <= -7 ||
    /// m + n >= 2`, a case that adds `m <= n + 5` reads `a >= -2` where the enumeration of
    /// the hubs in `-10..=10` gives `a >= -1`, and the eager join of two such cases took the
    /// union of the coarse sides (`l01_39_reduced_product::lazy`, seed 22671). The lazy join
    /// escapes this because the tests that left the leaf stale made each part of its block
    /// due. If refreshing finds an eager scope empty, the join is the other side
    /// ([`Scope::join_refreshed`]).
    ///
    /// Complexity tradeoff: naive version, every part of each star's block projected again,
    /// O(d) projections per star of d disjunctions per join and O(k²) over k stars that share
    /// d = k distinct disjunctions (57.4× the bytes at 8×k on
    /// `l01_39_reduced_product::scaling::an_eager_scope_with_many_distinct_disjunctions_among_the_hubs_of_a_star_scales`).
    /// Used: only a block with one conjunct not a constraint has that part projected again,
    /// one part per star, with the classes of `Scope::settle` (C37) shared. Tradeoff: a block
    /// of two such conjuncts or more keeps the parts its constraints did not make due, as
    /// before; S16 projects such a core one disjunction at a time in any case. Tests:
    /// `l01_39_reduced_product::lazy::a_join_settles_a_star_it_drops_or_whose_core_gains_a_disjunction`
    /// (the eager join against the enumeration) and
    /// `l01_39_reduced_product::scaling::an_eager_join_projects_again_the_stars_it_settles_and_scales`;
    /// COMPLEXITY.md row C45.
    fn refresh<'a>(&mut self, names: impl IntoIterator<Item = &'a Arc<str>>) {
        if self.lazy {
            return self.settle(names);
        }
        if self.bottom {
            return;
        }
        let mut seen: BTreeSet<BlockId> = BTreeSet::new();
        let blocks: Vec<BlockId> = names
            .into_iter()
            .filter_map(|x| self.relation.star(x))
            .filter(|b| seen.insert(*b))
            .collect();
        self.settle_blocks(blocks, true);
    }

    /// Projects the due parts of `blocks` ([`Scope::settle`]), and with `fresh` also the one
    /// part of a block that holds exactly one conjunct not a constraint (`Scope::refresh`),
    /// then reduces.
    fn settle_blocks(&mut self, blocks: Vec<BlockId>, fresh: bool) {
        if blocks.is_empty() {
            return;
        }
        // Per class, the other names and the leaf's interval and class before its last
        // projection, and the leaf's interval after.
        type Before = (Projected, (IntervalSet, Congruence));
        let mut done: BTreeMap<conjuncts::Class, (Before, IntervalSet)> = BTreeMap::new();
        for id in blocks {
            let (b, mut due) = self.block(&self.relation, id);
            if fresh {
                let mut free = b.parts.iter().filter(|(_, p)| p.of.is_some());
                if let (Some((at, _)), None) = (free.next(), free.next())
                    && !due.contains(at)
                {
                    due.push(at.clone());
                }
                // A block with nothing to project, as most in an eager scope, is kept as it is.
                if due.is_empty() {
                    self.keep(b);
                    continue;
                }
            }
            let class = b.leaf.as_ref().and_then(|x| {
                let c = self.relation.class_of(x)?.clone();
                Some((x.clone(), c))
            });
            let Some((leaf, class)) = class else {
                self.project_block(b, due);
                continue;
            };
            let others: Vec<Arc<str>> = b.names().into_iter().filter(|n| *n != leaf).collect();
            let own = |s: &Scope| {
                let p = s.get(&leaf);
                (p.ints().clone(), framed_class(&p))
            };
            let before: Before = (self.snapshot(&others), own(self));
            if let Some((_, after)) = done.get(&class).filter(|(was, _)| *was == before) {
                let after = after.clone();
                if let Some(p) = self.names.get_mut(&leaf) {
                    let prem = p.premises();
                    p.meet_ints(after, &prem);
                }
                for p in b.parts.values() {
                    let at = self.snapshot(&p.names);
                    self.projected.insert(p.key.clone(), (p.with.clone(), at));
                }
                self.keep(b);
                continue;
            }
            let refused = self.refusals.len();
            self.project_block(b, due);
            if self.refusals.len() == refused
                && !self.get(&leaf).ints().is_empty()
                && self.snapshot(&others) == before.0
            {
                done.insert(class, (before, self.get(&leaf).ints().clone()));
            }
        }
        self.reduce_with(false);
        debug_assert!(fresh || !self.bottom, "settling a leaf emptied a scope");
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
        // The stars a lazy scope left unprojected are not known: each is cut by every bound
        // until it is projected ([`Order::projected`]).
        if self.lazy {
            self.seen.order = Order::default();
        }
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
    // Complexity tradeoff: naive version, the body of each `let` gets a copy of the whole
    // scope, O(s) per binding and O(n²) over a chain of n `let`s. Used: the binding changes the
    // scope in place and `Scope::unbind` restores it from the returned `Unbind`, O(log s) in the
    // persistent maps plus the reductions of `p`, near linear over the chain (42.6 ms → 3.4 ms
    // at 200 `let`s). Tradeoffs: the scope is still copied when `x` shadows a name or `p` is empty; bindings must be
    // undone in the reverse order they were made. Tests: `l01_39_reduced_product::scaling`
    // and `a_binding_forgets_what_held_of_the_name_it_shadows`; COMPLEXITY.md row S8.
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

    /// Meets the type of `x`, when in scope, with `ty`, the type `x` has where the scope is
    /// read. A join of a side that holds `x` with one that never read it holds `x` of no type
    /// (`Scope::join_settled`), and its relation may still mention `x`: in `a >= n || a >=
    /// 5`, the case `a >= 5` reads no `n`. Unlike [`Scope::bind`], which forgets what held of
    /// the name, the relation is kept, so a test on `x` below reaches the names it relates
    /// `x` to. O(log² n) for `n` names.
    // Complexity tradeoff (item ST-walk-checker-admit): naive version, read `x` from the whole
    // map (`NameProducts`'s `Deref`), which builds every path's members, O(n log² n) for each
    // scope version, and the checker meets the type of every name it reads. Used:
    // `NameProducts::read`, O(log² n); the write, which takes `x` off its path (O(n log² n)),
    // happens only when the type narrows, and it rarely does, since the type was met already.
    pub fn meet_type(&mut self, x: &Arc<str>, ty: &Type) {
        let Some(p) = self.names.read(x) else {
            return;
        };
        let met = p.ty.element.meet(ty);
        if self.bottom || met == p.ty.element {
            return;
        }
        let mut p = p.into_owned();
        p.ty.element = met;
        // Until no reduction changes a domain; each change is a meet, so the loop descends.
        while p.reduce_domains() {}
        let empty = p.is_empty();
        self.names.insert(x.clone(), p);
        if empty {
            self.bottom = true;
            self.empty_if_bottom();
        }
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
            Some(_) => Lazy::made(summary),
        };
        let order = self.clock;
        let lambda = matches!(**e, Term::Lam(..));
        let binding = Binding {
            function: lambda.then(|| e.clone()),
            summary,
            term: (!lambda && self.summarizes(&p)).then(|| e.clone()),
        };
        self.clock += 1;
        if !self.bottom && !p.is_empty() && !self.names.contains_key(x) {
            let before = self.fresh_before();
            self.names.set_fresh(x, Some(p));
            self.bindings.insert(x.clone(), binding);
            self.orders.insert(x.clone(), order);
            self.seen_fresh(x, before.as_ref());
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
        let gone: Vec<Address> = self.kept.by.of(x).cloned().collect();
        for k in &gone {
            self.kept.forget(k);
        }
        // The ends tests gave the old `x` do not hold of the new one.
        for upper in [false, true] {
            self.direct.remove(&(x.clone(), upper));
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
                let before = self.fresh_before();
                self.names.set_fresh(&x, None);
                self.bindings.remove(&x);
                self.orders.remove(&x);
                for upper in [false, true] {
                    self.direct.remove(&(x.clone(), upper));
                }
                self.seen_fresh(&x, before.as_ref());
            }
            Unbind::Saved(s) => *self = *s,
        }
    }

    /// The names before a fresh binding or unbinding, for [`Scope::seen_fresh`]: the exact map
    /// when it costs nothing to read ([`NameProducts::built`]), else `None`. `O(1)`.
    fn fresh_before(&self) -> Option<imbl::OrdMap<Arc<str>, Product>> {
        self.names.built().cloned()
    }

    /// Tells the caches of the last reduction, projection, enumeration and order of leaves
    /// ([`Order`]) that the fresh name `x` came into scope or left it, the names having been
    /// `before`. A fresh name is mentioned by no conjunct and no written constraint, and
    /// [`Scope::bind`] reduced its product to its fixed point, so a reduction would only have
    /// synchronized its bounds: the caches take it as reduced, and the next reduction costs the
    /// names that changed since, not every name bound since the last reduction of this scope.
    /// A walk reduces the scope of each test (a clone), never the scope it binds in, so without
    /// this a block of `d` bindings with a test in each cost `Θ(d²)` (repair of PA-let-block).
    ///
    /// Each cache is rebuilt from the names as they now are, with its own entries where it
    /// differed from `before`: a cache that shares the names' persistent nodes is compared
    /// with them in the entries that differ ([`changed`]), and one that took `x` by its own
    /// insertion would share none of them after a few bindings. The cost is the entries that
    /// differ, each `O(log n)`. With `before` `None` (names on difference paths whose exact
    /// map is not built), each cache takes `x`'s entry alone: the same map, since the names now
    /// are `before` with that entry, without building the exact map.
    fn seen_fresh(&mut self, x: &Arc<str>, before: Option<&imbl::OrdMap<Arc<str>, Product>>) {
        // Complexity tradeoff (COMPLEXITY.md PA-let-block): naive, the caches left as they
        // were, so each test diffs every name bound since the last reduction, Θ(k) at the k-th
        // binding and Θ(d²) over a block of d bindings; used, each cache rebased on the names
        // now, O(entries that differ · log n) per binding. Precondition: `x` is fresh, so its
        // product is already at its fixed point.
        //
        // With difference paths (item ST-walk-checker-admit): naive, the rebase above, which
        // reads the exact map, built in O(n log² n) for each version, so a test after each
        // fresh binding cost Theta(n log² n) and a chain Theta(n² log² n). Used, `x`'s entry
        // set in each cache, O(log n); the cache then shares no nodes with the exact map,
        // so the reduction that reads it after a refused test diffs it in O(n), which the
        // materialization of that test costs anyway.
        let x_now = before
            .is_none()
            .then(|| self.names.read(x).map(std::borrow::Cow::into_owned));
        let now = before.map(|_| self.names.view());
        let rebase = |cache: &mut imbl::OrdMap<Arc<str>, Product>| {
            let (Some(before), Some(now)) = (before, now) else {
                match x_now.as_ref().and_then(Option::as_ref) {
                    Some(p) => _ = cache.insert(x.clone(), p.clone()),
                    None => _ = cache.remove(x),
                }
                return;
            };
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
        // The order of an eager scope's leaves ([`Order::sync`]) is such a cache too; `x`, in
        // no conjunct, is no star's leaf, so the order has nothing to place for it. A lazy
        // scope keeps no order, and its empty one would cost every name to rebase.
        if !self.lazy {
            rebase(&mut self.seen.order.names);
        }
        // Stating the bounds of `x`, a name of no conjunct, adds no conjunct, so the relation
        // the paths were admitted against is still the relation; it is marked again, since the
        // records may be written in a new copy of the conjunction (`Relation::state_fresh`),
        // and the next difference test would otherwise be refused (item
        // ST-walk-checker-admit).
        let at = (self.names.relation.as_ref()).is_some_and(|m| self.relation.at(m));
        let (below, above) = sides(self.names.read(x).as_deref());
        let gapped = self.off_paths(x);
        self.relation.state_fresh(x, below, above, gapped);
        if at {
            self.names.relation = Some(self.relation.mark());
        }
    }

    /// The summary of `e`, an integer bound to a name of product `p` ([`let_summary`]), over
    /// the names it reads, made when first read ([`Lazy`]): those bound by `let`s with a
    /// summary that holds are read through it, and the others are inputs. It keeps the
    /// integers of its inputs here as the scope's names, and the orders of their bindings as
    /// the scope's orders, each a copy in `O(1)` of a persistent map. Made, it costs `e`'s size
    /// and the domains of the inputs it reads itself, not the summaries of the names it reads
    /// ([`Scope::inputs_and_lets`]), beside checking that those hold ([`Scope::holds`]).
    fn summarize(&self, e: &Shared, p: &Product) -> Lazy {
        if !self.summarizes(p) {
            return Lazy::made(None);
        }
        Lazy::pending(e, self.basis())
    }

    /// The parts of this scope a summary reads ([`View::summarize_free`]): the names and the
    /// bindings with their orders (a summary keeps its own last reads, `Held::last`). `O(1)`.
    fn basis(&self) -> Parts {
        Parts {
            names: self.names.clone(),
            bindings: self.bindings.clone(),
            orders: self.orders.clone(),
        }
    }

    /// Whether a name of product `p` bound here keeps a summary: an integer in a reachable
    /// scope.
    fn summarizes(&self, p: &Product) -> bool {
        !self.bottom && p.ty.element.subtype(&Type::int())
    }

    /// The parts of this scope the summaries of its bindings read ([`View`]).
    fn view(&self) -> View<'_> {
        View {
            names: &self.names,
            bindings: &self.bindings,
            orders: &self.orders,
            bottom: self.bottom,
        }
    }

    /// [`View::holds`] here.
    fn holds(&self, held: &Arc<Held>) -> bool {
        self.view().holds(held)
    }

    /// [`View::inputs_and_lets`] here.
    fn inputs_and_lets(
        &self,
        free: &BTreeSet<Arc<str>>,
        all: bool,
    ) -> (Domains, Lets, Option<Weak<Held>>) {
        self.view().inputs_and_lets(free, all)
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

    /// Narrows again by each test of [`Scope::kept`] a case of which the products of now
    /// leave with no value ([`KeptTests::dead`]), looking only at the names whose products
    /// differ from those of `before`, the scope this one was narrowed from, until no trigger
    /// fires; then reduces with `reduce` when a test narrowed. So `x % 2 == 0` after
    /// `(x % 2 == 1 && y >= 0) || y <= -5` drops the first case, as the other order does. A
    /// trigger narrows only by a test that holds, so one that does not fire costs precision
    /// and nothing else.
    // Complexity tradeoff: naive, narrow again by every kept test after each test, O(k) for k
    // kept tests, Θ(k·m) for m tests; or by each kept test that reads a moved name, Θ(k·m)
    // still when m tests move one name k tests read (61 times the bytes at 8n,
    // `split_moved_often_scales`; 8.1 times with this method). Used: the names whose
    // products differ, from the diff of two persistent maps (`NameProducts::changed`, near
    // the number of changes), and for each the triggers that fire (`KeptTests::dead`,
    // O(log k + f)); a test is narrowed again only when a case of it is gone, so at most
    // once per case. A scope with no kept test pays one look at an empty map. The written
    // constraints: see [`Scope::written_dead`]; those looked at are the ones written since
    // `before` (the diff of two persistent maps) and those on a name fixed since.
    fn narrow_kept_again(&mut self, before: &Scope, reduce: fn(&mut Scope)) {
        let mut since = before.names.clone();
        let mut since_written = before.written.clone();
        while !self.bottom
            && !(self.kept.triggers.is_empty() && self.kept.fixed.names().next().is_none())
        {
            let moved = self.names.moved_since(&since);
            let vars: imbl::OrdSet<Arc<str>> = if moved {
                (self.kept.triggers.keys())
                    .chain(self.kept.fixed.names())
                    .cloned()
                    .collect()
            } else {
                imbl::OrdSet::new()
            };
            let names: BTreeSet<Arc<str>> = self.names.changed(&since, &vars).cloned().collect();
            let mut due = BTreeSet::new();
            for n in names.iter().filter(|n| self.kept.triggers.contains_key(*n)) {
                let p = self.get(n);
                let q = since.product(n);
                let class_moved = (q.as_ref())
                    .is_none_or(|q| q.cell.congruence.element != p.cell.congruence.element);
                self.kept.dead(n, &p, q.as_ref(), class_moved, &mut due);
            }
            if self.kept.fixed.names().next().is_some() {
                let mut ws: BTreeSet<Address> = BTreeSet::new();
                for d in since_written.diff(&self.written) {
                    if let DiffItem::Add(k, _) | DiffItem::Update { new: (k, _), .. } = d {
                        ws.insert(k.clone());
                    }
                }
                for n in &names {
                    let now = self.names.read(n).and_then(|p| p.value().cloned());
                    if now.is_some() && now != since.product(n).and_then(|q| q.value().cloned()) {
                        ws.extend(self.written_by.of(n).cloned());
                    }
                }
                self.written_dead(&ws, &mut due);
            }
            if due.is_empty() {
                return;
            }
            since = self.names.clone();
            since_written = self.written.clone();
            for k in due {
                let Some(t) = self.kept.forget(&k) else {
                    continue;
                };
                self.names.materialize();
                self.settle_test(&t.test);
                self.narrow(&t.test, true, &t.premises);
                if self.bottom {
                    break;
                }
            }
            reduce(self);
        }
    }

    /// Adds to `out` the kept tests with a case that a written constraint of `ws` leaves with
    /// no value: the case fixes each of its names the scope leaves open ([`KeptTest::points`]),
    /// and it gives a value other than `true` there, as an enumeration in the case would have
    /// ([`Scope::enumerate_on`], with no name open). A case that leaves a name of the
    /// constraint open is not looked at: in the case, enumeration would need that name's
    /// listed members, which the join does not keep.
    // Complexity tradeoff: naive, narrow again by every kept test after each write, or each
    // test reading a name of the constraint, Θ(|t|) a test, Θ(k·m·|t|) for k tests and m
    // writes. Used: the tests with a case that fixes the open name of the constraint fixed in
    // the fewest tests (`fixed`, a persistent map by name, O(log k) a name), since a case
    // must fix them all, and one evaluation of the constraint at each such case's point:
    // each pair of a case and a constraint is evaluated when the constraint is written, and
    // again only when one of its names is fixed, as the order that writes the constraint
    // first evaluates it in each case. A test whose case is found is narrowed again, once
    // per case. Tradeoff: a test fixed on the chosen name whose case leaves another open name
    // is looked at and passed over, O(c) for its c cases.
    fn written_dead(&self, ws: &BTreeSet<Address>, out: &mut BTreeSet<Address>) {
        for w in ws {
            let Some(free) = self.written.get(w) else {
                continue;
            };
            if !free.iter().all(|n| self.names.contains_key(n)) {
                continue;
            }
            let statics = self.statics_of(free);
            let open: Vec<&Arc<str>> = free.iter().filter(|n| !statics.contains_key(*n)).collect();
            let Some(least) = open.iter().min_by_key(|n| self.kept.fixed.count(n)) else {
                continue;
            };
            for k in self.kept.fixed.of(least) {
                let Some(t) = self.kept.tests.get(k).filter(|_| !out.contains(k)) else {
                    continue;
                };
                let dead = t.points.iter().any(|ps| {
                    let mut at = statics.clone();
                    at.extend((ps.iter()).filter(|(n, _)| free.contains(n)).cloned());
                    if !open.iter().all(|n| at.contains_key(*n)) {
                        return false;
                    }
                    let c = substitute(w.term(), &at);
                    stage::ends(&c)
                        && matches!(Evaluator::new(World::new()).run(&c),
                            Ok(v) if v != Value::Bool(true))
                });
                if dead {
                    out.insert(k.clone());
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
        self.seen.drop_blocks();
    }

    /// The static names among `names`, and their values.
    fn statics_of<'a>(
        &self,
        names: impl IntoIterator<Item = &'a Arc<str>>,
    ) -> BTreeMap<Arc<str>, Value> {
        names
            .into_iter()
            .filter_map(|n| {
                let v = self.names.read(n)?.value()?.clone();
                Some((n.clone(), v))
            })
            .collect()
    }

    /// `test` under the functions in scope it calls, and those they call in turn, each a `let`
    /// in the order of its binding, so that the preimage reads through the calls (DESIGN.md
    /// step L1.25); `None` when it calls none. A function that reads a name bound at or after
    /// its own binding, itself included, would read another binding here, so it is left
    /// unbound and the transfer stops at its call. The cost is the functions reached and
    /// their terms' sizes, each visited once.
    // Complexity tradeoff: naive version, the functions a test calls are followed along every
    // path of calls, exponential in the depth when each function calls the two before it (did
    // not finish in 120 s at 32 without the visited set). Used: a visited set of the functions
    // reached, each closed over once, O(functions reached + their sizes) per test. Tradeoffs:
    // the closed test is kept as a written constraint, so its size counts once per arm; the
    // preimage still recurses on the depth of the term (T2-mid), so the scaling test stops at
    // 256 levels. Test `l01_39_reduced_product::scaling::tests_read_through_the_functions_they_call_scale`;
    // COMPLEXITY.md row S24.
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
        self.names.product(name).unwrap_or_else(Product::top)
    }

    /// A warning for each question the integer solver left undecided while this scope was
    /// narrowed or projected, joined scopes included, in the order of [`Refused`]: by
    /// constraint, how it was asked, then cause, whatever order they were met in.
    pub fn warnings(&self) -> Vec<Warning> {
        (self.refusals.iter())
            .filter(|(r, _)| !matches!(r.cause, Cause::Looped(_)))
            .map(|(r, kept)| r.warning(kept))
            .collect()
    }

    /// The message of each test this scope was narrowed by whose `||` alternatives limit each
    /// other's ranges in a loop ([`Cause::Looped`]), which the checker rejects: its headline,
    /// then its steps and its repair. In the order of [`Refused`].
    pub fn looped(&self) -> Vec<Warning> {
        (self.refusals.iter())
            .filter(|(r, _)| matches!(r.cause, Cause::Looped(_)))
            .map(|(r, kept)| r.warning(kept))
            .collect()
    }

    /// Keeps `r`, a question the integer solver left undecided while this scope was narrowed or
    /// projected, once, with `kept`, the sets it left its variables. The same question asked
    /// again in this scope keeps the meet of the sets of each time, each of which holds every
    /// value the question allows here, so the sets do not depend on the order the questions
    /// were met in. `names` are the names of the scope its constraint mentions, under each of
    /// which it is found (`Scope::refused_by`): a question its text shows alike may be asked of
    /// an outer `x` and again of an inner `x` that shadows it, and is then found under both.
    /// O(log k) in the k refusals kept, O(m log m) in the m variables of `kept`, and O(n log k)
    /// for the n names. Every refused test and part of the relation is kept through here.
    pub fn refuse(&mut self, r: Refused, kept: Kept, names: &[Arc<str>]) {
        index_refused(&mut self.refused_by, &r, names);
        let kept = match self.refusals.get(&r) {
            Some(old) => kept_meet(old, &kept),
            None => kept,
        };
        self.refusals.insert(r, kept);
    }

    /// Each question the integer solver left undecided in this scope whose constraint mentions
    /// one of `names`, names of the scope (`x@k` for a binder elaboration renamed), by the
    /// binding: a question on an outer `x` is not found by an inner `x` that shadows it. Once
    /// each, in the order of [`Refused`], with the sets it left its variables. O(m log k + q
    /// log q) for m names among k questions and the q questions found (`Scope::refused_by`).
    pub fn refused_on<'n>(
        &self,
        names: impl IntoIterator<Item = &'n str>,
    ) -> Vec<(&Refused, &Kept)> {
        let mut found: Vec<&Refused> = (names.into_iter())
            .filter_map(|n| self.refused_by.get(n))
            .flatten()
            .collect();
        found.sort_unstable();
        found.dedup();
        (found.into_iter())
            .filter_map(|r| self.refusals.get_key_value(r))
            .collect()
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
    /// mentions, each leaf of a star at such a name, and each name of a conjunct one side
    /// holds alone. A stale leaf they do not differ at has one product, hubs, star and settled
    /// product on both sides, so it stays stale in the join, where settling it gives that
    /// product.
    ///
    /// An eager scope picks the same leaves, as if each were stale, and projects their stars
    /// again on each side (`Scope::refresh`): a star's projection may still be the one made
    /// before the case's tests on other terms of its names, and the join of two such sides
    /// would keep the coarser of the two.
    ///
    /// A name of a conjunct one side holds alone whose free conjuncts differ between the sides
    /// changes the core ([`Conjuncts::core`]) of each star of two hubs or more at it, so its
    /// leaf, of one product `L` on both sides, settles to `L` met with the projection `pA` of
    /// one side's core and `pB` of the other's, and the eager join holds `L ∩ (pA ∪ pB)`. The
    /// join's core is the disjunction of the sides' cores, whose projection is `pA ∪ pB`, but
    /// a core of two disjunctions or more is projected one disjunction at a time (S16), which
    /// may give a larger `pJ`: with `n - m >= -6 || n <= -8` on both sides, `n - m >= -8` on
    /// one and `n - m >= -6` on the other, the join's core holds the first disjunction and
    /// `n - m >= -8 || n - m >= -6`, and projects `x >= n && x >= -m` to `x >= -4`, where each
    /// side's core of one disjunction gives `x >= -3`. When the join's free conjuncts at each
    /// hub of the star's class hold those of one side `S`, with the hubs and the names of
    /// those conjuncts of one product on both sides, the join's core holds that side's and
    /// adds no disjunction to it, so `pJ ⊆ pS` and `pJ = pA ∪ pB`: the leaf is left as it is,
    /// and settling it in the join gives the eager product. Such a class costs the difference
    /// of its hubs' free conjuncts, not its leaves; the leaves of any other class are settled
    /// on both sides and the sides joined again. The two cases of `!(x >= n && x >= m)`,
    /// `x < n` and `x >= n && x < m`, hold `x` free at both hubs in the second, and join to
    /// the star `x < n || x < m` ([`Formula::either`]), so the join's free conjuncts at the
    /// hubs are the first case's.
    ///
    /// A leaf left stale whose star the join does not hold, or holds in another class, is
    /// settled on both sides too: the disjunction of the conjuncts the sides hold alone may
    /// mention a hub and a name that is no satellite, as `(z >= 0 && n + m <= -7) ||
    /// (z < 0 && n - m >= -30)` mentions `z`, so that the hubs no longer admit the star, and
    /// the join would read the leaf as a name of no star, which nothing settles.
    // Complexity tradeoff: naive version, the join is `Or(R∧A, R∧B)`, which copies the common
    // part R into each side, so k joins in a row cost 2^k connectives. Used: the conjuncts the
    // sides share are found by the difference of their persistent sets (`Conjuncts`) and kept
    // once; the rest becomes one `Formula::either` of the two remainders, with the equalities
    // both sides hold (Karr's join, `Scope::hull`); the cost follows the conjuncts the sides
    // differ in, and each join of differing sides adds one disjunction. Tradeoffs: no cap, so a
    // scope keeps every conjunct; a relation with disjunctions is decided by a greedy choice
    // with one level of lookahead (`Refusal::Disjuncts` where both fail) and projected per
    // disjunction (S16), not split into all its conjunctions. Splitting the blocks the join
    // touches is S29 (`conjuncts::Blocks::remove`). Tests in `l01_39_reduced_product::scaling`:
    // `narrowing_by_a_conjunction_of_disjunctions_scales` and
    // `a_join_keeps_the_equalities_of_its_sides_and_scales`; COMPLEXITY.md row S2.
    //
    // Complexity tradeoff (SETTLE-class-join): naive version, every leaf of a star at a name
    // of a conjunct one side holds alone is settled on both sides, O(k) block checks per join
    // on k stars at hubs `n`, `m` and O(k²) over a nest of k such joins. Used: only names held
    // differently or written on one side alone settle the stars at them; a name whose free
    // conjuncts differ settles the leaves of a class at it only when the join's free
    // conjuncts at the class's hubs hold neither side's, found by the difference of the
    // persistent sets after a first join, O((classes + differ) log n). Tradeoffs: a class
    // that fails the check costs its leaves as before, and a second `join_settled`; a class
    // that passes leaves its leaves stale in the join, settled when read. Tests:
    // `l01_39a_bit_words::scaling::reads_under_the_else_arms_of_satellites_of_two_hubs_scale`,
    // `l01_39_reduced_product::lazy::a_join_settles_the_leaves_whose_core_differs_as_settling_every_name_does`;
    // COMPLEXITY.md row C40.
    //
    // Complexity tradeoff (SETTLE-class-check-case): naive version, settle every stale leaf of
    // either side before the join, O(k) projections per join on k stale leaves. Used: the
    // stars and classes of each side against the first join's, by the difference of their
    // persistent maps, which the join copies from one side and changes where the sides
    // differ, so O((stars and classes changed) log n); only the leaves whose star is gone or
    // whose class changed are settled. Tradeoffs: a dropped star costs its leaves'
    // projections and a second `join_settled`, as a class that fails the check does. Tests:
    // `l01_39_reduced_product::lazy::a_join_settles_a_star_it_drops_or_whose_core_gains_a_disjunction`
    // (its random part against the enumeration of the hubs) and the `reads_under_the_else_arms`
    // scaling test above; COMPLEXITY.md row C40.
    pub fn join(&self, other: &Scope) -> Scope {
        if self.bottom {
            return other.clone();
        }
        if other.bottom {
            return self.clone();
        }
        let mut differ: BTreeSet<Arc<str>> = BTreeSet::new();
        // The names held differently or mentioned by a written constraint one side holds
        // alone, at which the core of every star ([`Conjuncts::core`]) may differ.
        let mut moved: BTreeSet<Arc<str>> = BTreeSet::new();

        for d in self.names.diff(&other.names) {
            let (DiffItem::Add(n, _)
            | DiffItem::Remove(n, _)
            | DiffItem::Update { old: (n, _), .. }) = d;
            moved.insert(n.clone());
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
            moved.extend(free.iter().cloned());
        }
        let free = |s: &Scope, n: &str| s.relation.free_set(n).cloned().unwrap_or_default();
        // The other names of conjuncts one side holds alone whose free conjuncts differ.
        let cored: Vec<Arc<str>> = (differ.iter())
            .filter(|n| !moved.contains(*n))
            .filter(|n| free(self, n).diff(&free(other, n)).next().is_some())
            .cloned()
            .collect();
        differ.extend(moved.iter().cloned());
        let mut leaves = differ.clone();
        let (mut a, mut b) = (self.clone(), other.clone());
        // Of two eager sides, the stars at a hub moved whose leaf the bound of the star's
        // family does not cut are at their projection on each side, which refreshing them
        // leaves as it is ([`Scope::moved_blocks`]); the others are refreshed.
        // Complexity tradeoff: naive version, every leaf hanging at each hub moved is
        // refreshed (C45), O(k) for `k` stars per join and O(k²) over a nest of `k` `if`s on
        // the hubs. Used: the leaves the family bounds cut ([`Scope::cut_leaves`]), O(F·p +
        // (c + 1) log k) per hub for `F` families and `c` leaves cut. A join with a lazy side
        // settles the leaves at a hub moved after the first join, below, as lazy stars are not
        // kept at their projection. COMPLEXITY.md row C49.
        let eager = !self.lazy && !other.lazy;
        for side in [&mut a, &mut b] {
            if eager {
                side.seen.order.sync(&side.relation, &side.names);
            }
            for n in &moved {
                if eager {
                    leaves.extend(side.cut_leaves(&side.relation, n));
                }
                leaves.extend(side.relation.around(n));
            }
        }
        a.refresh(&leaves);
        b.refresh(&leaves);
        let joined = Scope::join_refreshed(&a, &b);
        if joined.bottom {
            return joined;
        }
        let mut due: BTreeSet<Arc<str>> = BTreeSet::new();
        // The leaves whose star the join drops or holds in another class (see above), not
        // among the leaves settled already.
        for side in [self, other] {
            let (stars, classes) = (joined.relation.stars(), joined.relation.classes_of());
            for d in side.relation.stars().diff(stars) {
                if let DiffItem::Remove(x, _) = d {
                    due.insert(x.clone());
                }
            }
            for d in side.relation.classes_of().diff(classes) {
                if let DiffItem::Remove(x, _) | DiffItem::Update { old: (x, _), .. } = d {
                    due.insert(x.clone());
                }
            }
        }
        due.retain(|x| !leaves.contains(x));
        // Whether the join's free conjuncts at `h` hold those of side `s`.
        let within = |s: &Scope, h: &str| {
            (free(s, h).diff(&free(&joined, h)))
                .all(|d| matches!(d, imbl::ordset::DiffItem::Add(_)))
        };
        // Whether the join holds hub `h` as side `s` does: of one interval and class, with the
        // free conjuncts of `s` at it.
        let as_side = |s: &Scope, h: &Arc<str>| {
            let h = std::slice::from_ref(h);
            within(s, &h[0]) && joined.snapshot(h) == s.snapshot(h)
        };
        // A hub moved in a lazy join leaves the stars at it stale where the join holds it as
        // one side does, with that side's free conjuncts: each such star is that side's, whose
        // leaf is settled when read; otherwise each leaf at it is settled on both sides.
        // Complexity tradeoff (NARROW-or-order): naive version, every leaf hanging at each hub
        // moved settled on both sides, O(k) projections per join for k stars at the hub, and
        // O(k²) over k tests of `a_i >= n || a_i >= 5` on the hub `n`. Used: one comparison of
        // the hub's interval and class and one difference of its free conjuncts per side,
        // O(log n + c) for c conjuncts that differ; a hub the join holds unlike both sides
        // costs its leaves as before. COMPLEXITY.md row C54; test
        // `l01_39a_bit_words::scaling::a_hub_settles_its_scopes_in_time_linear_in_the_tests`.
        if !eager {
            for n in &moved {
                if [self, other].iter().any(|s| as_side(s, n)) {
                    continue;
                }
                for side in [self, other] {
                    due.extend(side.relation.hanging(n).flat_map(|g| conjuncts::names(g)));
                }
            }
        }
        let mut checked: BTreeSet<&conjuncts::Class> = BTreeSet::new();
        let at: Vec<&Arc<str>> = if eager {
            Vec::new()
        } else {
            moved.iter().collect()
        };
        for n in cored.iter().chain(at) {
            for side in [self, other] {
                for c in side.relation.classes_at(n) {
                    if !checked.insert(c) {
                        continue;
                    }
                    let hubs: BTreeSet<Arc<str>> = (c.iter())
                        .flat_map(|g| conjuncts::names(g))
                        .filter(|h| &**h != conjuncts::LEAF)
                        .collect();
                    if ![self, other]
                        .iter()
                        .any(|s| hubs.iter().all(|h| as_side(s, h)))
                    {
                        due.extend(self.relation.class_leaves(c).cloned());
                        due.extend(other.relation.class_leaves(c).cloned());
                    }
                }
            }
        }
        if due.is_empty() {
            return joined;
        }
        a.refresh(&due);
        b.refresh(&due);
        Scope::join_refreshed(&a, &b)
    }

    /// [`Scope::join_settled`] of two sides after [`Scope::refresh`], which may find one side
    /// empty: the join is then the other side.
    fn join_refreshed(a: &Scope, b: &Scope) -> Scope {
        match (a.bottom, b.bottom) {
            (true, _) => b.clone(),
            (_, true) => a.clone(),
            _ => a.join_settled(b),
        }
    }

    /// [`Scope::join`] of two sides that differ at no stale leaf.
    fn join_settled(&self, other: &Scope) -> Scope {
        // A name both sides share unchanged is its own join; the others are found by the
        // persistent maps' difference, which skips what they share.
        let mut names = self.names.view().clone();
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
        // are grouped. It states as well its bounds tighter than the other side's on the names both
        // sides' own conjuncts mention, which its relation need not hold either.
        let (a, b) = (
            self.stated(other, &mine, &theirs),
            other.stated(self, &theirs, &mine),
        );
        let mut relation = self.relation.clone();
        // The joined names as the relation reads them for its stars ([`Scope::sync_bounds`]):
        // only names among the seeds differ from `self`'s.
        for n in &seeds {
            let (below, above) = sides(names.get(n));
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
        let kept = self.kept.join(&other.kept);
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
        let mut seen = self.seen.clone();
        for d in self.projected.diff(&other.projected) {
            match d {
                DiffItem::Remove(k, _) => {
                    projected.remove(k);
                    seen.drop_part(k);
                }
                DiffItem::Update {
                    old: (k, (with, v)),
                    new: (_, (theirs, _)),
                } => {
                    if with != theirs {
                        projected.remove(k);
                        seen.drop_part(k);
                        continue;
                    }
                    let at = v
                        .iter()
                        .map(|(n, _, _)| {
                            let p = names.get(n).cloned().unwrap_or_else(Product::top);
                            (n.clone(), p.ints().clone(), framed_class(&p))
                        })
                        .collect();
                    projected.insert(k.clone(), (with.clone(), at));
                    // The kept block holds this side's products, which the record no longer
                    // shows, so the part is checked at the block's next projection.
                    seen.drop_part(k);
                }
                DiffItem::Add(..) => {}
            }
        }
        // A star projected on both sides as it is now is projected in the join: its projection
        // onto its hubs holds of each side's hubs, so of their hull ([`Order::projected`]).
        let unmarked: Vec<Arc<str>> = if self.lazy || other.lazy {
            Vec::new()
        } else {
            (self.seen.order.projected)
                .diff(&other.seen.order.projected)
                .filter_map(|d| match d {
                    DiffItem::Remove(x, _) | DiffItem::Update { old: (x, _), .. } => {
                        Some(x.clone())
                    }
                    DiffItem::Add(..) => None,
                })
                .collect()
        };
        for x in &unmarked {
            seen.order.projected.remove(x);
            seen.order.place(&relation, &names, x);
        }
        // This side's point, which goes with this side's last enumeration, kept below as the
        // join's: the constraints on a name the join changed are searched again, and the
        // others hold at it as they did on this side. The other side's values are not mixed
        // in, since this side's constraints need not hold at them.
        let exactly = self.exactly.clone();
        let mut refusals = self.refusals.clone();
        let mut refused_by = self.refused_by.clone();
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
        // Each name keeps the questions found under it on either side. The other side's index
        // is read where it differs from this side's, and a name's questions where they differ,
        // so a join costs O(d log k) for the d entries that differ, not the whole index.
        for d in self.refused_by.diff(&other.refused_by) {
            match d {
                DiffItem::Add(n, theirs) => {
                    refused_by.insert(n.clone(), theirs.clone());
                }
                DiffItem::Update {
                    old: (n, mine),
                    new: (_, theirs),
                } => {
                    let mut both = mine.clone();
                    for e in mine.diff(theirs) {
                        if let imbl::ordset::DiffItem::Add(r) = e {
                            both.insert(r.clone());
                        }
                    }
                    refused_by.insert(n.clone(), both);
                }
                DiffItem::Remove(..) => {}
            }
        }
        Scope {
            gaps: LowerGaps::default(),
            relation,
            written,
            written_by,
            kept,
            bottom: false,
            emptied: Emptied(false, self.emptied.1.clone()),
            enumerated,
            projected,
            exact: self.exact,
            exactly,
            refusals,
            refused_by,
            // Both sides narrow one scope, which bound the names; neither binds one the other
            // does not.
            bindings: self.bindings.clone(),
            orders: self.orders.clone(),
            clock: self.clock.max(other.clock),
            names: names.into(),
            // This side's reduced names and what it last projected and enumerated: the join
            // differs from them in what it changed.
            reduced: self.reduced.clone(),
            seen,
            // It goes with this side's last projection, as `seen` does.
            potential: self.potential.clone(),
            lazy: self.lazy || other.lazy,
            in_case: self.in_case && other.in_case,
            // A root a constraint failed at on either side is reported.
            rooted: self.rooted.clone().union(other.rooted.clone()),
            root_failures: self
                .root_failures
                .clone()
                .union(other.root_failures.clone()),
            spent: {
                // An entry either side spent is spent on the join, so that no later test
                // projects for it again on this path: a bound on the work, not a fact of the
                // products.
                // Complexity tradeoff: O(d log s) for the d entries spent on one side only, of
                // s spent, as the diff of `names` above; the naive version, the intersection,
                // would let each side of every later test spend the entry again.
                let mut spent = self.spent.clone();
                for d in self.spent.diff(&other.spent) {
                    if let imbl::ordset::DiffItem::Add(e) = d {
                        spent.insert(e.clone());
                    }
                }
                spent
            },
            direct: {
                // The join's states are either side's, so an end holds of them where both
                // sides hold one, as the looser of the two.
                // Complexity tradeoff: O(d log e) for the d ends that differ, of e, by the
                // maps' difference; the naive version, the two maps walked whole, costs every
                // name a test of one name bounded on this path.
                let mut direct = self.direct.clone();
                for d in self.direct.diff(&other.direct) {
                    match d {
                        DiffItem::Remove(k, _) => {
                            direct.remove(k);
                        }
                        DiffItem::Update {
                            old: (k, mine),
                            new: (_, theirs),
                        } => {
                            let looser = if k.1 {
                                mine.max(theirs)
                            } else {
                                mine.min(theirs)
                            };
                            direct.insert(k.clone(), looser.clone());
                        }
                        DiffItem::Add(..) => {}
                    }
                }
                direct
            },
        }
    }

    /// `mine`, the conjuncts of the relation the other side does not hold, with the finite
    /// bounds of each name `theirs` mentions and the relation does not, and, of each name both
    /// `mine` and `theirs` mention, the ends a test of that name alone gave it on this side
    /// ([`Scope::direct`]) where tighter than `other`'s bound.
    ///
    /// The second part keeps what a test of one name adds to a test the two sides take in
    /// opposite ways: the case `a < n && a >= 5`, whose relation is `a <= n - 1` alone and
    /// whose `a >= 5` is a test of `a` alone, joined with the case `a >= n`, gives `a >= n ||
    /// a >= 5` ([`Formula::either`] drops `a <= n - 1` against `a >= n`), where the relations
    /// alone give `true` and the join would forget both cases. The case's `n >= 6` is not
    /// stated: the relation gives it again from `a >= 5`, and with it `a` would be no star's
    /// leaf ([`Conjuncts::star`]). Nor is a bound the case derived from the relation, as `b >=
    /// 8` of the case `a + 2 * b == 1000` beside `a <= 2 || b >= 8`: the shared relation gives
    /// it again, and stated it would add one conjunct to the join at each such test. A bound
    /// no tighter than the other side's holds of the join's product of the name, so the
    /// disjunction does not need it.
    fn stated(&self, other: &Scope, mine: &[Arc<Formula>], theirs: &[Arc<Formula>]) -> Formula {
        let mut out: Vec<Formula> = Vec::new();
        let mut seen: BTreeSet<Arc<str>> = BTreeSet::new();
        // Complexity tradeoff: naive version, the atoms of each conjunct that mentions a name
        // were collected again for each name, O(s² log s) for one conjunct of s atoms over s
        // names, as the disjunction a nest of k excluded sides joins into (s near k). Used:
        // the atoms of each conjunct, collected once per call and looked up by its address,
        // O(s log s) in all; the conjuncts live in the relation for the whole call, and the
        // map is only looked up, never walked, so no answer changes. One set of atoms per
        // conjunct read. COMPLEXITY.md C51; test
        // `l01_39_reduced_product::nests::excluded_sides_cost_the_names_they_change`.
        let mut atoms_of: HashMap<*const Formula, BTreeSet<Atom>> = HashMap::new();
        // The names of `mine`, once each: O(s log s) for `s` atoms, as the loop below.
        let shared: BTreeSet<Arc<str>> = mine.iter().flat_map(|g| syms(g)).collect();
        let bound = |n: &Arc<str>, upper: bool, v: &Num| {
            let (x, v) = (Lin::atom(Atom::Sym(n.clone())), Lin::constant(v));
            Formula::Con(match upper {
                false => Con::ge(&x, &v),
                true => Con::ge(&v, &x),
            })
        };
        for n in theirs.iter().flat_map(|g| syms(g)) {
            if !seen.insert(n.clone()) {
                continue;
            }
            let Some((lo, hi)) = self.names.get(&n).and_then(|p| p.ints().bounds()) else {
                continue;
            };
            if shared.contains(&n) {
                let theirs = other.names.get(&n).and_then(|p| p.ints().bounds());
                for (upper, end) in [(false, theirs.map(|b| b.0)), (true, theirs.map(|b| b.1))] {
                    if let Some(v) = self.direct.get(&(n.clone(), upper))
                        && end.is_none_or(|e| match upper {
                            false => End::Fin(v.clone()) > *e,
                            true => End::Fin(v.clone()) < *e,
                        })
                    {
                        out.push(bound(&n, upper, v));
                    }
                }
                continue;
            }
            let x = Atom::Sym(n.clone());
            if self.relation.mentioning(&n).any(|g| {
                atoms_of
                    .entry(Arc::as_ptr(g))
                    .or_insert_with(|| g.atoms())
                    .contains(&x)
            }) {
                continue;
            }
            if let End::Fin(v) = lo {
                out.push(bound(&n, false, v));
            }
            if let End::Fin(v) = hi {
                out.push(bound(&n, true, v));
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
        self.assume_with(test, outcome, premises, Scope::reduce)
    }

    /// [`Scope::assume`] and [`Scope::assume_case`], each with its own `reduce`: a test
    /// [`Scope::extend_path`] admits edits the paths, and any other is narrowed by the solver,
    /// with no reduction after a row [`Scope::extend_threshold`] certified, since it leaves
    /// the products as they were and reducing would split every row again, Theta(n) a test.
    /// With the feature `preimage-ref`, an admitted test or certified row is compared with
    /// the solver's scope (`path_check`).
    fn assume_with(
        &self,
        test: &Term,
        outcome: bool,
        premises: &Premises,
        reduce: fn(&mut Scope),
    ) -> Scope {
        let mut s = self.clone();
        let admitted =
            s.extend_path(test, outcome, premises) || s.extend_pendant(test, outcome, premises);
        if admitted {
            if s.bottom {
                reduce(&mut s);
            }
        } else {
            s.names.materialize();
            s.settle_test(test);
            let plain = plain_test(test, &s);
            s.narrow(plain.as_ref().unwrap_or(test), outcome, premises);
            // A scope left with paths ends with sides of a conjunction the paths took, after a
            // reduction (`Scope::narrow_linear`), as a forward order of admitted tests does.
            // Complexity tradeoff: naive, reduce again, which materializes the paths and
            // solves every row, Θ(n) a test and Θ(n²) for a cycle given at once (s4 `cycle0`,
            // `cycle1`); used, no second reduction, O(1); the paths' products are exact by
            // the shortest-path argument of `NameProducts::hold` (Bellman 1958, Shostak
            // 1981). Measured 8.1 to 8.7 at 8n in every order (ST-walk-orders).
            let certified = (s.seen.extension.as_deref()).is_some_and(Extension::certified);
            if s.bottom || !s.names.implicit() && !certified {
                reduce(&mut s);
            }
        }
        s.narrow_kept_again(self, reduce);
        #[cfg(feature = "preimage-ref")]
        {
            let certified = |s: &Scope| s.seen.extension.clone().filter(|e| e.certified());
            let newly = match (certified(self), certified(&s)) {
                (None, Some(_)) => true,
                (Some(a), Some(b)) => !Arc::ptr_eq(&a, &b),
                _ => false,
            };
            if admitted || newly || s.names.implicit() {
                path_check::compare(&s, || {
                    path_check::as_reference(|| self.assume_with(test, outcome, premises, reduce))
                });
            }
        }
        s
    }

    /// A path of difference constraints whose projections share affine bounds.
    // Complexity tradeoff: naive version, `narrow` splits a disjunction into cases and
    // propagates the live arm over every name on the chain, Theta(n) per test. Used: a test
    // of one or two names with unit coefficients, or a two-armed `or` one of whose arms is a
    // bound its name's current interval already falsifies, edits the path representation
    // ([`NameProducts`]) in O(log n). For the `or`, the scope keeps what `narrow_linear`
    // keeps when one arm is dead: the relation gains the live arm's relation (the whole
    // test's when the arm is on one name), `refuse_looped` runs on the plain test, and an
    // end of a single name that moves is recorded in `direct`; checked step by step against
    // the solver's scopes on the lazy tests (products, bottom, relation and `direct` equal).
    // Tradeoffs: `refuse_looped` and `relation_of` are O(size of the test) per test; a
    // general incremental solve of difference constraints (Ramalingam, Song, Joskowicz and
    // Miller, "Solving systems of difference constraints incrementally", Algorithmica
    // 23(3), 1999) would admit more tests but keeps no shared interval per path.
    //
    // The checker's scopes (item ST-walk-checker-admit): naive, the scope of ST-walk-implicit
    // refused a lazy scope, one with bindings and a test with premises, which is every scope
    // of the checker (walk.rs starts from `Scope::lazy` and binds each name it reads to
    // `Var(itself)`; `Run::walk_arms` assumes under a premise), so there each test ran the
    // solver, Theta(n) a test and Theta(n^2) a chain. Used, the admission of round 3 of the
    // cross-review of ST-walk-implicit, taken further to lazy scopes:
    // - a name may be bound when it is bound to itself with no summary over another name
    //   (`Scope::self_bound`): a test narrowing it then reaches no other name through a
    //   binding (`Scope::through_terms` reads only a binding's term, `Var(n)` here);
    // - premises go on each name whose end the test's own meet moves
    //   (`NameProducts::rest_on`), main's rule; O(1) more a test;
    // - a lazy scope is admitted: no admitted conjunct leaves a stale leaf, since the path's
    //   products are its exact projection, which settling a star would only meet again; and
    //   `assume_case` and `reaches`, the lazy scope's entry points, try this first.
    // With the feature `preimage-ref`, `path_check` runs the solver beside each admitted test
    // and compares the scopes (`l01_39_reduced_product::path_check`).
    fn extend_path(&mut self, test: &Term, outcome: bool, prem: &Premises) -> bool {
        if self.bottom || self.exact || self.in_case || !self.written.is_empty() {
            return false;
        }
        #[cfg(feature = "preimage-ref")]
        if path_check::reference() {
            return false;
        }
        if self
            .names
            .blocker
            .as_ref()
            .is_some_and(|g| self.relation.set().contains(g))
        {
            return false;
        }
        let mut live_side = None;
        let c = if let Some(c) = path_con(test, outcome) {
            c
        } else if self.names.relation.is_some()
            && outcome
            && let Term::Prim(Prim::Or, sides) = test
            && sides.len() == 2
        {
            let (Some(a), Some(b)) = (path_con(&sides[0], true), path_con(&sides[1], true)) else {
                return false;
            };
            let dead = |c: &Con| {
                if c.lin.terms.len() != 1 {
                    return false;
                }
                let Some((Atom::Sym(n), k)) = c.lin.terms.first_key_value() else {
                    return false;
                };
                let Some(p) = self.names.product(n) else {
                    return false;
                };
                if p.ty.element != Type::int() || !p.premises().is_empty() {
                    return false;
                }
                let Some((lo, hi)) = p.ints().bounds() else {
                    return true;
                };
                let End::Fin(v) = (if k.is_positive() { hi } else { lo }) else {
                    return false;
                };
                (&(&Int::from(v) * k) + &c.lin.constant).is_negative()
            };
            if dead(&a) {
                live_side = Some(1);
                b
            } else if dead(&b) {
                live_side = Some(0);
                a
            } else {
                return false;
            }
        } else {
            return false;
        };
        if !matches!(c.lin.terms.len(), 1 | 2) {
            return false;
        }
        if self.names.relation.is_none() && c.lin.terms.len() == 1 {
            return false;
        }
        if let Some(relation) = &self.names.relation {
            if !self.relation.at(relation) {
                return false;
            }
        } else {
            if let Some(g) = self.relation.set().iter().find(|g| {
                !matches!(&***g,
                Formula::Con(c) if c.rel == Rel::Ge && c.lin.terms.len() == 1
                    && c.lin.terms.keys().all(|a| matches!(a, Atom::Sym(_))))
            }) {
                self.names.blocker = Some(g.clone());
                return false;
            }
        }
        let mut names = Clone::clone(&self.names);
        let mut positive = None;
        let mut negative = None;
        for (a, k) in &c.lin.terms {
            let Atom::Sym(n) = a else {
                return false;
            };
            if !self.self_bound(n) {
                return false;
            }
            if *k == Int::from(1) && positive.is_none() {
                positive = Some(n);
            } else if *k == Int::from(-1) && negative.is_none() {
                negative = Some(n);
            } else {
                return false;
            }
        }
        let held = names.pending.is_some();
        let result = match (positive, negative) {
            (Some(b), Some(a)) => names.link(a, b, &-&c.lin.constant, prem),
            (Some(n), None) => names.bound(n, true, &-&c.lin.constant, prem),
            (None, Some(n)) => names.bound(n, false, &c.lin.constant, prem),
            _ => None,
        };
        let Some(mut bottom) = result else {
            return false;
        };
        if held && !bottom {
            let Some(b) = names.pending_holds() else {
                return false;
            };
            bottom = b;
        }
        let end = |ns: &NameProducts, n: &Arc<str>, upper: bool| {
            let p = ns.product(n)?;
            let ints = p.ints();
            let (lo, hi) = ints.bounds()?;
            match if upper { hi } else { lo } {
                End::Fin(v) => Some(v.clone()),
                _ => None,
            }
        };
        if let Some(i) = live_side {
            let plain = plain_test(test, self);
            let t = plain.as_ref().unwrap_or(test);
            let Term::Prim(Prim::Or, plain_sides) = t else {
                return false;
            };
            let Some(whole) = self.relation_of(t, outcome) else {
                return false;
            };
            let body = self.relation_of(&plain_sides[i], true).unwrap_or(whole);
            let (tree, pol) = Tree::of(t);
            self.refuse_looped(t, &tree, outcome == pol, outcome);
            self.relation.defer(body);
        } else if c.lin.terms.len() == 2 {
            self.relation.defer(Formula::Con(c.clone()));
        }
        if c.lin.terms.len() == 1 {
            let (n, upper) = match (positive, negative) {
                (Some(n), None) => (n, false),
                (None, Some(n)) => (n, true),
                _ => unreachable!("a unary constraint has one name"),
            };
            let (old, new) = (end(&self.names, n, upper), end(&names, n, upper));
            if let Some(v) = new
                && old.as_ref() != Some(&v)
            {
                self.direct.insert((n.clone(), upper), v);
            }
        }
        names.relation = Some(self.relation.mark());
        self.names = names;
        self.bottom = bottom;
        true
    }

    /// Admits `(x - y >= gap && y >= start) || y <= low`, `low < start`, on a leaf `y` no
    /// conjunct mentions yet ([`PendantRow`]): `y` becomes a pendant leaf of the hub `x`, which
    /// goes on a path of its own, and the row is held apart in the relation. Later tests on
    /// the hub that the paths admit then narrow every such leaf through its hub at no cost per
    /// leaf, and any other test materializes the products and runs the solver as before.
    // Complexity tradeoff (XR-hub-moved-relation): naive version, the row is split into its
    // two cases, each a copy of the scope reduced by the solver, and the cases are joined. The
    // first case raises the hub's lower end to `start + gap`, which makes every earlier row on
    // the hub due, so the k-th row projects k - 1 rows for nothing (the join restores the
    // hub): Θ(k²) over k rows. Then each test lowering the hub's upper end changes every
    // leaf, and an eager scope that holds each product writes k of them per test, Θ(k²) over
    // k tests (linear_moved: 60.7 times the bytes at 8n on main). Used: by the witness
    // argument of [`PendantRow`] the row narrows no hub and a leaf's product is its own met with
    // `(-inf, low] ∪ [start, H - gap]` for the hub's upper end `H`, so the leaf keeps its own
    // product and reads `H` when it is read, as a path member reads its root's interval
    // ([`NameProducts`]). A row costs O(log n) (one entry of the pendant map, the hub put on
    // a path, the row pushed on the relation's pending list) and a test on the hub O(log n)
    // (`NameProducts::bound`); reading a leaf O(log² n), the exact map O(n log² n) once per
    // version. The argument is the support argument of Freuder, "A sufficient condition for
    // backtrack-free search", JACM 29(1), 1982 (a tree of binary constraints, each arc
    // consistent, leaves every value reachable), here with the explicit witness `y <= low`
    // that holds with every hub value. The leaf's own product has two values at most `low`
    // and the hub two values at least, so the box of the second case gives the join no
    // affine equality (Karr's join, which the solver's path takes). Tradeoffs: the leaf must
    // be on no path, a pendant of no other row and in no other conjunct (the relation at the
    // mark of the last admission, or unary bounds alone), the test must hold under no
    // premises, and the leaf a plain integer interval with no premises; a later test on a
    // leaf, any test the paths refuse, or a write through `DerefMut` materializes every leaf
    // in O(k log² n) once and runs the solver, which projects each row once more. Measured
    // (`linear_moved_often_scales`, xst/s4.rs, k = 16 and 128): 8.2 times the instructions and
    // 8.1 times the bytes, against 60.7 times the bytes on main; the family at k = 64 allocates
    // 7.7 MB, against 3.87 GB on main (COMPLEXITY.md HUB-moved-relation).
    fn extend_pendant(&mut self, test: &Term, outcome: bool, prem: &Premises) -> bool {
        if self.bottom
            || self.exact
            || self.in_case
            || !self.written.is_empty()
            || !outcome
            || !prem.is_empty()
        {
            return false;
        }
        #[cfg(feature = "preimage-ref")]
        if path_check::reference() {
            return false;
        }
        if !matches!(test, Term::Prim(Prim::Or, sides) if sides.len() == 2) {
            return false;
        }
        if self
            .names
            .blocker
            .as_ref()
            .is_some_and(|g| self.relation.set().contains(g))
        {
            return false;
        }
        // The row as `narrow` and `narrow_linear` take it, so the relation holds the very
        // formula the solver's path adds.
        let plain = plain_test(test, self);
        let t = plain.as_ref().unwrap_or(test);
        let (tree, pol) = Tree::of(t);
        if !matches!(tree.nodes[0].kind, Kind::Nest(..)) {
            return false;
        }
        let Some(body) = self.relation_of(&tree.term_at(0), outcome == pol) else {
            return false;
        };
        let Some((leaf, row)) = pendant_row(&body) else {
            return false;
        };
        if let Some(relation) = &self.names.relation {
            if !self.relation.at(relation) {
                return false;
            }
        } else if let Some(g) = self.relation.set().iter().find(|g| {
            !matches!(&***g,
            Formula::Con(c) if c.rel == Rel::Ge && c.lin.terms.len() == 1
                && c.lin.terms.keys().all(|a| matches!(a, Atom::Sym(_))))
        }) {
            self.names.blocker = Some(g.clone());
            return false;
        }
        if !self.self_bound(&leaf) || !self.self_bound(&row.hub) {
            return false;
        }
        let mut names = Clone::clone(&self.names);
        if names.paths.contains_key(&leaf) || names.pendants.contains_key(&leaf) {
            return false;
        }
        let Some(p) = names.base.get(&leaf) else {
            return false;
        };
        if p.ty.element != Type::int()
            || classed(p)
            || listed(p).is_some()
            || !p.premises().is_empty()
            || p.cell.ints.element != Bounds::ints(p.ints().clone())
        {
            return false;
        }
        // Two values at most `low`: the witness of every hub value, and no equality.
        let Some((End::Fin(lo), hi)) = p.ints().only() else {
            return false;
        };
        if Int::from(lo) >= row.low {
            return false;
        }
        let hi = hi.clone();
        if names.member(&row.hub).is_none() {
            return false;
        }
        let Some(hub) = names.product(&row.hub) else {
            return false;
        };
        // Both cases live, as the solver's join of the two: a dead first case leaves the
        // test of one name `y <= low`, whose moved end the solver records ([`Scope::direct`]).
        if !hub.premises().is_empty()
            || row.cap(hub.ints()).is_none()
            || hi < End::Fin(Num::from(&row.start))
        {
            return false;
        }
        names.pendants.insert(leaf, row);
        names.view = Some(Arc::new(OnceLock::new()));
        self.refuse_looped(t, &tree, outcome == pol, outcome);
        self.relation.defer(body);
        names.relation = Some(self.relation.mark());
        self.names = names;
        true
    }

    /// Whether `n` is not bound, or bound to itself (`Var(n)`) with no summary over another
    /// name, as the checker binds a name it reads (walk.rs `Ck::with_bound`): a test that
    /// narrows it then narrows no other name through a binding, since
    /// [`Scope::through_terms`] reads only a binding's term and its summary reads only `n`.
    /// A name bound to another's summary (`bind_summarized`) or to a function is refused.
    fn self_bound(&self, n: &Arc<str>) -> bool {
        self.bindings.get(n).is_none_or(|b| {
            b.function.is_none()
                && b.term
                    .as_deref()
                    .is_some_and(|t| matches!(t, Term::Var(m) if m == n))
                && b.summary.reads_only(n)
        })
    }

    /// Certifies a row `x + w <= a || y - w >= b` with a fresh non-hub endpoint.
    // Complexity tradeoff: splitting every row into reduced cases revisits all earlier rows,
    // O(n²) over a walk. At the hub's lower end, a fresh y's upper end extends every old
    // state, and the all-lower witness admits every y; for a fresh x, its lower end extends
    // every old state and the all-upper witness admits every x. Thus all non-hub values
    // remain attainable there. The all-upper witness at the hub's upper end still passes.
    // This is a certificate for the walk's shape (one hub, each row's other names new), not a
    // general incremental solver for such rows; any other row clears it and reduces as
    // before. Products and affine hulls are unchanged; keeping each whole row (deferred, see
    // [`Relation`]) and the set of used endpoints costs O(log n) a row, O(n log n) over the
    // walk. The argument is Freuder's ("A sufficient condition for backtrack-free search",
    // JACM 29(1), 1982): rows that join a tree of names, each arc consistent with the box,
    // leave every value of the box reachable without search. ST-walk-orders extends it to a
    // walk's start `v0 - w >= 1` (conjuncts of the hub and one name that hold at both
    // witnesses, kept as used) and to a forced row whose first case no point of the box
    // meets, which is `y - w >= b` and raises `y` alone; before, each ran the solver over
    // every row, Θ(n²) (14.4 at 8n in reverse). Measured, instructions at 8n over n: s4 walk
    // 8.1 to 9.97 in reverse, 6.5 to 8.1 at once, 10.2 to 10.4 forward, walk without its
    // start 8.3 to 9.75. The walk's last test, which no certificate covers, runs the solver
    // once over every row; the cross-review of ST-walk-implicit measured it at 79% of the
    // walk's work at 8n (allocator calls), which keeps the forward walk above 9.
    //
    // The checker's scopes (item ST-walk-checker-admit) are admitted as in
    // `Scope::extend_path`: lazy, names bound to themselves (`Scope::self_bound`), and
    // premises. Main splits the row into its cases `x + w <= upper` and `y - w >= lower` and
    // joins them; a meet adds its premises only when it narrows and a join keeps both sides'
    // (zedc-lattice `Entry::meet`, `Entry::join`), so a name rests on the row's premises when
    // one case narrows it, three comparisons of ends, O(1) a row. The second case never
    // narrows w, since `yh - wh >= lower` is checked below.
    fn extend_threshold(&mut self, body: &Formula, prem: &Premises) -> bool {
        if self.bottom || self.exact || self.in_case || !self.written.is_empty() {
            return false;
        }
        #[cfg(feature = "preimage-ref")]
        if path_check::reference() {
            return false;
        }
        let previous = match self.seen.extension.as_deref() {
            Some(Extension::Certified {
                hub,
                used,
                names,
                relation,
            }) if names.ptr_eq(&self.names) && self.relation.at(relation) => {
                Some((hub.clone(), used.clone()))
            }
            Some(Extension::Certified { .. }) => return false,
            Some(Extension::Coupled(g)) if self.relation.set().contains(g) => return false,
            _ => None,
        };
        let Some(row) = threshold::leaf_row(body) else {
            return false;
        };
        let threshold::LeafRow {
            x,
            y,
            hub: w,
            upper,
            lower,
        } = row;
        if previous
            .as_ref()
            .is_some_and(|(hub, used)| *hub != w || (used.contains(&x) && used.contains(&y)))
            || ![&x, &y, &w].into_iter().all(|n| self.self_bound(n))
        {
            return false;
        }
        let unary = |g: &Arc<Formula>| {
            matches!(&**g, Formula::Con(c)
            if c.rel == Rel::Ge && c.lin.terms.len() == 1
                && c.lin.terms.keys().all(|a| matches!(a, Atom::Sym(_))))
        };
        let int = Type::int();
        let ends = |n: &Arc<str>| {
            let p = self.names.read(n)?;
            if p.ty.element != int || classed(&p) || listed(&p).is_some() {
                return None;
            }
            let (End::Fin(lo), End::Fin(hi)) = p.ints().only()? else {
                return None;
            };
            (lo < hi).then(|| (Int::from(lo), Int::from(hi)))
        };
        let (Some((xl, xh)), Some((wl, wh)), Some((yl, yh))) = (ends(&x), ends(&w), ends(&y))
        else {
            return false;
        };
        if &yh - &wh < lower {
            return false;
        }
        let forced = &xl + &wl > upper;
        // A first row may follow conjuncts of the hub and one other name `z`, `c z + d w + k
        // >= 0` with `d < 0`, that hold at both witnesses: the all-lower point (`zl`, `wl`) and
        // the all-upper point (`zh`, `wh`). Each is antitone in `w`, so lowering `w` keeps it,
        // and the box of the products is their exact projection: `w = v` is met at the
        // all-upper point with `w` lowered to `v`; `z = v` at the all-lower point with `z`
        // raised to `v` when `c >= 0`, and when `c < 0` since `c v + d wl >= c zh + d wh`. So
        // the argument above holds for the rows after them, with `z` taken as used: such a
        // `z` may be a row's `x` or `y`, but not both. This is the start test `v0 - w >= 1` a
        // walk gives before its rows (ST-walk-orders).
        let mut base = Vec::new();
        if previous.is_none() {
            for g in self.relation.set().iter().filter(|g| !unary(g)) {
                let z = match &**g {
                    Formula::Con(c) if c.rel == Rel::Ge && c.lin.terms.len() == 2 => c
                        .lin
                        .terms
                        .iter()
                        .find_map(|(a, k)| match a {
                            Atom::Sym(z) if *z != w => Some((z, k, c)),
                            _ => None,
                        })
                        .filter(|_| {
                            c.lin
                                .terms
                                .get(&Atom::Sym(w.clone()))
                                .is_some_and(|d| d.is_negative())
                        }),
                    _ => None,
                };
                let held = z.and_then(|(z, k, c)| {
                    let (zl, zh) = ends(z)?;
                    let d = c.lin.terms.get(&Atom::Sym(w.clone()))?;
                    let at = |zv: &Int, wv: &Int| &(&(k * zv) + &(d * wv)) + &c.lin.constant;
                    (!at(&zl, &wl).is_negative() && !at(&zh, &wh).is_negative()).then_some(z)
                });
                match held {
                    Some(z) => base.push(z.clone()),
                    None => {
                        self.seen.extension = Some(Arc::new(Extension::Coupled(g.clone())));
                        return false;
                    }
                }
            }
        }
        let fresh = |n: &Arc<str>| {
            !base.contains(n) && previous.as_ref().is_none_or(|(_, u)| !u.contains(n))
        };
        if !fresh(&x) && !fresh(&y) || forced && !fresh(&y) {
            return false;
        }
        // A row whose first case no point of the box meets (`xl + wl > a`, as each row of a
        // walk after its start `v0 - w >= 1`: `v0 >= 1` kills `v0 + w <= 0`, and the row
        // raises `v1` to 1, which kills the next row's first case) is `y - w >= b` on the box.
        // With `y` fresh it raises `y`'s lower end to `b + wl` and nothing else: an old point
        // with `y` raised to `yh` meets it, as the all-lower point with `y` at any value of
        // its new interval does, and the all-upper point still holds it, so the argument above
        // holds after it. Main's join is its second case alone, which narrows `y` with the
        // row's premises and not `w`, since `yh - wh >= b`.
        if forced {
            let lo = &lower + &wl;
            if lo > yl {
                let d = IntervalSet::range(End::Fin(Num::from(&lo)), End::PosInf);
                self.meet_name(&y, &d, true, prem);
            }
        } else {
            for (n, narrowed) in [
                (&x, &xh + &wl > upper),
                (&w, &wh + &xl > upper),
                (&y, &yl - &wl < lower),
            ] {
                if narrowed {
                    self.names.rest_on(n, prem);
                }
            }
        }
        let mut used = previous.map_or_else(|| base.into_iter().collect(), |(_, used)| used);
        // A forced row keeps its live case alone, as `narrow_linear` does for a nest a case of
        // which no point meets.
        let kept = match body {
            Formula::Or(arms) if forced => arms.iter().find(|a| {
                a.cons()
                    .iter()
                    .any(|c| c.lin.terms.contains_key(&Atom::Sym(y.clone())))
            }),
            _ => None,
        };
        self.relation.defer(kept.unwrap_or(body).clone());
        used.insert(x);
        used.insert(y);
        self.seen.extension = Some(Arc::new(Extension::Certified {
            hub: w,
            used,
            names: self.names.view().clone(),
            relation: self.relation.mark(),
        }));
        true
    }

    /// [`Scope::assume`] for a scope that is read and not shown: one no state reaches keeps its
    /// names as they were, with `bottom` set, and [`Scope::get`] gives the bottom for each, so
    /// that a test that fails costs what it narrows and not the names in scope. A nest of `k`
    /// tests that each fail in one case, on `k` names, is then `O(k)` narrowings and not
    /// `O(k²)` (`Scope::reduce_case`).
    pub fn assume_case(&self, test: &Term, outcome: bool, premises: &Premises) -> Scope {
        self.assume_with(test, outcome, premises, Scope::reduce_case)
    }

    /// Whether some state may reach this scope where `test` gave `outcome`: false only when
    /// [`Scope::assume_case`] would be bottom, and then not always, since the test's relation
    /// taken whole is not kept. A test that splits into cases, as `!(a >= n && a >= m)`, stops
    /// at the first case some state reaches and joins none: a join reads the relation of
    /// both cases, which under `k` stars at a hub is `k` conjuncts. With the answer, the
    /// refusals of the narrowed copy, those of this scope among them, so that the caller can
    /// report the questions the test asked (DESIGN.md L1.39): a refused question never shows a
    /// case empty, so it can only make the answer true.
    pub fn reaches(
        &self,
        test: &Term,
        outcome: bool,
        premises: &Premises,
    ) -> (bool, imbl::OrdMap<Refused, Kept>) {
        if self.bottom {
            return (false, self.refusals.clone());
        }
        let mut s = self.clone();
        // A test `Scope::extend_path` admits has no cases, so it is answered as
        // `Scope::assume_case` answers it, O(log n).
        if s.extend_path(test, outcome, premises) {
            #[cfg(feature = "preimage-ref")]
            path_check::compare_value((!s.bottom, s.refusals.clone()), || {
                path_check::as_reference(|| self.reaches(test, outcome, premises))
            });
            return (!s.bottom, s.refusals);
        }
        s.settle_test(test);
        let plain = plain_test(test, &s);
        let (tree, pol) = Tree::of(plain.as_ref().unwrap_or(test));
        let value = outcome == pol;
        let split = match &tree.nodes[0].kind {
            Kind::Nest(and, _) => *and != value,
            Kind::If(_) => true,
            _ => false,
        };
        match split {
            // The first case some state may reach, with what it refused; with none, the
            // questions of the cases shown empty changed no answer.
            true => match s.cases(&tree, 0, value, premises, true, &mut Vec::new()) {
                Some(case) => (true, case.refusals),
                None => (false, s.refusals),
            },
            false => {
                s.narrow_node(&tree, 0, value, premises);
                s.reduce_case();
                (!s.bottom, s.refusals)
            }
        }
    }

    /// Whether some state may reach this scope where the integer `t` is 0, as
    /// [`Scope::reaches`] answers it for `t == 0`, with the roots at which a written constraint
    /// gave neither `true` nor `false`. When `t` is a polynomial in one open integer name `x`,
    /// its other names of one value each read as constants, `x`'s members are first met with
    /// the integer roots of `t` in `x`'s interval, a listed set (DESIGN.md sec:constraints,
    /// QUESTIONS A81), so that each written constraint on `x` alone is evaluated at each root
    /// (`Scope::enumerate`) and a root it rules out is not reached. The solutions of a
    /// congruence are not listed: only the roots of `t` are.
    ///
    /// Sound under overflow: the program's `t` is 0 only where the polynomial is, since an
    /// operation that overflows gives `#overflow` and not a number, so the states where `t` is
    /// 0 are among those at the roots.
    ///
    /// Complexity tradeoff: the naive method evaluates each constraint at each member of `x`'s
    /// interval, O(w) for w members (10^9 for `p: int[0..10^9]`), and an interval of no bound
    /// is never done. Used: the integer roots of a sparse polynomial of t terms, whose
    /// coefficients have at most B bits, in time polynomial in t and B and not in the degree
    /// (Cucker, Koiran and Smale, "A polynomial time algorithm for Diophantine equations in one
    /// variable", J. Symbolic Comput. 27 (1999)), [`zed_kernel::poly::roots::integer_roots`];
    /// then one evaluation of each constraint on `x` at each of the at most t distinct roots
    /// the algorithm leaves after its gap split, and O(1) for a `t` with no root. Given up: a
    /// polynomial in two or more open names, whose integer roots are not a finite list in
    /// general (Hilbert's tenth problem for several variables); `Scope::reaches` answers it.
    pub fn zero_reached(&self, t: &Term, premises: &Premises) -> (bool, imbl::OrdSet<RootFailure>) {
        if self.bottom {
            return (false, imbl::OrdSet::new());
        }
        let test = Term::Prim(Prim::Eq, vec![t.clone(), Term::Lit(Value::Int(0))]);
        let mut s = self.clone();
        s.settle_test(&test);
        let int = Type::int();
        let free = stage::free(t);
        let statics = s.statics_of(&free);
        let open: Vec<&Arc<str>> = (free.iter())
            .filter(|n| !statics.contains_key(*n))
            .collect();
        if let [x] = open[..]
            && let Some(p) = s.names.get(x)
            && p.ty.element.subtype(&int)
        {
            let constant = |n: &str| match statics.get(n)? {
                Value::Int(k) => Some(BigInt::from(*k)),
                _ => None,
            };
            let ints = p.ints().clone();
            let end = |e: &End| e.to_i64().map(BigInt::from);
            let (lo, hi) = match ints.bounds() {
                Some((lo, hi)) => (end(lo), end(hi)),
                None => return (false, imbl::OrdSet::new()),
            };
            let roots = term_roots(t, x, &constant, lo.as_ref(), hi.as_ref());
            let listed: Option<Vec<i64>> = match roots {
                Some(Roots::Listed(rs)) => {
                    rs.iter().map(i64::try_from).collect::<Result<_, _>>().ok()
                }
                _ => None,
            };
            if let Some(rs) = listed {
                let rs: Vec<i64> = rs.into_iter().filter(|&r| ints.contains(r)).collect();
                if rs.is_empty() {
                    return (false, imbl::OrdSet::new());
                }
                let p = s.names.get_mut(x).expect("a name in scope");
                let prem = p.premises();
                p.cell
                    .finite
                    .meet(&FiniteSet::of(rs.iter().map(|&r| Value::Int(r))), &prem);
                p.meet_ints(
                    IntervalSet::from_pieces(
                        rs.iter().map(|&r| (End::of(r), End::of(r))).collect(),
                    ),
                    &prem,
                );
                s.rooted.insert(x.clone());
            }
        }
        let plain = plain_test(&test, &s);
        let (tree, pol) = Tree::of(plain.as_ref().unwrap_or(&test));
        s.narrow_node(&tree, 0, pol, premises);
        s.reduce_case();
        (!s.bottom, s.root_failures)
    }

    /// Narrows by `test`, read by [`plain_test`], giving `outcome`. The test is read as a
    /// [`Tree`]; when it has cases, the linear relation of the whole test, taken before any
    /// narrowing, is kept with the join of the cases, which keeps only what the cases share.
    fn narrow(&mut self, test: &Term, outcome: bool, prem: &Premises) {
        if self.bottom {
            return;
        }
        // No aggregate exists for a bare upper sum. Avoid constructing its
        // second relation before lower_gap_test declines it; a later lower
        // clause will synchronize the sum from the actual relation.
        if !self.exact
            && !self.in_case
            && lower_gap_syntax(test)
            && (!matches!(test, Term::Prim(Prim::Le, _)) || !self.gaps.pairs.is_empty())
            && let Some(body) = self.relation_of(test, outcome)
            && self.lower_gap_test(&body, prem)
        {
            return;
        }
        let (tree, pol) = Tree::of(test);
        self.refuse_looped(test, &tree, outcome == pol, outcome);
        self.narrow_linear(&tree, 0, outcome == pol, prem);
    }

    /// Keeps the refusal of `test`, whose tree is `tree` and whose root gives `value`, when its
    /// `||` alternatives limit each other's ranges in a loop (DESIGN.md step L1.39, the class
    /// of S4; [`loops::check`]): the checker rejects it ([`Cause::Looped`]). The scope is still
    /// narrowed as before, which is sound. Tradeoff: DESIGN names S4, the greatest fixed point of
    /// projection, promotion and join, as the narrowing of a test in the class; this keeps
    /// [`Scope::narrow_linear`], which keeps the test's linear relation and narrows a part by
    /// narrowing each case and joining them ([`Scope::cases`], COMPLEXITY.md C42), with no
    /// fixed-point loop of its own. Within the class no join narrows a bound twice (DESIGN
    /// L1.39), so a loop of S4's steps is expected to add nothing; measured, the arms of the eight
    /// in-class tests of `l01_39_reduced_product::loops` have exactly the least and greatest
    /// values that enumeration over `-6..=6` finds, both outcomes, every name (that test checks
    /// it). Equality with S4 on every in-class test is not proved here. A test with no choice of two alternatives, the most
    /// common, is passed over after one look at the root and its sides; any other costs
    /// O(s + N log N) for `s` nodes and `N` atom terms.
    fn refuse_looped(&mut self, test: &Term, tree: &Tree, value: bool, outcome: bool) {
        if let Some(r) = self.looped_refusal(test, tree, value, outcome) {
            self.refuse(r, Arc::new(BTreeMap::new()), &[]);
        }
    }

    /// The refusal [`Cause::Looped`] of `test` giving `outcome` in this scope, as the checker
    /// reports it at each `if` whose condition joins tests by `&&`, `||` or `!` (DESIGN.md step
    /// L1.39: the class depends on the test as written, so a test outside it is rejected
    /// whether or not its arms are read); none when the test is in the class. The scope gives
    /// the names' ranges. Costs what `Scope::refuse_looped` does.
    pub fn looped_test(&self, test: &Term, outcome: bool) -> Option<Refused> {
        if self.bottom {
            return None;
        }
        let mut s = self.clone();
        s.settle_test(test);
        let plain = plain_test(test, &s);
        let t = plain.as_ref().unwrap_or(test);
        let (tree, pol) = Tree::of(t);
        s.looped_refusal(t, &tree, outcome == pol, outcome)
    }

    /// The refusal [`Scope::refuse_looped`] keeps, or none.
    fn looped_refusal(
        &self,
        test: &Term,
        tree: &Tree,
        value: bool,
        outcome: bool,
    ) -> Option<Refused> {
        // The parts: each node with its value whose sides or arms are alternatives.
        let unforced = |n: usize, v: bool| match &tree.nodes[n].kind {
            Kind::Nest(and, _) => *and != v,
            Kind::If(_) => true,
            Kind::Lit(_) | Kind::Atom => false,
        };
        type Sides = Vec<(usize, bool)>;
        let (base_nodes, part_nodes): (Sides, Sides) = match &tree.nodes[0].kind {
            Kind::Nest(and, sides) if *and == value => (sides.iter())
                .map(|&(k, p)| (k, value == p))
                .partition(|&(k, v)| !unforced(k, v)),
            _ if unforced(0, value) => (Vec::new(), vec![(0, value)]),
            _ => return None,
        };
        if part_nodes.is_empty() {
            return None;
        }
        // The tree orders the sides of a nest by form ([`Tree`]); a message lists them as
        // written: by where each node's term comes in a walk of the test, which holds every
        // node's term. O(s log s) for `s` connectives and tests.
        let mut at: BTreeMap<*const Term, usize> = BTreeMap::new();
        let mut walk = vec![test];
        while let Some(t) = walk.pop() {
            let i = at.len();
            at.entry(t as *const Term).or_insert(i);
            match t {
                Term::Prim(Prim::And | Prim::Or | Prim::Not, a) => walk.extend(a.iter().rev()),
                Term::If(c, a, b) => walk.extend([&**b, &**a, &**c]),
                _ => {}
            }
        }
        let place = |n: usize| at.get(&(tree.nodes[n].term as *const Term)).copied();
        let (mut base_nodes, mut part_nodes) = (base_nodes, part_nodes);
        base_nodes.sort_by_key(|&(n, _)| place(n));
        part_nodes.sort_by_key(|&(n, _)| place(n));
        // Each text a message may print, as the nodes it joins by `&&` with their values: built
        // into a term only when printed, so a test in the class copies no term.
        let mut texts: Vec<Vec<(usize, bool)>> = Vec::new();
        // Whether every atom gathered is read as linear atoms.
        let gather = |n: usize,
                      v: bool,
                      out: &mut Vec<(usize, Lin)>,
                      texts: &mut Vec<Vec<(usize, bool)>>| {
            let mut whole = true;
            let mut stack = vec![(n, v)];
            while let Some((n, v)) = stack.pop() {
                match &tree.nodes[n].kind {
                    Kind::Lit(_) => whole = false,
                    Kind::Atom => {
                        let t = tree.nodes[n].term;
                        let lins = self.atom_lins(t, v);
                        whole &= !lins.is_empty();
                        for l in lins {
                            texts.push(vec![(n, v)]);
                            out.push((texts.len() - 1, l));
                        }
                    }
                    Kind::Nest(_, sides) => stack.extend(sides.iter().map(|&(k, p)| (k, v == p))),
                    Kind::If([(c, pc), (a, pa), (b, pb)]) => {
                        whole = false;
                        stack.extend([(*c, *pc), (*c, !*pc), (*a, v == *pa), (*b, v == *pb)]);
                    }
                }
            }
            whole
        };
        let mut base = Vec::new();
        let mut kept = Vec::new();
        for &(k, v) in &base_nodes {
            gather(k, v, &mut base, &mut texts);
            texts.push(vec![(k, v)]);
            kept.push(texts.len() - 1);
        }
        let mut parts = Vec::new();
        for &(n, v) in &part_nodes {
            // Each case: a node and its value, or for an `if` its condition and an arm.
            let cases: Vec<Vec<(usize, bool)>> = match &tree.nodes[n].kind {
                Kind::Nest(_, sides) => {
                    let mut sides = sides.clone();
                    sides.sort_by_key(|&(k, _)| place(k));
                    sides.iter().map(|&(k, p)| vec![(k, v == p)]).collect()
                }
                Kind::If([(c, pc), (a, pa), (b, pb)]) => vec![
                    vec![(*c, *pc), (*a, v == *pa)],
                    vec![(*c, !*pc), (*b, v == *pb)],
                ],
                Kind::Lit(_) | Kind::Atom => unreachable!("a part has alternatives"),
            };
            let mut cs = Vec::new();
            for case in cases {
                let mut atoms = Vec::new();
                let mut whole = true;
                for &(k, w) in &case {
                    whole &= gather(k, w, &mut atoms, &mut texts);
                }
                texts.push(case.clone());
                cs.push(loops::Case {
                    text: texts.len() - 1,
                    atoms,
                    whole,
                });
            }
            texts.push(vec![(n, v)]);
            parts.push(loops::Part {
                text: texts.len() - 1,
                cases: cs,
            });
        }
        let mut boxes = BTreeMap::new();
        let lins = (base.iter().map(|(_, l)| l)).chain(
            parts
                .iter()
                .flat_map(|p| p.cases.iter().flat_map(|c| c.atoms.iter().map(|(_, l)| l))),
        );
        for l in lins {
            for a in l.terms.keys() {
                let Atom::Sym(n) = a else { continue };
                boxes.entry(n.clone()).or_insert_with(|| {
                    let x = self.get(n).ints().clone();
                    let end = |e: &End| e.to_i64().map(i128::from);
                    let (lo, hi) = x.bounds().map_or((None, None), |(l, h)| (end(l), end(h)));
                    (lo, hi, format!("int{x}"))
                });
            }
        }
        let t = loops::Test {
            base,
            kept,
            parts,
            boxes,
        };
        let text = |i: usize| {
            let shown: Vec<Term> = (texts[i].iter())
                .map(|&(k, w)| negated_if(tree.nodes[k].term, !w))
                .collect();
            let t = balanced(Prim::And, shown);
            let free = stage::free(&t);
            plain_text(&t, &|u| {
                print::written(u, written_name, &|x| free.contains(x))
            })
        };
        let l = loops::check(&t, outcome, &text)?;
        let free = stage::free(test);
        let constraint: Arc<str> = print::written(test, written_name, &|x| free.contains(x)).into();
        Some(Refused {
            constraint,
            asked: Asked::Test { outcome },
            cause: Cause::Looped(Arc::new(l)),
        })
    }

    /// The atoms `lin >= 0` of `t` giving `value`, a comparison of linear sums of this scope's
    /// integer names and literals: one for `<`, `<=`, `>`, `>=`, two for `==`, and none for
    /// `!=`, which narrows no bound, or for any other test. O(the size of `t`).
    fn atom_lins(&self, t: &Term, value: bool) -> Vec<Lin> {
        let Term::Prim(p, a) = t else {
            return Vec::new();
        };
        let [x, y] = &a[..] else { return Vec::new() };
        let p = if value {
            *p
        } else {
            match p {
                Prim::Lt => Prim::Ge,
                Prim::Le => Prim::Gt,
                Prim::Gt => Prim::Le,
                Prim::Ge => Prim::Lt,
                Prim::Eq => Prim::Ne,
                Prim::Ne => Prim::Eq,
                _ => return Vec::new(),
            }
        };
        let (Some(x), Some(y)) = (self.lin_of(x), self.lin_of(y)) else {
            return Vec::new();
        };
        let d = x.minus(&y);
        let one = Int::from(1i64);
        let shifted = |l: Lin, by: &Int| Lin {
            constant: &l.constant - by,
            ..l
        };
        match p {
            Prim::Ge => vec![d],
            Prim::Gt => vec![shifted(d, &one)],
            Prim::Le => vec![d.times(-1i64)],
            Prim::Lt => vec![shifted(d.times(-1i64), &one)],
            Prim::Eq => vec![d.clone(), d.times(-1i64)],
            _ => Vec::new(),
        }
    }

    /// `t` as a linear sum of this scope's integer names, a name of one value read as its
    /// value; `None` for any other term. O(the size of `t` times the names it holds).
    fn lin_of(&self, t: &Term) -> Option<Lin> {
        let int = Type::int();
        Some(match t {
            Term::Lit(Value::Int(k)) => Lin::constant(Int::from(*k)),
            Term::Var(n) => {
                let p = self.names.read(n)?;
                if !p.ty.element.subtype(&int) {
                    return None;
                }
                match p.value() {
                    Some(Value::Int(k)) => Lin::constant(Int::from(*k)),
                    Some(_) => return None,
                    None => Lin::atom(Atom::Sym(n.clone())),
                }
            }
            Term::Prim(Prim::Neg, a) if a.len() == 1 => self.lin_of(&a[0])?.times(-1i64),
            Term::Prim(p @ (Prim::Add | Prim::Sub), a) if a.len() == 2 => {
                let (x, y) = (self.lin_of(&a[0])?, self.lin_of(&a[1])?);
                if *p == Prim::Add {
                    x.plus(&y)
                } else {
                    x.minus(&y)
                }
            }
            Term::Prim(Prim::Mul, a) if a.len() == 2 => {
                let (x, y) = (self.lin_of(&a[0])?, self.lin_of(&a[1])?);
                match (x.terms.is_empty(), y.terms.is_empty()) {
                    (true, _) => y.times(x.constant.clone()),
                    (_, true) => x.times(y.constant.clone()),
                    _ => return None,
                }
            }
            _ => return None,
        })
    }

    /// Narrows by the sides of a root conjunction giving `value`, in the order given, when
    /// each is narrowed exactly: by the paths ([`Scope::extend_path`]), as a row
    /// [`Scope::extend_threshold`] certifies, or, when some side is a nest or an `if`, as an
    /// atom the solver takes (`Scope::atom`), the scope being reduced after the atoms before
    /// the next row and at the end. `false` when a side is none of these, with the scope
    /// possibly changed; the caller then goes back to the scope it had before the conjunction
    /// ([`Scope::narrow_linear`]).
    fn sides_exactly(
        &mut self,
        tree: &Tree,
        sides: &[(usize, bool)],
        value: bool,
        prem: &Premises,
    ) -> bool {
        let nests = |k: usize| matches!(tree.nodes[k].kind, Kind::Nest(..) | Kind::If(_));
        let atoms_solved = sides.iter().any(|&(k, _)| nests(k));
        let mut unreduced = false;
        for &(k, p) in sides {
            let v = value == p;
            if self.bottom {
                return true;
            }
            if self.extend_path(&tree.term_at(k), v, prem) {
                continue;
            }
            if !nests(k) {
                if !atoms_solved {
                    return false;
                }
                self.names.materialize();
                self.narrow_node(tree, k, v, prem);
                unreduced = true;
                continue;
            }
            if unreduced {
                self.reduce_case();
                unreduced = false;
                if self.bottom {
                    return true;
                }
            }
            self.names.materialize();
            let Some(body) = self.relation_of(&tree.term_at(k), v) else {
                return false;
            };
            if !self.extend_threshold(&body, prem) {
                return false;
            }
        }
        if unreduced {
            self.reduce_case();
        }
        true
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
        // Complexity tradeoff: naive, a root nest the value forces whose test has a relation is
        // narrowed as one node (`narrow_node`), which splits each `or` side into cases and
        // joins them against the whole relation: a walk of n rows `v_i + w <= 0 || v_{i+1} - w
        // >= 1` given as one conjunction takes Θ(n) per row and Θ(n²) in all (measured 44 to
        // 85 at 8n on main, ST-walk-orders). Used: first the sides one by one, each narrowed
        // exactly ([`Scope::sides_exactly`]): by the paths, or as a row `extend_threshold`
        // certifies (Freuder, "A sufficient condition for backtrack-free search", JACM 29(1),
        // 1982: a tree of constraints that are arc consistent is solved without search), or
        // as an atom the solver takes; O(s log s) for a test of `s` nodes, plus the
        // certification of each row, as in the forward order. A conjunction with a side none
        // of these takes goes back to the scope before it (one clone of persistent maps, O(1))
        // and is narrowed as before, so it costs at most its narrowing twice. Measured at 8n,
        // instructions: the walk 6.5 to 8.1 at n = 5 to 40, without its start 8.6 to 9.6,
        // the chains with a cycle (s4 `cycle0`, `cycle1`) 8.1 to 8.5.
        if let Kind::Nest(and, sides) = &tree.nodes[n].kind
            && *and == value
            && n == 0
        {
            // The sides in the tree's order of rank, and among one rank in the order the test
            // gives them: the tree numbers a root's sides from its last to its first
            // ([`Tree::of`]), where its own order sorts them by form, so that a walk's rows
            // would come in the order of their names' texts (`v1`, `v10`, `v11`, ..., `v2`),
            // each joining two names that rows before it hold and no row certified.
            let mut ordered = sides.clone();
            ordered.sort_by_key(|&(k, _)| (tree.nodes[k].rank, std::cmp::Reverse(k)));
            let saved = self.clone();
            if self.sides_exactly(tree, &ordered, value, prem) {
                return;
            }
            *self = saved;
        }
        let body = match &tree.nodes[n].kind {
            Kind::Nest(..) | Kind::If(_) => self.relation_of(&tree.term_at(n), value),
            Kind::Lit(_) | Kind::Atom => None,
        };
        if body
            .as_ref()
            .is_some_and(|body| self.extend_threshold(body, prem))
        {
            return;
        }
        if self
            .seen
            .extension
            .as_deref()
            .is_some_and(Extension::certified)
        {
            self.seen.extension = None;
            self.reduce();
        }
        let Some(body) = body else {
            match &tree.nodes[n].kind {
                Kind::Nest(and, sides) if *and == value && n == 0 => {
                    for &(k, p) in sides {
                        self.narrow_linear(tree, k, value == p, prem);
                    }
                }
                _ => self.narrow_kept(tree, n, value, prem, Watch::Cases),
            }
            return;
        };
        let before = self.relation.clone();
        let body = match &tree.nodes[n].kind {
            Kind::Nest(and, sides) if *and != value => {
                // A nest the value does not force: its relation is that of the sides with a
                // case that is not bottom, when some side has none. So `n + m >= -1 ||
                // m - n >= 15` where the products hold `m - n <= 11` keeps `n + m >= -1`, a
                // constraint, not a disjunction a later projection would have to meet with
                // the others at the hubs (S16 projects one disjunction at a time).
                // Complexity tradeoff: naive, keep the whole test's relation, O(1) more, and a
                // dead side's disjunction is left for a later projection, which settles a
                // lazy star coarser than the eager product; here, the sides' liveness comes
                // from the cases already narrowed, and a second relation is taken only when a
                // side is dead, of the live sides alone: O(s) for a test of `s` nodes, no
                // further case and no projection (COMPLEXITY.md C42).
                let mut live = Vec::new();
                let cases = self.case_list(tree, n, value, prem, false, &mut live);
                let body = if live.contains(&false) && live.contains(&true) {
                    let terms: Vec<Term> = sides
                        .iter()
                        .zip(&live)
                        .filter(|(_, l)| **l)
                        .map(|(&(k, p), _)| signed(tree.term_at(k), p))
                        .collect();
                    let p = if *and { Prim::And } else { Prim::Or };
                    self.relation_of(&balanced(p, terms), value).unwrap_or(body)
                } else {
                    body
                };
                self.join_kept(cases, signed(tree.term_at(n), value), prem, Watch::Points);
                body
            }
            _ => {
                self.narrow_kept(tree, n, value, prem, Watch::Points);
                body
            }
        };
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
                    .read(n)
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

    /// [`Scope::narrow_node`], keeping the test when it splits: a nest the value does not
    /// force, or an `if`, is split into its cases, which are joined and the test kept as
    /// [`Scope::join_kept`] does, watched by `watch`.
    fn narrow_kept(&mut self, tree: &Tree, n: usize, value: bool, prem: &Premises, watch: Watch) {
        let splits = match &tree.nodes[n].kind {
            Kind::Nest(and, _) => *and != value,
            Kind::If(_) => true,
            Kind::Lit(_) | Kind::Atom => false,
        };
        if !splits || self.bottom {
            return self.narrow_node(tree, n, value, prem);
        }
        let cases = self.case_list(tree, n, value, prem, false, &mut Vec::new());
        self.join_kept(cases, signed(tree.term_at(n), value), prem, watch);
    }

    /// Becomes the join of `cases`, the cases of `test` that are not bottom (bottom when
    /// there are none), and, with two cases or more, keeps `test` in [`Scope::kept`] with
    /// what `watch` names of its cases, when that is not empty: the join keeps only what the
    /// cases share, so a later test may leave one case where the join kept two.
    // Complexity tradeoff: naive, the cases joined and the test forgotten, as with a
    // relation-free nest before ST-class-case-reverse, and with any test the linear relation
    // holds before ST-relation-case-written: O(c) cases, and the order of the tests changes
    // the answer (a written constraint after `(x == 3 && y == 0) || x <= -5` left 3). Used:
    // the same cases, kept unjoined until the join, plus O(c·v) triggers for v names the
    // test reads and the points of the cases in time near the entries consecutive cases
    // differ in ([`case_points`]), each put in the persistent index in O(log k); a test the
    // relation holds takes points alone ([`Watch::Points`]), so it adds nothing to the index
    // when no case fixes a name, as with the rows of a walk, and a later move of an end, a
    // class or a hole narrows it through the relation's projection, not by narrowing it again.
    fn join_kept(&mut self, cases: Vec<Scope>, test: Term, prem: &Premises, watch: Watch) {
        let in_case = self.in_case;
        if cases.len() < 2 {
            match cases.into_iter().next() {
                Some(s) => *self = s,
                None => self.bottom = true,
            }
            self.in_case = in_case;
            return;
        }
        let free: Vec<Arc<str>> = stage::free(&test).into_iter().collect();
        let joined = self.join_preserving_outer(cases.clone());
        let triggers = match watch {
            Watch::Cases => case_triggers(&cases, &free, &joined),
            Watch::Points => Vec::new(),
        };
        let points = case_points(self, &cases, &free, &joined);
        *self = joined;
        self.in_case = in_case;
        if !self.bottom && !(triggers.is_empty() && points.is_empty()) {
            self.kept.keep(KeptTest {
                test,
                free,
                premises: prem.clone(),
                triggers,
                points,
            });
        }
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
            Kind::Nest(..) | Kind::If(_) => {
                match self.cases(tree, n, value, prem, false, &mut Vec::new()) {
                    Some(mut s) => {
                        s.in_case = self.in_case;
                        *self = s;
                    }
                    None => self.bottom = true,
                }
            }
        }
    }

    /// The join of [`Scope::case_list`], or `None` when it is empty.
    fn cases(
        &self,
        tree: &Tree,
        n: usize,
        value: bool,
        prem: &Premises,
        any: bool,
        live: &mut Vec<bool>,
    ) -> Option<Scope> {
        let out = self.case_list(tree, n, value, prem, any, live);
        (!out.is_empty()).then(|| self.join_preserving_outer(out))
    }

    // Complexity tradeoff: naive version, when a case constraint replaces a block's least
    // constraint (`x - j * y >= 1 < x + y >= -1000` in Arm 2 of `persist`), that case removes
    // `(old_least, leaf)` from its `projected` map, so `join_refreshed` drops the outer record
    // even when the joined scope returns to the outer constraint set and unchanged hub domains
    // (`30` redundant `project_each` calls on Star and Free at k = 16, Gemini seat, round 3).
    // Used: restore outer `self.projected` entries missing from `s.projected` whose key formula
    // remains in `s.relation`, whose hubs match `outer_snap`, and whose star leaf (whose
    // half-line bound depends only on the hubs) narrowed monotonically within a single contiguous
    // unclassed interval; `Scope::is_projected` still checks `outer_with == p.with` at the next
    // block update. Reference: P. Cousot and R. Cousot, "Systematic design of program analysis
    // frameworks", POPL '79, 1979, pp. 269-282 (monotone fixed-point preservation across joins).
    fn join_preserving_outer(&self, cases: Vec<Scope>) -> Scope {
        let mut s = join_cases(cases);
        if s.bottom {
            return s;
        }
        let mut restores: Vec<(PartKey, (PartWith, Projected))> = Vec::new();
        for d in self.projected.diff(&s.projected) {
            let DiffItem::Remove(k, (outer_with, outer_snap)) = d else {
                continue;
            };
            if !s.relation.set().contains(&k.0) {
                continue;
            }
            if let Some(leaf) = &k.1
                && s.relation.star(leaf).is_none()
            {
                continue;
            }
            let mut ok = true;
            let mut updated_snap: Vec<(Arc<str>, IntervalSet, Congruence)> =
                Vec::with_capacity(outer_snap.len());
            for (n, outer_ints, outer_cls) in outer_snap.iter() {
                let p = s.get(n);
                let cls = framed_class(&p);
                if k.1.as_ref() == Some(n) {
                    if classed(&p)
                        || &cls != outer_cls
                        || outer_ints.only().is_none()
                        || p.ints().only().is_none()
                        || !p.ints().is_subset(outer_ints)
                    {
                        ok = false;
                        break;
                    }
                } else if p.ints() != outer_ints || &cls != outer_cls {
                    ok = false;
                    break;
                }
                updated_snap.push((n.clone(), p.ints().clone(), cls));
            }
            if ok {
                restores.push((k.clone(), (outer_with.clone(), updated_snap.into())));
            }
        }
        for (k, val) in restores {
            s.projected.insert(k, val);
        }
        s
    }

    /// The cases of node `n` giving `value` that are not bottom, in the order they are made.
    /// A nest the value does not force has a case per side, each starting from this scope
    /// with the sides before it excluded from the names' products ([`Scope::exclude`]); an
    /// `if` has the case of each arm. A nest the value forces narrows by each side but the one
    /// of the most nodes that has cases, whose cases are the nest's: so a chain of nests is
    /// one list of cases, joined in pairs ([`join_cases`]), and only a side of at most half a
    /// nest's nodes is narrowed by a call within this one. With `any`, the first case some
    /// state reaches, unjoined ([`Scope::reaches`]).
    ///
    /// When node `n` is a nest the value does not force, `live` is set to one entry per side,
    /// in the order of the sides: whether some case of the side is not bottom. A side whose
    /// cases are all bottom, or that is not reached because the sides before it, excluded,
    /// leave nothing, holds at no state of this scope that no side before it holds; so the
    /// test holds where the live sides do ([`Scope::narrow_linear`]). Otherwise `live` is left
    /// empty. Complexity tradeoff: naive, a side's liveness found by narrowing a copy of the
    /// scope by the side alone, one more case per side; here it is read off the cases this
    /// walk makes anyway, O(1) per case and O(s) for the root's `s` sides (COMPLEXITY.md
    /// C42). A side is dead only when its cases are, with the products as narrowed here.
    fn case_list(
        &self,
        tree: &Tree,
        n: usize,
        value: bool,
        prem: &Premises,
        any: bool,
        live: &mut Vec<bool>,
    ) -> Vec<Scope> {
        let root = n;
        live.clear();
        let mut out = Vec::new();
        // Each case with the side of the root it comes from, when the root has sides.
        let mut start = self.clone();
        start.in_case = true;
        let mut work = vec![(start, n, value, None)];
        while let Some((mut s, n, v, top)) = work.pop() {
            if s.bottom {
                continue;
            }
            match &tree.nodes[n].kind {
                Kind::Nest(and, sides) if *and != v => {
                    if n == root {
                        live.resize(sides.len(), false);
                    }
                    for (i, &(k, p)) in sides.iter().enumerate() {
                        let top = if n == root { Some(i) } else { top };
                        work.push((s.clone(), k, v == p, top));
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
                        Some((k, p)) => work.push((s, k, v == p, top)),
                        None if any && !s.bottom => return vec![s],
                        None => {
                            if let Some(i) = top {
                                live[i] |= !s.bottom;
                            }
                            out.push(s);
                        }
                    }
                }
                Kind::If([c, a, b]) => {
                    let mut t = s.clone();
                    t.narrow_node(tree, c.0, c.1, prem);
                    t.reduce_case();
                    work.push((t, a.0, v == a.1, top));
                    s.narrow_node(tree, c.0, !c.1, prem);
                    s.reduce_case();
                    work.push((s, b.0, v == b.1, top));
                }
                Kind::Lit(_) | Kind::Atom => {
                    s.narrow_node(tree, n, v, prem);
                    s.reduce_case();
                    if any && !s.bottom {
                        return vec![s];
                    }
                    if let Some(i) = top {
                        live[i] |= !s.bottom;
                    }
                    out.push(s);
                }
            }
        }
        out.retain(|s| !s.bottom);
        out
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
        // An equality with a literal, and the congruence of `x mod c == r`. The names whose
        // integers an equality narrows are read through their terms with the others below.
        let mut changed = Vec::new();
        if let Term::Prim(op @ (Prim::Eq | Prim::Ne), a) = &t
            && a.len() == 2
        {
            let equal = (*op == Prim::Eq) == outcome;
            for (l, r) in [(&a[0], &a[1]), (&a[1], &a[0])] {
                match (l, r) {
                    // Both sides of `==` have one carrier, so an `int` literal beside a name
                    // with no `int` value stands for a literal of the name's carrier that the
                    // term's maker read at `int`, as `1 + 1` in `r == 1 + 1` with `r: rat`;
                    // read as the `int`, it would empty the name where the test holds and drop
                    // that arm. Such a test narrows nothing (NARROW-ne-rat-divisor).
                    (Term::Var(x), Term::Lit(v)) if equal || !convex => {
                        if let Some(p) = self.names.get_mut(x)
                            && (int_lit(v).is_none() || !p.ty.element.subtype(&!&Type::int()))
                            && equality(p, v, equal, prem)
                        {
                            changed.push(x.clone());
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
                    // `x mod 2 != r` leaves the one other class; for a modulus above 2 the
                    // classes left are not one class, and the congruence keeps them all.
                    (Term::Prim(Prim::Mod, m), Term::Lit(r)) => {
                        if let [Term::Var(x), Term::Lit(c)] = &m[..]
                            && let (Some(r), Some(c)) = (int_lit(r), int_lit(c))
                            && c.abs() == Num::from(2)
                            && (r.is_zero() || r == Num::ONE)
                            && let Some(p) = self.names.get_mut(x)
                        {
                            let other = if r.is_zero() { 1 } else { 0 };
                            p.cell.congruence.meet(&Congruence::new(2, other), prem);
                        }
                    }
                    _ => {}
                }
            }
        }
        // An order test of a name against a `rat` literal that `0r` fails at this outcome, as
        // `r > 0r`, `r >= 1r` or the `else` of `r > -1r`, takes `0r` from the name, as the
        // `else` of `r == 0r` does (NARROW-ne-rat-divisor), so that a divisor the test keeps
        // from zero gives no `#divByZero`.
        // Complexity tradeoff: the complete method is an interval of rationals per name, a
        // domain the reduced product does not have, met at each test in the size of its ends
        // and joined at each arm's end; used: the one value a divisor needs, `0r`, read from
        // the literal's sign alone, O(1) per test whatever the literal's size, and the name's
        // type then excludes one value at most whatever the number of tests. Every other
        // order fact on a `rat` name is given up, as the reduced product gives it up today.
        if let Term::Prim(op @ (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge), a) = &t
            && a.len() == 2
        {
            let flipped = match op {
                Prim::Lt => Prim::Gt,
                Prim::Le => Prim::Ge,
                Prim::Gt => Prim::Lt,
                _ => Prim::Le,
            };
            for (l, r, op) in [(&a[0], &a[1], *op), (&a[1], &a[0], flipped)] {
                if let (Term::Var(x), Term::Lit(Value::Rat(q))) = (l, r)
                    && let Some(p) = self.names.get_mut(x)
                {
                    // Where `0r` lies beside the literal.
                    let side = match (q.is_zero(), q.is_negative()) {
                        (true, _) => std::cmp::Ordering::Equal,
                        (false, true) => std::cmp::Ordering::Greater,
                        (false, false) => std::cmp::Ordering::Less,
                    };
                    let holds = match op {
                        Prim::Lt => side.is_lt(),
                        Prim::Le => side.is_le(),
                        Prim::Gt => side.is_gt(),
                        _ => side.is_ge(),
                    };
                    if holds != outcome {
                        let zero = Value::rat(zed_kernel::Rat::int(0.into()));
                        if equality(p, &zero, false, prem) {
                            changed.push(x.clone());
                        }
                    }
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
                        .filter(|(n, _)| self.names.contains_key(n))
                        .map(|(n, d)| (n.clone(), d.clone()))
                        .collect(),
                );
                // The names read free in the test are in scope where it is written; a name it
                // binds in two places is read in a part through one value (`print::pretty_in`).
                let free = stage::free(written);
                let constraint: Arc<str> =
                    print::written(written, written_name, &|x| free.contains(x)).into();
                let names = mentioned(&constraint, free.iter().cloned());
                let r = Refused {
                    constraint,
                    asked: Asked::Test { outcome },
                    cause: cause.into(),
                };
                self.refuse(r, kept, &names);
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
            // Complexity tradeoff: naive version, each name met in place (`get_mut`), which
            // copies the map's path to it and the product's domains (`Arc::make_mut`) even
            // when the meet changes nothing; the later reduction then finds the name by the
            // maps' difference and compares the copied domains whole. A case of a nest
            // starts with the sides before it excluded, so the i-th case re-met up to
            // min(i, m) of the m names unchanged: O(k m) comparisons for k sides, quadratic
            // for k differences over k/4 names. Used: the meet made on a copy of the product
            // (one `Arc`) and put back only when it changed the interval (`Entry::meet`
            // reports every change): the same names, O(log m) per name changed and nothing
            // copied for one unchanged (COMPLEXITY.md C51). Test:
            // `l01_39_reduced_product::nests::excluded_sides_cost_the_names_they_change`.
            // A test of one name keeps the ends it moved ([`Scope::direct`]).
            let one = (inputs.len() == 1 && through.is_empty()).then(|| inputs[0].clone());
            let ends = |s: &Scope, n: &Arc<str>| {
                let b = s.names.get(n).and_then(|p| p.ints().bounds());
                b.map(|(l, h)| (l.clone(), h.clone()))
            };
            for (n, d) in pre.domains.iter().chain(&through) {
                let before = ends(self, n);
                if self.meet_name(n, d, convex, prem) {
                    changed.push(n.clone());
                    if one.as_ref() == Some(n)
                        && let (Some((lo0, hi0)), Some((lo, hi))) = (before, ends(self, n))
                    {
                        for (upper, moved, end) in [(false, lo > lo0, lo), (true, hi < hi0, hi)] {
                            if let (true, End::Fin(v)) = (moved, end) {
                                self.direct.insert((n.clone(), upper), v);
                            }
                        }
                    }
                }
            }
        }
        self.through_terms(changed, convex, prem);
        (exact, inputs, free)
    }

    /// Meets the integers of `n`, when in scope, with `d`, or its hull with `convex`; the
    /// product is put back only when the meet changed it ([`Scope::atom_names`]). Gives whether
    /// it did.
    fn meet_name(&mut self, n: &Arc<str>, d: &IntervalSet, convex: bool, prem: &Premises) -> bool {
        let Some(p) = self.names.get(n) else {
            return false;
        };
        let mut p = p.clone();
        let met = if convex {
            p.meet_ints(d.hull(), prem)
        } else {
            p.meet_ints(d.clone(), prem)
        };
        if met {
            self.names.insert(n.clone(), p);
        }
        met
    }

    /// Meets the integers of `n`, when in scope, with `x` on the premises its product rests
    /// on; the product is put back only when the meet changed it, as [`Scope::meet_name`] does.
    // Complexity tradeoff: naive version, the meet made in place (`get_mut`), which copies the
    // path to `n` and the product even when the meet changes nothing; a block kept many tests
    // ago ([`Block::update`]) then finds its names by a difference of the maps that skips only
    // what they share, and compares each copied product with the one it kept: Theta(t) per
    // update, Theta(n²) over the n tests of a family whose threshold rows are met each test
    // (s4 `walk`, 19.9 million product comparisons at n = 2560 against 0.34 million at 320).
    // Used: a copy of the product (one `Arc`), put back only when changed, as the reduction
    // does (COMPLEXITY.md row PA-bind-cost): O(log n) per meet, nothing copied when nothing
    // changes, and the difference walks the changes alone (ST-walk-orders; 0.14 million
    // comparisons at 2560, 17 thousand at 320; the s4 walk in reverse went from 14.4 to 9.6
    // times the instructions at 8n). The maps copy the path to a changed node and share the
    // rest (Driscoll, Sarnak, Sleator and Tarjan, "Making data structures persistent", JCSS
    // 38(1), 1989), so a difference is cheap only while unchanged nodes stay shared. Test:
    // `xst::s4::a_walk_narrows_in_near_linear_time_at_once_and_in_reverse`.
    fn meet_own(&mut self, n: &Arc<str>, x: IntervalSet) {
        let Some(p) = self.names.get(n) else {
            return;
        };
        let mut p = p.clone();
        let prem = p.premises();
        if p.meet_ints(x, &prem) {
            self.names.insert(n.clone(), p);
        }
    }

    /// Whether `n`, in scope, has no value: its type has none, or it is read through its term
    /// ([`Binding::term`], given only to bindings whose type holds integers alone) and has no
    /// integers. A meet of the integers changes the type only at the next reduction.
    fn no_value(&self, n: &Arc<str>) -> bool {
        let p = &self.names[n];
        p.is_empty()
            || (p.ints().is_empty() && self.bindings.get(n).is_some_and(|b| b.term.is_some()))
    }

    /// Narrows the inputs of the integer bindings among `changed`, names a test has just
    /// narrowed, that have no summary that holds ([`View::summary`]), by reading each one's
    /// term backward from its integers ([`let_narrowing`] of the demand of those integers), as
    /// a test reads a function it calls through its term ([`Scope::close`]): with `z = abs(x)`,
    /// `z > 5` narrows `x` to `..=-6, 6..`. The inputs a term narrows that are such bindings
    /// in turn are read the same way. A name is read only when every name its term reads was
    /// bound before it, so that each is still the binding the term read.
    ///
    /// A term reads only names bound before its own, so the bindings are read latest first
    /// from a heap by the order of their binding, a topological order of the bindings, and
    /// each is read at most once a test, after every binding that could narrow it. A name left
    /// with no value ends the reads: no state reaches the scope, which its reduction then
    /// finds, and reading on would empty every link before it, O(n) for each such arm.
    // Complexity tradeoff: naive version, each test closed over every binding it reaches, as
    // `Scope::close` does for functions, and the closed test read whole: O(size of the chain)
    // a test whatever it narrows, so k tests at each of n links of a chain cost Θ(k n²). Used:
    // only the bindings whose integers this test changed are read, each once (a visited set
    // and the heap's topological order), each costing its own term, O(m (s + log n)) a test
    // for m bindings changed, of terms of size s. Tradeoffs: a binding whose integers this
    // test leaves as they were is not read, since the test that last narrowed it read it
    // then; a test that narrows every link of a chain still costs every link, as the scope
    // then differs from the one before in all of them, so n such tests cost Θ(n²) reads, the
    // size of the narrowings they give. Tests
    // `l01_39_reduced_product::let_terms::reading_chains_of_terms_scales` (4n reads) and
    // `a_test_that_narrows_every_link_reads_every_link_once` (n(n+1) reads); COMPLEXITY.md
    // row PA-let-unsummarized-narrow.
    fn through_terms(&mut self, changed: Vec<Arc<str>>, convex: bool, prem: &Premises) {
        if changed.iter().any(|n| self.no_value(n)) {
            return;
        }
        let mut seen: BTreeSet<Arc<str>> = BTreeSet::new();
        let mut todo: BinaryHeap<(u64, Arc<str>)> = BinaryHeap::new();
        let push = |n: Arc<str>,
                    s: &Scope,
                    seen: &mut BTreeSet<Arc<str>>,
                    todo: &mut BinaryHeap<(u64, Arc<str>)>| {
            if let Some(&o) = s.orders.get(&n)
                && s.bindings.get(&n).is_some_and(|b| b.term.is_some())
                && seen.insert(n.clone())
            {
                todo.push((o, n));
            }
        };
        for n in changed {
            push(n, self, &mut seen, &mut todo);
        }
        let int = Type::int();
        while let Some((order, z)) = todo.pop() {
            if self.bottom {
                return;
            }
            let Some(e) = self.bindings.get(&z).and_then(|b| b.term.clone()) else {
                continue;
            };
            if self.view().summary(&z).is_some() {
                continue;
            }
            let later = |m: &Arc<str>| self.orders.get(m).is_some_and(|c| *c >= order);
            if stage::free(&e).iter().any(later) {
                continue;
            }
            let closed = self.close(&e);
            let e = closed.as_ref().map_or(&*e, |c| c);
            let statics = self.statics_of(stage::free(e).iter().filter(|n| {
                !self
                    .names
                    .get(*n)
                    .is_some_and(|p| p.ty.element.subtype(&int))
            }));
            let t = substitute(e, &statics);
            let (over, lets, _) = self.inputs_and_lets(&stage::free(&t), true);
            if over.is_empty() && lets.is_empty() {
                continue;
            }
            let reads: Vec<_> = lets.values().filter_map(|l| l.read.clone()).collect();
            let demand = Demand::Ints(self.get(&z).ints().clone());
            #[cfg(feature = "counts")]
            super::preimage::counts::TERM_READS.set(super::preimage::counts::TERM_READS.get() + 1);
            let narrowed = match let_narrowing(&t, &over, lets, &demand) {
                Some(narrowed) => narrowed,
                None => {
                    let vars = reads.iter().flat_map(|r| r.vars().iter());
                    (over.keys().chain(vars))
                        .map(|n| (n.clone(), IntervalSet::empty()))
                        .collect()
                }
            };
            for (n, d) in &narrowed {
                if self.meet_name(n, d, convex, prem) {
                    if self.no_value(n) {
                        return;
                    }
                    push(n.clone(), self, &mut seen, &mut todo);
                }
            }
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
    ///
    /// The names are found from those a copy of the scope last emptied, by the bindings that
    /// differ: the names of a scope are those it was made with and those it binds
    /// ([`Scope::bind`]), each binding in `orders`, so two scopes made from one differ in their
    /// names only where their orders differ.
    ///
    /// Complexity tradeoff: the naive emptying makes the bottom of each name, `O(n)` for `n`
    /// names, so that a walk showing an arm no state reaches below each of `d` nested
    /// bindings cost `Θ(d²)`. Here it costs the bindings that differ from the last emptied
    /// scope, found by the persistent maps' difference, each `O(log n)`, and `O(n)` only for
    /// the first. Given up: one emptied scope is kept, so emptyings alternating between two
    /// scopes far apart pay their difference each time; a result whose count of names is not
    /// the scope's is made afresh. Trigger: a scope no state reaches that is shown, as an arm
    /// of a walk. Test:
    /// `l01_39_reduced_product::if_shortcut::one_pass_and_transfer_scale_on_deep_nests`,
    /// COMPLEXITY.md row PA-walk-nest-cost.
    fn empty_if_bottom(&mut self) {
        if !self.bottom || self.emptied.0 {
            return;
        }
        let mut last = self
            .emptied
            .1
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let bottom = Product::bottom();
        let names = (last.as_ref())
            .map(|was| {
                let mut out = was.names.clone();
                for d in was.orders.diff(&self.orders) {
                    match d {
                        DiffItem::Add(n, _) if self.names.contains_key(n) => {
                            _ = out.insert(n.clone(), bottom.clone())
                        }
                        DiffItem::Remove(n, _) if !self.names.contains_key(n) => _ = out.remove(n),
                        _ => {}
                    }
                }
                out
            })
            .filter(|out| out.len() == self.names.len())
            .unwrap_or_else(|| {
                (self.names.keys())
                    .map(|n| (n.clone(), bottom.clone()))
                    .collect()
            });
        *last = Some(Emptying {
            orders: self.orders.clone(),
            names: names.clone(),
        });
        self.names = names.into();
        self.emptied.0 = true;
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
        // Whether the names may differ from `last`: not after a round whose enumeration
        // changed nothing, since `last` is the names just before it.
        //
        // Complexity tradeoff: naive version, the names are compared with `last` at the top of
        // each round and after the loop, and with those at the start of the round by a check
        // that no name rose and again by `==`: each a walk of the two maps' paths to the
        // changes, about 4,000 to 8,000 instructions on the 1,000 names of the fee test. Used:
        // the comparison with `last` is skipped when the enumeration reports no change, and the
        // check and `==` share one walk, O(changes) each as before, about 25,000 instructions a
        // binding fewer (COMPLEXITY.md row PA-bind-cost). Test:
        // `l01_39_reduced_product::deep_let::the_arms_of_a_deep_block_scale`.
        let mut moved_since = true;
        loop {
            if self.bottom || self.relation.is_bottom() {
                self.bottom = true;
                break;
            }
            // The names that differ from `last`, found by the walk that checks none is empty:
            // `since`, those the names have, taken below as those to reduce when nothing
            // between changed the names, and `differ`, those and the names gone, in key order,
            // taken as the names moved since the last projection when that projection was of
            // `last`.
            //
            // Complexity tradeoff: naive version, the names that differ from `last` found
            // three times a round, by the check that none is empty, for the names moved since
            // the last projection, and again after the projection: walks of the same two maps
            // when the last projection and the one now changed no name, about 9,000
            // instructions each a binding of the fee test. Used: the names the check found,
            // kept when the maps are those it walked (`ptr_eq`), the same names, O(changes) as
            // before (COMPLEXITY.md row PA-bind-cost). Test:
            // `l01_39_reduced_product::deep_let::the_arms_of_a_deep_block_scale`.
            let mut since = Vec::new();
            let mut differ = Vec::new();
            if moved_since {
                for d in last.diff(&self.names) {
                    let (n, keep_differ) = match d {
                        DiffItem::Add(n, p) => {
                            if p.empties() {
                                self.bottom = true;
                                break;
                            }
                            since.push(n.clone());
                            (n, true)
                        }
                        DiffItem::Update {
                            old: (_, a),
                            new: (n, p),
                        } => {
                            // Complexity tradeoff: naive version, a name is found empty by its
                            // type alone, which the reduction of its domains below empties
                            // only after the projection: an integer name a case empties by its
                            // interval, as `x0 < j + 1` where `x0 >= k` in the case of `y_j <=
                            // -1` of a chain raise in reverse, made every block that mentions
                            // the name due, O(k) blocks at each of `k` tests, Θ(k² log k).
                            // Used: the interval and the class read as the reduction would,
                            // O(1) more a name changed, and the case stops before its
                            // projection. Test:
                            // `l01_39_reduced_product::xst::s4::a_chain_raise_in_reverse_narrows_in_near_linear_time`,
                            // COMPLEXITY.md row ST-walk-orders.
                            if p.empties() {
                                self.bottom = true;
                                break;
                            }
                            since.push(n.clone());
                            (n, !same_framed(a, p))
                        }
                        DiffItem::Remove(n, _) => (n, true),
                    };
                    if keep_differ {
                        differ.push(n.clone());
                    }
                }
                if self.bottom {
                    break;
                }
            }
            let before = self.names.view().clone();
            // The names whose bounds may have changed since the last projection, so that the
            // stars it finds are those of the bounds as they are.
            let moved: Vec<Arc<str>> = match &self.seen.projection {
                Some((names, _)) if moved_since && names.ptr_eq(&last) => differ,
                Some((names, _)) => names
                    .diff(&self.names)
                    .filter_map(|d| match d {
                        DiffItem::Add(n, _) | DiffItem::Remove(n, _) => Some(n.clone()),
                        DiffItem::Update {
                            old: (_, a),
                            new: (n, b),
                        } => (!same_framed(a, b)).then(|| n.clone()),
                    })
                    .collect(),
                None => self.names.keys().cloned().collect(),
            };
            self.sync_bounds(&moved);
            // The names and conjuncts as projected are those before the projection, so that a
            // projection that moves a bound is followed by another, until none moves one.
            if let Some(due) = self.due(whole, force, &moved) {
                force = false;
                self.seen.projection = Some((self.names.view().clone(), (*self.relation).clone()));
                self.project(due, whole);
            }
            let dirty: Vec<Arc<str>> = if moved_since && self.names.ptr_eq(&before) {
                since
            } else {
                (changed(&last, &self.names))
                    .map(|(n, _)| n.clone())
                    .collect()
            };
            // Complexity tradeoff: naive version, each name reduced in place (`get_mut`), which
            // copies the map's path to it even when the reduction changes nothing, so the walks
            // that compare the names with `before` and `last`, here and at the next reduction,
            // walk that path: about 4,000 instructions for the copy and as many for each walk,
            // on the 1,000 names of the fee test. Used: the reduction made on a copy of the
            // product (one `Arc`), put back only when it changed a domain, which every change
            // of `reduce_domains` reports (each is an `Entry::meet`): the same names, the same
            // `O(log n)` a name changed, nothing copied for one unchanged (COMPLEXITY.md row
            // PA-bind-cost). Test: `l01_39_reduced_product::deep_let::the_arms_of_a_deep_block_scale`.
            for n in &dirty {
                if let Some(p) = self.names.get(n) {
                    let mut p = p.clone();
                    if p.reduce_domains() {
                        self.names.insert(n.clone(), p);
                    }
                }
            }
            last = self.names.view().clone();
            if dirty
                .iter()
                .any(|n| self.names.get(n).is_some_and(Product::is_empty))
            {
                self.bottom = true;
                break;
            }
            moved_since = self.enumerate();
            // `before == names` is the diff being empty (`imbl`'s `PartialEq`), so one walk
            // finds both that and, in a debug build, that no name rose.
            let mut same = true;
            for d in before.diff(&self.names) {
                same = false;
                debug_assert!(
                    matches!(d, DiffItem::Update { old: (_, a), new: (_, b) } if b.leq(a)),
                    "a reduction rose"
                );
                if !cfg!(debug_assertions) {
                    break;
                }
            }
            if same {
                break;
            }
        }
        if self.bottom || (moved_since && empty(&self.names, &last)) {
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
    /// forgotten, so that it is projected again if it comes back. `moved` is the names that
    /// differ between the names as last projected and the names now, in key order, as
    /// [`Scope::reduce_with`] found them.
    // Complexity tradeoff: naive version, the difference of the names as last projected and
    // the names now found here again, after `reduce_with` found it for `moved` with neither map
    // changed between, one more walk of the two maps' paths to the changes per round, about
    // 3,300 instructions a binding of the fee test (COMPLEXITY.md row PA-bind-cost). Used: the
    // names `reduce_with` found, O(changes). Test:
    // `l01_39_reduced_product::deep_let::the_arms_of_a_deep_block_scale`.
    fn due(&mut self, whole: bool, force: bool, moved: &[Arc<str>]) -> Option<Due> {
        if !self.lazy {
            self.seen.order.sync(&self.relation, &self.names);
        }
        let Some((_, old)) = &self.seen.projection else {
            return Some(Due::All);
        };
        if force {
            return Some(Due::All);
        }
        let mut out: BTreeSet<BlockId> = BTreeSet::new();
        let mut seeds = Seeds::default();
        let mut any = false;
        let blocks = self.relation.blocks();
        for n in moved {
            any = true;
            seeds.names.insert(n.clone());
            seeds.changed.insert(n.clone());
            out.extend(self.moved_blocks(&self.relation, n));
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
        // ([`Scope::leaf_bound_stays`]). A lazy one finds the leaf stale when read, since the
        // star's part is keyed by those conjuncts. The star's projection gives the hubs no bound
        // that the hubs' own block lacks: the leaf is unbounded on the side away from them, and
        // the conjuncts among them are parts of both blocks, keyed apart ([`PartKey`]), so the
        // two scopes hold the hubs alike (item NARROW-lazy-settle).
        let mut families: BTreeSet<conjuncts::Class> = BTreeSet::new();
        let mut gone: Vec<Arc<Formula>> = Vec::new();
        // The blocks of `old` that lost a conjunct, and those whose names were made seeds.
        let (mut lost, mut named): (BTreeSet<BlockId>, BTreeSet<BlockId>) = Default::default();
        for d in old.set().diff(self.relation.set()) {
            any = true;
            match d {
                imbl::ordset::DiffItem::Add(g) => {
                    out.extend(blocks.of(g));
                    seeds.names.extend(conjuncts::names(g));
                    seeds.added.insert(g.clone());
                    if !self.lazy {
                        families.extend(self.relation.classed(g));
                    }
                }
                imbl::ordset::DiffItem::Remove(g) => {
                    if !self.lazy {
                        families.extend(old.classed(g));
                    }
                    // A conjunct gone from a tree of difference constraints and bounds leaves
                    // the bounds there a fixed point of those left. From any other tree, whose
                    // projection may have been refused, its names and its block's are made
                    // seeds, and so unsure, below.
                    // Complexity tradeoff: naive version, the names and the block now of each
                    // conjunct of the block `g` left, read for each conjunct removed: O(d log n)
                    // for a block of d conjuncts, so one conjunct taken out of a block of near
                    // k at each of k tests costs O(k² log n). Used: the block's names from their
                    // counts ([`conjuncts::Blocks::names_of`]) and the blocks now of its
                    // conjuncts from the difference of its conjuncts then and now
                    // ([`conjuncts::Blocks::now_of`]), each read once for all the conjuncts
                    // removed from it, in O(log n) per name and per conjunct moved. Test
                    // `l01_39_reduced_product::families::coordkk_scales`; COMPLEXITY.md row
                    // PERF-l139-due.
                    let names = conjuncts::names(g);
                    let was = old.blocks().of(g);
                    if names.iter().any(|n| !old.differences_only_at(n)) {
                        seeds.names.extend(names);
                        if let Some(b) = was.filter(|&b| named.insert(b)) {
                            seeds.names.extend(old.blocks().names_of(b).cloned());
                        }
                    }
                    if let Some(b) = was.filter(|&b| lost.insert(b)) {
                        out.extend(blocks.now_of(old.blocks(), b));
                    }
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
        // stay ([`Scope::leaf_bound_stays`]), every star of the class is projected again, though
        // a leaf whose own product lies within both bounds keeps its product. Why: finding only
        // the leaves whose own bound lies past the class's needs them ordered by their own
        // products, which every narrowing of a leaf would have to keep. Trigger: a test among
        // the hubs of `k` stars of one class that moves the class's bound, or one of the cases
        // `leaf_bound_stays` leaves out: `k` projections, as the `k` leaves that move cost.
        // Test: `l01_39_reduced_product::scaling::tests_among_the_hubs_of_many_stars_narrow_an_eager_scope_in_linear_time`.
        // COMPLEXITY.md row C26. A complete solution keeps the leaves of each class ordered by
        // their own bound on the side the class bounds, in each scope, and projects only those
        // the class's new bound cuts.
        for f in &families {
            // A class of the family with stars before and now; one that had none before is new
            // and its stars are projected anyway.
            let class = self
                .relation
                .family_classes(f)
                .find(|c| old.class_leaves(c).next().is_some());
            // Complexity tradeoff: naive version, the check of the class's bound made for every
            // family, two projections of each of its parts when the bound is found again
            // ([`Scope::leaf_bound_stays`]). Used: a family with one star before skips the
            // check and projects the star, which costs only its parts that are due
            // ([`Block::update`]), and gives what the check would leave, the star's products
            // being those its projection gives. Tradeoffs: the star is projected though its
            // leaf's bound may stay, one projection of its due parts; the check reads two
            // leaves at most, O(log n). Test:
            // `l01_39_reduced_product::scaling::an_eager_scope_with_many_distinct_disjunctions_among_the_hubs_of_a_star_scales`.
            // COMPLEXITY.md row C26.
            let one = old
                .family_classes(f)
                .flat_map(|c| old.class_leaves(c))
                .take(2)
                .count()
                < 2;
            let stays = match class {
                Some(c) if one => {
                    self.seen.bounds.remove(c);
                    false
                }
                Some(c) => {
                    let (stays, record) = self.leaf_bound_stays(old, c);
                    match record {
                        Some(r) => self.seen.bounds.insert(c.clone(), r),
                        None => self.seen.bounds.remove(c),
                    };
                    stays
                }
                None => false,
            };
            if stays {
                continue;
            }
            for c in self.relation.family_classes(f) {
                out.extend(
                    self.relation
                        .class_leaves(c)
                        .filter_map(|x| self.relation.star(x)),
                );
            }
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
                .range((g.clone(), None)..)
                .map(|(k, _)| k)
                .take_while(|k| k.0 == g)
                .cloned()
                .collect();
            for k in &keys {
                self.projected.remove(k);
                self.seen.drop_part(k);
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
        if !whole && self.gaps.holds(&self.relation, &self.names) {
            return;
        }
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
            self.seen.drop_blocks();
            return;
        }
        if whole {
            // The conjuncts linked by shared atoms, found by a union-find over the atoms, not
            // by the trees of blocks: a star is a tree of its own ([`Conjuncts::star`]), and
            // this projection is the one the blocks' is checked against. Its records are keyed
            // without a leaf, so no kept block stays.
            self.seen.drop_blocks();
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
            let mut trees: BTreeMap<usize, Vec<&Arc<Formula>>> = BTreeMap::new();
            for (g, at) in self.relation.set().iter().zip(first) {
                if let Some(i) = at {
                    trees.entry(root(&mut parent, i)).or_default().push(g);
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
                        if !self.lazy {
                            self.seen.order.sync(&relation, &self.names);
                        }
                        for n in &ns {
                            for c in self.moved_blocks(&relation, n) {
                                if blocks.tree(c) != t {
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
                        if !self.lazy {
                            self.seen.order.sync(&relation, &self.names);
                        }
                        for n in &ns {
                            for c in self.moved_blocks(&relation, n) {
                                if blocks.tree(c) != t {
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
            // Complexity tradeoff: naive version, each name of the block compared with a
            // snapshot taken before its projection, O(m) for `m` names. Used: the names'
            // products before, a persistent map shared in O(1), diffed with those after, which
            // skips what they share, O(c log m) for `c` changed names. Tradeoffs: a scope that
            // turned bottom shows no change in its map, so it is checked first. COMPLEXITY.md
            // row C26.
            let start = self.names.view().clone();
            let refusals = self.refusals.clone();
            let (block, due) = self.block(&relation, b);
            self.project_block(block, due);
            if self.bottom {
                self.relation = relation;
                return;
            }
            // A star projected is noted, so that a later move of a hub that leaves its leaf
            // within its family's bound passes it over ([`Scope::moved_blocks`]).
            if !self.lazy {
                let leaf = (blocks.members(b))
                    .filter(|_| blocks.is_apart(b))
                    .flat_map(|g| conjuncts::names(g))
                    .find(|x| relation.star(x) == Some(b));
                if let Some(x) = leaf {
                    let refused = !self.refusals.ptr_eq(&refusals);
                    self.seen.order.mark(&relation, &self.names, &x, refused);
                }
                self.seen.order.sync(&relation, &self.names);
            }
            let users = &self.seen.blocks[&b].users;
            let moved: Vec<Arc<str>> = start
                .diff(&self.names)
                .filter_map(|d| {
                    let (n, old, new) = match d {
                        DiffItem::Add(n, p) => (n, None, Some(p)),
                        DiffItem::Remove(n, p) => (n, Some(p), None),
                        DiffItem::Update { old, new } => (new.0, Some(old.1), Some(new.1)),
                    };
                    let top = Product::top();
                    let (old, new) = (old.unwrap_or(&top), new.unwrap_or(&top));
                    let same = same_framed(old, new);
                    (!same && users.contains_key(n)).then(|| n.clone())
                })
                .collect();
            let mut echo = false;
            for n in &moved {
                let p = self.get(n);
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
                for c in self.moved_blocks(&relation, n) {
                    if c != b {
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
                let names = self.seen.blocks[&b].names();
                let (tree, _) = conjuncts::reach(&[&relation], names, |_| true);
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
            if ints.is_empty() {
                return Ends::Done(Shortest::Bottom(n.clone()));
            }
            dom.push(ints.pieces().map(|(a, b)| (int(a), int(b))).collect());
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
                let between = Formula::and(gs.into_iter().map(|g| (**g).clone()).collect());
                let constraint: Arc<str> = between.written(written_name).into();
                let on = mentioned(&constraint, syms_of(&between));
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
                    &on,
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
    /// In O(m log n) for the `m` edges at the names of the component of each edge whose
    /// potential falls, of `n` names, and once more for each cycle of weight 0 tied; an edge
    /// against the order of the components costs those the search that ends first finds
    /// ([`reorder`]).
    fn repair(
        &mut self,
        relation: &Conjuncts,
        t: BlockId,
        added: &BTreeSet<Arc<Formula>>,
    ) -> Result<Option<Arc<str>>, Fall> {
        let blocks = relation.blocks();
        let mut pot = self.potential.clone();
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
                pot.tied.insert((g.clone(), false));
                pot.tied.insert((g.clone(), true));
            }
            pending.push((g.clone(), false, e));
            if let Some(e) = back {
                pending.push((g.clone(), true, e));
            }
        }
        let found = put_in(relation, t, added, &pending, &mut pot)?;
        if found.is_none() {
            self.potential = pot;
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
    /// In O((r + their edges) log n) for the `r` names of the component of `x` whose
    /// potential falls ([`Potential`]): O(log n) for a name on no cycle, as each name of a
    /// chain or a ladder is. A projection stops raising a tree at the first raise that fails
    /// ([`Scope::project`]).
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
        let mut pot = self.potential.clone();
        pot.at.insert(x.clone(), (&px.0 - &(&g - &was), px.1));
        pot.gap.insert(x.clone(), g);
        let out: Vec<(Arc<Formula>, bool, Edge)> = tree_edges(relation, t, x)
            .into_iter()
            .filter(|(_, _, e)| e.from.as_ref() == Some(x) && e.to.is_some())
            .collect();
        if let Ok(None) = put_in(relation, t, &BTreeSet::new(), &out, &mut pot) {
            self.potential = pot;
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
    /// at most the gap `g_x` the potential holds with, so the key of a name is the rank of its
    /// component on this side, then its bound less `q`, the potential up, and the potential
    /// plus the gap, negated, down; an edge `s → x` of weight `k` read within a component is
    /// checked to have `q_s + k - q_x - g_x` of zero or more, which is its reduced weight in the
    /// potential on either side, and one between components to go up in rank on this side
    /// ([`Potential`]). Each key pushed is then at least the key popped, and each name is
    /// popped at its latest bound once.
    // Complexity tradeoff: naive version, every seed reads all its edges in and the Dijkstra
    // search starts from every seed, so a hub `n` with 2k edges from k tests `ai == n` is read
    // twice per side at each test, O(k²) (37.4 times the instructions from k = 150 to 1200).
    // Used: a seed reads only the edges of the conjuncts added, and the edges into it only if
    // its product changed or another block moved it (`Seeds::changed`); the search starts from
    // the changed seeds and those lowered, O((s + a + m) log n) per projection (8.6 times).
    // Tradeoffs: correctness rests on every other edge holding at the fixed point the last
    // projection left, so `Seeds::changed` must record every change of a seed's product.
    // Test `l01_39a_bit_words::scaling::tests_that_equate_each_reading_to_a_hub_read_the_hub_once_each`;
    // COMPLEXITY.md row NARROW-hub-seed-edges.
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
        // The component of `n` and its rank on this side: an edge between components goes up
        // in rank, so against the edges down in rank.
        let rank = |n: &Arc<str>| -> Result<(u64, i64), Fall> {
            let c = self.potential.comp_of(n)?;
            let r = self.potential.rank(c);
            Ok((c, if up { r } else { -r }))
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
        let mut heap: BinaryHeap<Queued> = BinaryHeap::new();
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
                heap.push(Reverse(((rank(s)?.1, l - &q(s)?), s.clone())));
            }
        }
        while let Some(Reverse(((_, k), s))) = heap.pop() {
            let Some(Some(ls)) = label.get(&s).cloned() else {
                continue;
            };
            let qs = q(&s)?;
            if &ls - &qs != k {
                continue;
            }
            let rs = rank(&s)?;
            for (_, _, e) in tree_edges(relation, t, &s) {
                let (a, b) = way(&e);
                let (Some(a), Some(x)) = (a, b) else {
                    continue;
                };
                if a != s {
                    continue;
                }
                let qx = q(&x)?;
                let rx = rank(&x)?;
                let holds = if rx.0 == rs.0 {
                    &(&(&qs + &e.weight) - &qx) - &gap(&x) >= Int::ZERO
                } else {
                    rx.1 > rs.1
                };
                if !holds {
                    return Err(Fall::Potential);
                }
                let by = &ls + &e.weight;
                if read(&mut label, &x)?.is_none_or(|c| by < c) {
                    let at = snap(&x, by);
                    moved.insert(x.clone(), at.clone());
                    heap.push(Reverse(((rx.1, &at - &qx), x.clone())));
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
            let mut all: Vec<Vec<usize>> = vec![Vec::new(); main.len()];
            for (i, j, _, _) in &tight {
                out[*i].push(*j);
            }
            for g in &cons {
                let Some((e, back)) = conjuncts::edges(g) else {
                    continue;
                };
                for e in std::iter::once(e).chain(back) {
                    if let (Some(u), Some(v)) = (&e.from, &e.to)
                        && let (Some(&i), Some(&j)) = (at.get(u), at.get(v))
                    {
                        all[i].push(j);
                    }
                }
            }
            // The components of every edge, numbered with each after those it reaches, so a
            // rank that falls with the number goes up along each edge between them.
            let parts = zedc_solvers::utvpi::components(&all, |j| *j);
            let count = parts.iter().map(|c| c + 1).max().unwrap_or(0);
            for n in &names {
                self.potential.leave(n);
            }
            for (k, (n, _)) in main.iter().enumerate() {
                let c = parts[k];
                let id = self.potential.next + c as u64;
                self.potential.comp.insert(n.clone(), id);
                let part = self.potential.parts.entry(id).or_insert_with(|| Component {
                    rank: 0,
                    names: imbl::OrdSet::new(),
                    ends: imbl::OrdSet::new(),
                });
                part.names.insert(n.clone());
            }
            // The ends of each edge between components.
            for (i, heads) in all.iter().enumerate() {
                for &j in heads.iter().filter(|&&j| parts[j] != parts[i]) {
                    for k in [i, j] {
                        let id = self.potential.next + parts[k] as u64;
                        if let Some(part) = self.potential.parts.get_mut(&id) {
                            part.ends.insert(main[k].0.clone());
                        }
                    }
                }
            }
            // Ranked after every other, each after those it reaches.
            for c in (0..count).rev() {
                let id = self.potential.next + c as u64;
                if self.potential.parts.contains_key(&id) {
                    let last = self.potential.last();
                    self.potential.rank_after(id, last);
                }
            }
            self.potential.next += count as u64;
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
            .read(n)
            .is_some_and(|p| classed(&p) || hole_gap(p.ints()) > self.potential.gap_of(n))
    }

    /// Projects the parts of `b` that are due, then marks every part of `b` projected. A
    /// part is due when it is new or its names' intervals or classes have changed since its
    /// last projection, and a projection that moves a name's bound makes due again the other
    /// parts that mention the name, so a bound passes along a chain of parts. When one name's
    /// bound moves a second time, the parts may pass it back and forth by steps as small as
    /// one value; the block's conjuncts are then projected together once, which gives the
    /// fixed point the steps tend to, and the worklist stops. That is an event of the
    /// projection, not a count of steps or a size.
    fn project_block(&mut self, mut b: Block, due: Vec<PartAt>) {
        let start = self.names.view().clone();
        let (was_stair, was_ray) = (b.stair_managed, b.ray_managed);
        let mut covered = self.cover(&mut b, true);
        let mut due = due;
        due.extend(b.released(was_stair, was_ray).cloned());
        let mut moved: BTreeSet<Arc<str>> = BTreeSet::new();

        let due = if covered.is_some() || b.ray_managed {
            let mut due: BTreeSet<PartAt> = due.into_iter().collect();
            for d in start.diff(&self.names) {
                if let DiffItem::Update {
                    old: (_, a),
                    new: (_, nb),
                } = &d
                    && same_framed(a, nb)
                {
                    continue;
                }
                let (DiffItem::Add(n, _)
                | DiffItem::Remove(n, _)
                | DiffItem::Update { new: (n, _), .. }) = d;
                moved.insert(n.clone());
                due.extend(b.due_users(n).cloned());
            }
            due.into_iter().collect()
        } else {
            due
        };
        // Each part is compared with the snapshot of its own names, not the block's: a part
        // new to the block, or a name of another part, leaves it as it was, so a new conjunct
        // costs its own part and not the block's (the walk through a shared name). The parts
        // due come from the block kept from the last projection ([`Scope::block`]).
        if due.is_empty() {
            self.keep(b);
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
        //
        // Complexity tradeoff: naive version, `threshold::shape` read over every conjunct of
        // the block at each projection, O(k) for `k` conjuncts. Used: a block that holds a
        // conjunct showing it is no component ([`Block::unshaped`]) skips the read, in O(1).
        // Tradeoffs: the block keeps the set of such conjuncts, updated as conjuncts come and
        // go; a block without one is read whole, as before. COMPLEXITY.md row C26.
        // The aggregate is the exact solution of the entire component when every part
        // other than the constraints is a threshold row. Reading and solving that same
        // component again would rebuild a k-row system in each of k cases, O(k^2 log k).
        // The roles of the block's parts ([`Block::roles`]) establish coverage in O(1).
        // Complexity tradeoff: keep the general solver for components with other parts;
        // the wholly covered shape uses the persistent O(log k) threshold queries above.
        let all_stairs = covered.is_some() && b.roles.keys().all(|r| *r == Role::Stair);
        if b.unshaped.is_empty() && !all_stairs {
            let core: Vec<Arc<Formula>> = b.core.keys().cloned().collect();
            if let Some(shape) = &threshold::shape(&core)
                && self.project_threshold(shape)
            {
                self.cover(&mut b, covered.is_some());
                self.record(b, &start, &due);
                return;
            }
        }
        // A star's leaf is unbounded on the side away from its hubs, so each part bounds it by
        // a half-line its interval does not change, and no part's projection onto the hubs
        // reads it ([`Conjuncts::star`]): a move of the leaf makes no other part due and is
        // no move back and forth. Every part of a star mentions the leaf, through the star's
        // own conjunct, so otherwise each move of it projected all of them (item
        // NARROW-lazy-settle).
        let leaf = b.leaf.clone();
        let mut work: std::collections::VecDeque<PartAt> = due.iter().cloned().collect();
        // Complexity tradeoff: naive version, `PartAt` orders `(false, conjunct)` before
        // `(true, least)`, so in a case of a star (`persist` Arm 2 `x - j * y >= 1`) a woke
        // disjunction projects first under coarse hub bounds, `(true, least)` then narrows the
        // hub tighter (`x` from `-531` to `-124`), and that second movement of `x` trips
        // `again = true` (`30` extra `project_each` calls at k = 16, Gemini seat, round 3).
        // Used: on a star block, run `(true, least)` at the front of the initial worklist and
        // credit each hub it narrows once in `moved_by_base` so a single subsequent disjunctive
        // tightening does not trip `again` as ping-pong (two disjunctive tightenings still trip
        // `again`). Reference: C. Schulte and P. J. Stuckey, "Efficient constraint propagation
        // engines", ACM TOPLAS 31(1), Article 2, 2008.
        let mut initial_star_base: Option<PartAt> = None;
        let mut moved_by_base: BTreeSet<Arc<str>> = BTreeSet::new();
        if leaf.is_some()
            && work.len() >= 2
            && work.back().is_some_and(|at| at.0)
            && let Some(base_at) = work.pop_back()
        {
            initial_star_base = Some(base_at.clone());
            work.push_front(base_at);
        }
        let mut queued: BTreeSet<PartAt> = due.iter().cloned().collect();
        // The idle verdicts and certified chain ends found since the names last moved
        // ([`Scope::idle_by_chain`]).
        let mut certified: BTreeMap<PartAt, bool> = BTreeMap::new();
        let mut certified_chains: BTreeMap<Arc<Vec<ChainAtom>>, Vec<Int>> = BTreeMap::new();
        while let Some(i) = work.pop_front() {
            queued.remove(&i);
            let part = &b.parts[&i].clone();
            if b.managed(part) || self.puncture_idle(&b, &part.key.0) {
                continue;
            }
            // Complexity tradeoff: repeated projection is replaced by a sufficient
            // integer-witness certificate. It changes no marginal and cannot wake
            // another part or contribute a movement to again. Pugh, "The Omega
            // test: a fast and practical integer programming algorithm for dependence
            // analysis", Proceedings of Supercomputing '91, ACM/IEEE, 1991, pp. 4-13,
            // supplies the dark-shadow slack (a-1)(b-1). Parallel normalization and
            // non-growing elimination are described at eliminate: unlike the round-2 version of
            // this test, the number of rows is bounded by the input shape including box ends.
            // For V mixed names and R rows this is polynomial (repeated indexed row
            // passes), not a general O(n log n) projection algorithm. Measured in
            // review round 3 of PERF-l139-wake (COMPLEXITY.md row PERF-l139-wake). A first projection
            // is always retained. Classed or holed eliminands refuse this certificate.
            // A skipped solver refusal is not reconstructed: equality of warnings
            // remains a separate, explicitly tested limitation, not a consequence
            // of marginal support. The covered guard is unnecessary: cover was
            // called at loop entry and after the preceding actual projection; with
            // unchanged names and block, calling it again is idempotent (its own
            // documented invariant). No aggregate transition can be missed here.
            // Complexity tradeoff: naive version, `idle` on each projected part each time it
            // is dequeued: a test of k arms splits into k cases, each wakes the k earlier
            // parts, and each is certified again, k^2 eliminations of ~0.2M instructions.
            // Used: [`Scope::idle_by_chain`]. A part whose conjunct is a disjunction of rows
            // is implied by the least part of its chain key when that one's ends lie at or
            // below its own, and then it is idle whenever that one is: the certificate is
            // monotone in the point set, and the two formulas share the block's base and
            // names. One certificate per chain and box replaces one per part. Cost: O(log k)
            // to find the least part, O(e) to compare e ends; parts of other shapes, or not
            // above the least, are certified as before; a verdict is kept until the next
            // projection moves the names. Certificates in a model of the loop at k = 32:
            // star_extra 1488 against 93, chain 4032 against 250, coordmix 2512 against 590,
            // hopb unchanged (its chain keys all differ). Measured at 8n (instructions):
            // star_extra 14.8 to 10.1 times, coordmix_floor 12.0 to 10.2, chain 10.9 to 10.2
            // (XR-l139-family). Prior work: the certificate is the Omega test's exactness
            // check (Pugh, "The Omega test", Supercomputing '91, pp. 4-13); taking the least
            // element of a chain under implication is subsumption, as in clause subsumption.
            if !b.ray_managed
                && self.projected.contains_key(&part.key)
                && self.idle_by_chain(&b, &i, part, &mut certified, &mut certified_chains)
            {
                continue;
            }
            // Complexity tradeoff: naive version, a covered block's names copied and their
            // intervals and classes read before each part, O(N) per part for a block of N
            // names, O(N k) over k parts. Used: the names' map kept by sharing, O(1), and the
            // names of the block it differs at read after, O(c log N) for c changed names
            // ([`Scope::block_before`]). Tradeoffs: none; a part's own names, when the block
            // is not covered, are read as before, O(|part|).
            let start_part = (self.names.view().clone(), self.bottom);
            let part_before = (covered.is_none()).then(|| self.snapshot(&part.names));
            let projected_now = b.formula(part);
            let refusals_before = self.refusals.clone();
            self.project_part(&projected_now);
            certified.clear();
            certified_chains.clear();
            let after_part = self.names.view().clone();
            let was = (b.stair_managed, b.ray_managed);
            covered = self.cover(&mut b, covered.is_some());
            for j in b.released(was.0, was.1) {
                if queued.insert(j.clone()) {
                    work.push_back(j.clone());
                }
            }
            // An aggregate move is a projection of other parts. It must wake this part
            // again too, just as projecting a threshold row separately would. The diff
            // touches at most the two aggregate names and skips shared map structure.
            let aggregated: BTreeSet<Arc<str>> = after_part
                .diff(&self.names)
                .filter_map(|d| match d {
                    DiffItem::Add(n, _) | DiffItem::Remove(n, _) => Some(n.clone()),
                    DiffItem::Update {
                        old: (_, a),
                        new: (n, nb),
                    } => (!same_framed(a, nb)).then(|| n.clone()),
                })
                .collect();
            let mut again = false;
            let mut empty = false;
            let before = part_before.unwrap_or_else(|| self.block_before(&b, &start_part));
            for old in before.iter() {
                let n = &old.0;
                let p = self.get(n);
                if (p.ints(), &framed_class(&p)) == (&old.1, &old.2) {
                    continue;
                }
                empty |= p.ints().is_empty();
                if leaf.as_ref() == Some(n) {
                    continue;
                }
                if initial_star_base.as_ref() == Some(&i) {
                    moved_by_base.insert(n.clone());
                    again |= !moved.insert(n.clone());
                } else if !moved_by_base.remove(n) {
                    again |= !moved.insert(n.clone());
                }
                for j in b.due_users(n) {
                    if (j != &i || aggregated.contains(n)) && queued.insert(j.clone()) {
                        work.push_back(j.clone());
                    }
                }
            }
            if initial_star_base.as_ref() == Some(&i) {
                initial_star_base = None;
            }
            if empty {
                break;
            }
            if again {
                let all = compact_abs(&Formula::and(
                    b.parts.values().map(|p| b.formula(p)).collect(),
                ));
                // Complexity tradeoff (PERF-l139-persist-due): naive version, the conjunction
                // of all parts always projected here. In `persist` (the star `a >= x + y` and
                // the disjunctions `x + j * y >= 1 || x - j * y >= 1`) the abs forms make
                // `compact_abs` keep only the part of j = 1, the part just projected, so each
                // test projected that part twice: 4.1M instructions a test at k = 16, 57M of
                // the 551M of the run. Used: the projection is left out when its formula has
                // the conjuncts of the part just projected (`distinct_conjuncts`, O(r log r)
                // for its r conjuncts), that projection refused nothing, and the cover after
                // it moved no name. An exact projection meets the names `N` with the box of
                // `F ∧ N`; the box holds `F ∧ N`, so a second projection of `F` meets with the
                // same box and moves nothing, and `cover`, which reads only the names and the
                // block, gives what it gave. A refusal keeps the box stage's bounds, which a
                // second projection may narrow, so the projection is made then. Cost: one
                // persistent-map clone (O(1)) per part projected, and the comparison.
                // Measured (persist, k = 2 / 16): 65.5M / 551.3M instructions before,
                // 62.4M / 494.5M after (perf stat, the whole test).
                let repeat = aggregated.is_empty()
                    && self.refusals.ptr_eq(&refusals_before)
                    && distinct_conjuncts(&all) == distinct_conjuncts(&projected_now);
                if !repeat {
                    self.project_part(&all);
                    self.cover(&mut b, covered.is_some());
                }
                break;
            }
        }
        self.record(b, &start, &due);
    }

    /// Records the parts of `b` as projected, after a projection of it that began with the
    /// names' products `start` and projected the parts `due`: those parts, and each part that
    /// mentions a name the projection changed. Every other part was projected with its names'
    /// intervals and classes as they still are, so its record stays. Then keeps the block.
    ///
    /// Complexity tradeoff: naive version, every part of the block recorded again, O(k log k)
    /// for `k` parts. Used: the parts due and the users of the names whose products differ
    /// from `start`, found by a diff of persistent maps that skips what they share, in
    /// O((d + c) log k) for `d` parts due and `c` changed names' parts. Tradeoffs: the
    /// clone of the names' map at the start, O(1) by sharing. COMPLEXITY.md row C26.
    fn record(&mut self, b: Block, start: &imbl::OrdMap<Arc<str>, Product>, due: &[PartAt]) {
        let mut writes: BTreeSet<&PartAt> =
            due.iter().filter(|at| !b.managed(&b.parts[*at])).collect();
        for d in start.diff(&self.names) {
            if let DiffItem::Update {
                old: (_, a),
                new: (_, nb),
            } = &d
                && same_framed(a, nb)
            {
                continue;
            }
            let (DiffItem::Add(n, _)
            | DiffItem::Remove(n, _)
            | DiffItem::Update { new: (n, _), .. }) = d;
            writes.extend(b.due_users(n));
        }
        for at in writes {
            let p = &b.parts[at];
            let snapshot = self.snapshot(&p.names);
            self.projected
                .insert(p.key.clone(), (p.with.clone(), snapshot));
        }
        self.keep(b);
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
                for (n, (lo, hi)) in shape.names.iter().zip(names) {
                    self.meet_own(n, IntervalSet::range(lo, hi));
                }
                if let Some(w) = &shape.hub {
                    self.meet_own(w, hub);
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
            let (below, above) = sides(self.names.read(n).as_deref());
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
                (n.clone(), p.ints().clone(), framed_class(&p))
            })
            .collect()
    }

    /// The interval and class each name of `b` had at `then`, an earlier state of the names'
    /// products and of `bottom`, for the names whose product may differ now, in name order:
    /// those the names' map differs at, or every name of `b` when `bottom` has changed. The
    /// rest are as they were, so [`Scope::snapshot`] of all of `b`'s names gives no more.
    fn block_before(&self, b: &Block, then: &(imbl::OrdMap<Arc<str>, Product>, bool)) -> Projected {
        let (names, bottom) = then;
        let changed: Vec<Arc<str>> = if self.bottom != *bottom {
            b.names()
        } else {
            (names.diff(&self.names))
                .filter_map(|d| match d {
                    DiffItem::Add(n, _) | DiffItem::Remove(n, _) => Some(n.clone()),
                    DiffItem::Update {
                        old: (_, a),
                        new: (n, nb),
                    } => (!same_framed(a, nb)).then(|| n.clone()),
                })
                .filter(|n| b.users.contains_key(n))
                .collect()
        };
        let read = |n: Arc<str>, p: &Product| (n, p.ints().clone(), framed_class(p));
        changed
            .into_iter()
            .map(|n| match names.get(&n) {
                Some(p) if !*bottom => read(n, p),
                _ if *bottom => read(n, &Product::bottom()),
                _ => read(n, &Product::top()),
            })
            .collect()
    }

    /// The bound the conjuncts `core` of a class of stars ([`conjuncts::Class`]) give its
    /// leaf, in the names' products as they are: the meet of each part's ([`split`]), with the
    /// constraints together, from which a conjunct's part is made. `None` when a part's bound
    /// is not found. Each part is projected onto the leaf, written [`conjuncts::LEAF`], as
    /// [`Scope::project_block`] projects a star of the class, but with the leaf's own product
    /// left whole. A star bounds its leaf on one side only, by a half-line
    /// ([`Conjuncts::star`]), so when the projection is exact a leaf `x` of the class projects
    /// to its own product cut by that half-line, and keeps its product when the half-line
    /// stays ([`Scope::leaf_bound_stays`]). The projection is exact when every conjunct is a
    /// constraint or the negation of a bound and every name but the leaf has one interval: a
    /// leaf's own product of many intervals is then the one disjunction, which the solver
    /// projects exactly ([`presburger::project`]).
    fn core_leaf_bound(&self, core: &[Arc<Formula>]) -> Option<(IntervalSet, Arc<Formula>)> {
        let (cons, others): (Vec<&Arc<Formula>>, Vec<&Arc<Formula>>) =
            core.iter().partition(|g| matches!(&***g, Formula::Con(_)));
        let context = Split::new(&cons, None);
        let mut out = IntervalSet::top();
        let parts = others.into_iter().map(|g| context.part(g, &context));
        for (_, _, part) in parts.chain(context.constraints()) {
            out = out.meet(&self.part_leaf_bound(&part)?);
        }
        Some((out, context.base))
    }

    /// The bound one part of a class's conjuncts gives its leaf ([`Scope::core_leaf_bound`]):
    /// its projection onto the leaf, `None` when a name other than the leaf has more than one
    /// interval, the part does not mention the leaf, or the solver refuses.
    fn part_leaf_bound(&self, part: &Formula) -> Option<IntervalSet> {
        let leaf = Atom::Sym(Arc::from(conjuncts::LEAF));
        let (whole, syms) = self.framed(part);
        let one = |a: &Atom| match a {
            Atom::Sym(n) => a == &leaf || self.get(n).ints().len() <= 1,
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
        each.swap_remove(i).ok()
    }

    /// The blocks a move of `n` makes due ([`Conjuncts::moved`]), with the order of the leaves
    /// brought up to date first ([`Order::sync`]). A lazy scope leaves the stars at `n` to be
    /// settled when read ([`Conjuncts::moving`]). An eager one projects those whose leaf the
    /// move can change: a star bounds its leaf on one side by a half-line, and when every
    /// conjunct the stars of a family are projected with is a constraint or the negation of a
    /// bound and every hub holds one interval, the projection onto a leaf of class `c` is the
    /// leaf's product met with the family's bound `B` moved by the class's shift
    /// ([`Scope::core_leaf_bound`], [`Order`]), so a leaf whose product lies in it keeps its
    /// product. The star's projection onto its hubs reads only the leaf's product, and held of
    /// the hubs when the star was last projected ([`Order::projected`]); a move narrows them,
    /// and a join's hull of two sides that each hold it holds it. So such a star moves nothing
    /// and is left out. Otherwise, or when `B` is not one interval, every star of the family.
    ///
    /// Complexity tradeoff: naive version, every star at `n` projected again, or brought up to
    /// date to find nothing due ([`Scope::block`]), at each move of `n`: O(k) for `k` stars,
    /// and O(k²) for `k` tests on `n`, as a nest of `k` `if`s on the hubs of `k` stars. Used:
    /// the family's bound found once from the conjuncts the stars are projected with, and the
    /// leaves it cuts read from the two ends of the family's order, O(F·p + (c + 1) log k)
    /// for `F` families at `n`, `p` the cost of projecting a family's core onto its leaf, and
    /// `c` stars cut; keeping the order costs O(log k) per leaf changed ([`Order::sync`]).
    /// Tradeoffs: memory for two persistent ordered sets of the leaves of each family and the
    /// conjuncts of each star projected; a family whose core holds a conjunct other than a
    /// constraint or the negation of one ([`Scope::family_bound`]), or whose hubs have more
    /// than one interval, projects all its stars, as before; the core is read whole at each
    /// move, O(f) for `f` conjuncts among the hubs. Test:
    /// `l01_39_reduced_product::scaling::tests_on_the_hubs_of_many_stars_in_an_eager_scope_scale`.
    /// COMPLEXITY.md row C49.
    fn moved_blocks(&self, relation: &Conjuncts, n: &str) -> Vec<BlockId> {
        let blocks = relation.blocks();
        let mut out: Vec<BlockId> = blocks.moving_blocks(n).collect();
        if self.lazy {
            return out;
        }
        out.extend((self.cut_leaves(relation, n).iter()).filter_map(|x| relation.star(x)));
        out
    }

    /// The leaves of the stars at hub `n` of an eager scope whose projection can change them
    /// ([`Scope::moved_blocks`]): those whose product the bound of their family cuts, and
    /// every leaf of a family whose bound is not one interval found exactly. In
    /// O(F·p + (c + 1) log k) for `F` families at `n`, `p` the cost of projecting a family's
    /// core onto its leaf, and `c` leaves found, of `k`.
    fn cut_leaves(&self, relation: &Conjuncts, n: &str) -> Vec<Arc<str>> {
        let order = &self.seen.order;
        let mut out = Vec::new();
        for f in order.at.of(n) {
            let (Some(low), Some(high)) = (order.low.get(f), order.high.get(f)) else {
                continue;
            };
            let leaf = |(_, x): &(End, Arc<str>)| x.clone();
            match self.family_bound(relation, f) {
                Some((l, u)) => {
                    out.extend(low.iter().take_while(|(k, _)| *k < l).map(leaf));
                    out.extend((high.iter().rev()).take_while(|(k, _)| *k > u).map(leaf));
                }
                None => out.extend(low.iter().map(leaf)),
            }
        }
        out
    }

    /// The bound family `f`'s conjuncts and those among its hubs ([`Conjuncts::core`]) give
    /// its leaf, when it is one interval and the projection is exact
    /// ([`Scope::core_leaf_bound`]): every conjunct a constraint or the negation of one.
    /// `None` at the first conjunct that is neither, as for a disjunction among the hubs.
    ///
    /// Complexity tradeoff: naive version, any conjunct that does not mention the leaf
    /// admitted, so a core of `d` disjunctions among the hubs cost `d` projections of a part
    /// at each move or join, O(d²) for `d` tests that each add one (60.8 times the bytes at
    /// 8k on `an_eager_scope_with_many_distinct_disjunctions_among_the_hubs_of_a_star_scales`).
    /// Used: such a family keeps every leaf, each brought up to date as before by its block
    /// ([`Scope::block`], [`Scope::refresh`]); the check stops at the first such conjunct.
    /// COMPLEXITY.md row C49.
    fn family_bound(&self, relation: &Conjuncts, f: &conjuncts::Class) -> Option<(End, End)> {
        let exact = |g: &Arc<Formula>| match &**g {
            Formula::Con(_) => true,
            Formula::Not(n) => matches!(&**n, Formula::Con(c) if c.rel == Rel::Ge),
            _ => false,
        };
        let hubs = family_hubs(f);
        let mut core: BTreeSet<Arc<Formula>> = BTreeSet::new();
        for g in f.iter() {
            if !exact(g) {
                return None;
            }
            core.insert(g.clone());
        }
        // A star of one hub is projected with its own conjuncts alone.
        if hubs.len() > 1 {
            for g in hubs
                .iter()
                .flat_map(|h| relation.free_set(h).into_iter().flatten())
            {
                if !exact(g) {
                    return None;
                }
                core.insert(g.clone());
            }
        }
        let core: Vec<Arc<Formula>> = core.into_iter().collect();
        let (bound, _) = self.core_leaf_bound(&core)?;
        bound.only().cloned()
    }

    /// Whether class `c`'s conjuncts give its leaf the same bound in the relation as in `old`,
    /// the relation at the last projection, as [`Scope::core_leaf_bound`] finds it, with the
    /// record of the bound now to keep ([`LeafBound`]), `None` when there is none.
    ///
    /// Complexity tradeoff: naive version, the bound found from all the class's conjuncts
    /// before and now ([`Scope::core_leaf_bound`]), two projections of each of its `k` parts
    /// per test, O(k²) projections for `k` tests that each add a conjunct among its hubs.
    /// Used: the bound kept from the last check, valid while the free conjuncts at the hubs
    /// were as kept in `old` and the products of the names they mention are as kept, found by
    /// diffs of persistent sets and maps that skip what they share; the conjuncts added among
    /// the hubs since, when none is a constraint, each add a part whose bound met with the kept
    /// one is the new bound: O(a) projections for `a` added parts, and O((c + h) log n) to check
    /// `c` changes at `h` hubs. Tradeoffs: memory for one record per class checked, shared
    /// with the relation and the names; a conjunct gone, a constraint added or a name moved
    /// finds the bound from all the conjuncts again, as before. COMPLEXITY.md row C26.
    fn leaf_bound_stays(&self, old: &Conjuncts, c: &conjuncts::Class) -> (bool, Option<LeafBound>) {
        let hubs: BTreeSet<Arc<str>> = c
            .iter()
            .flat_map(|g| conjuncts::names(g))
            .filter(|n| &**n != conjuncts::LEAF)
            .collect();
        let here = |h: &Arc<str>| {
            let set = self.relation.free_set(h).cloned().unwrap_or_default();
            (h.clone(), set)
        };
        if self.relation.class_leaves(c).next().is_none() {
            return (false, None);
        }
        if let Some(kept) = self.seen.bounds.get(c)
            && let Some(added) = self.added_among(old, &hubs, kept)
        {
            let mut bound = kept.bound.clone();
            let mut mentioned = kept.mentioned.clone();
            for g in &added {
                if !leaf_literal(g) {
                    return (false, None);
                }
                let part = Formula::and(vec![(**g).clone(), (*kept.base).clone()]);
                let Some(one) = self.part_leaf_bound(&part) else {
                    return (false, None);
                };
                bound = bound.meet(&one);
                mentioned.extend(conjuncts::names(g));
            }
            let stays = bound == kept.bound;
            let record = LeafBound {
                free: hubs.iter().map(here).collect(),
                names: self.names.view().clone(),
                mentioned,
                base: kept.base.clone(),
                bound,
            };
            return (stays, Some(record));
        }
        let (Some(then), Some(now)) = (old.class_core(c), self.relation.class_core(c)) else {
            return (false, None);
        };
        let literal = |core: &[Arc<Formula>]| core.iter().all(|g| leaf_literal(g));
        let found = literal(&now).then(|| self.core_leaf_bound(&now)).flatten();
        let stays = then == now
            || (literal(&then)
                && found.as_ref().is_some_and(|(b, _)| {
                    self.core_leaf_bound(&then).is_some_and(|(a, _)| a == *b)
                }));
        let record = found.map(|(bound, base)| LeafBound {
            free: hubs.iter().map(here).collect(),
            names: self.names.view().clone(),
            mentioned: now
                .iter()
                .flat_map(|g| conjuncts::names(g))
                .filter(|n| &**n != conjuncts::LEAF)
                .collect(),
            base,
            bound,
        });
        (stays, record)
    }

    /// The conjuncts added among `hubs` from `old` to the relation, when the record `kept` was
    /// made with the free conjuncts at the hubs as `old` has them and the names it mentions are
    /// as kept, and every change since adds a conjunct that is no constraint; `None` otherwise.
    fn added_among(
        &self,
        old: &Conjuncts,
        hubs: &BTreeSet<Arc<str>>,
        kept: &LeafBound,
    ) -> Option<BTreeSet<Arc<Formula>>> {
        let empty = imbl::OrdSet::new();
        for h in hubs {
            let was = kept.free.get(h).unwrap_or(&empty);
            if was.diff(old.free_set(h).unwrap_or(&empty)).next().is_some() {
                return None;
            }
        }
        for d in kept.names.diff(&self.names) {
            let (DiffItem::Add(n, _)
            | DiffItem::Remove(n, _)
            | DiffItem::Update { new: (n, _), .. }) = d;
            if kept.mentioned.contains(n) {
                return None;
            }
        }
        let mut added = BTreeSet::new();
        for h in hubs {
            let then = old.free_set(h).unwrap_or(&empty);
            for d in then.diff(self.relation.free_set(h).unwrap_or(&empty)) {
                match d {
                    imbl::ordset::DiffItem::Add(g) if !matches!(&**g, Formula::Con(_)) => {
                        added.insert(g.clone());
                    }
                    _ => return None,
                }
            }
        }
        Some(added)
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
            // A part that is `false` itself, as `Formula::and` folds two equations of one sum
            // with different constants, mentions no name: an empty map would say nothing of
            // the names an equal writing of it mentions and empties, so the route is not
            // taken, as for any other part not of the form below.
            let names = conjuncts::names(part);
            if names.is_empty() {
                return None;
            }
            return Some(
                names
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
        let allow_multi = self.in_case || tops.iter().any(|g| one_disjunction(g) == Some(1));
        let mut hung: Vec<Pendant> = Vec::new();
        let mut rest: Vec<Formula> = Vec::new();
        for t in &tops {
            match self.pendant(t, |n| count.get(n).copied().unwrap_or(0), allow_multi) {
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
            let pieces = self.get(n).ints().len();
            if pieces == 0 {
                return None;
            }
            disjunctions += usize::from(pieces > 1);
        }
        if disjunctions > 1 {
            return None;
        }
        if allow_multi
            && let [p] = &hung[..]
            && let Some(out) = self.unbounded_unit(p, &rest)
        {
            if out.iter().all(|(_, d)| d.is_empty()) {
                // No conjunction of what is left has a point, so neither has `part`: each of
                // its names is empty, as below where the whole is `false`, not only the names
                // of the pendant and its form.
                return Some(
                    count
                        .into_keys()
                        .map(|n| (n, IntervalSet::empty()))
                        .collect(),
                );
            }
            return Some(out);
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
    fn pendant(
        &self,
        t: &Formula,
        count: impl Fn(&str) -> usize,
        allow_multi: bool,
    ) -> Option<Pendant> {
        let Formula::Con(c) = t else { return None };
        let mut lone = None;
        let mut multiple = false;
        for (a, k) in &c.lin.terms {
            let Atom::Sym(n) = a else { return None };
            if count(n) == 1 {
                multiple |= lone.replace((n, k)).is_some();
            }
        }
        // Preserve the ordinary unique-pendant route without domain scans.
        // If several coordinates are pendant, retain finite convex unit
        // coordinates in the form only when exactly one is a free half-line.
        // Complexity tradeoff: main rejects a row with multiple pendant
        // coordinates. Select its unique free half-line and retain finite,
        // convex unit coordinates in the form, using the same exact image-
        // of-hulls argument as the original route. Selection costs O(v),
        // followed by the original solver, not a new elimination algorithm.
        // Measured in review round 3 of PERF-l139-wake (allocator calls, 8n ratio): hopb/hoponb R=14.66/14.53 without, 12.75/12.65 with;
        // both-size totals increase about 18-19k here, largely startup work.
        // This measured ratio gain is not an asymptotic complexity claim.
        let (x, k) = if multiple {
            if !allow_multi || c.rel != Rel::Ge {
                return None;
            }
            let mut free = None;
            for (a, k) in &c.lin.terms {
                let Atom::Sym(n) = a else { return None };
                if count(n) != 1 {
                    continue;
                }
                let p = self.get(n);
                if k.abs() != Int::ONE || classed(&p) {
                    return None;
                }
                let (l, h) = p.ints().only()?;
                let unbounded = (*k == Int::ONE && *h == End::PosInf)
                    || (*k == -&Int::ONE && *l == End::NegInf);
                if unbounded && free.replace((n, k)).is_some() {
                    return None;
                }
            }
            free?
        } else {
            lone?
        };
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
    // Complexity tradeoff: the old method invokes integer elimination for every
    // stale punctured-line part. This boundary-support certificate instead reads
    // its two-name line and the base rows, O(arms + rows), independent of the
    // number of other parts. It is not entailment (the punctured-line rule of review round 1, which changed answers):
    // it proves every marginal value has support even with the base present.
    // This uses plan row PERF-l139-family's interval-constraint-propagation idea, with exact
    // integer fibers rather than the residual supports of AC-2001 (Bessiere, Regin,
    // Yap and Zhang, "An optimal coarse-grained arc consistency algorithm", Artificial
    // Intelligence 165(2), 2005) or watched literals.
    // Review round 3 of PERF-l139-wake, with a finite optimizer not kept: omitting this gives hop
    // R=21.38, hopon=22.08, hopb=35.29, hoponb=35.36; retaining it gives
    // 8.62, 8.89, 12.62, 12.66. Without that finite optimizer, the kept
    // source measures 10.55, 11.32, 12.75, 12.65. User scans still preclude
    // a global linear bound.
    // One half-plane cuts each fiber at only one end; a singleton fiber must
    // therefore be at a box edge. Only exact line/edge intersections can lose
    // support. The pendant's current lower end has a separate constructed
    // witness. No skipped projection changes a product or the again rule.
    fn puncture_idle(&self, b: &Block, g: &Formula) -> bool {
        self.puncture_support(b, g).unwrap_or(false)
    }

    fn puncture_support(&self, b: &Block, g: &Formula) -> Option<bool> {
        let Formula::Or(arms) = g else { return None };
        let c = arms.iter().find_map(|a| match a {
            Formula::Con(c) if c.rel == Rel::Ge && c.lin.terms.len() == 2 => Some(c),
            _ => None,
        })?;
        if !arms.iter().any(|a| {
            matches!(a, Formula::Con(d)
            if d.rel == Rel::Ge && d.lin.terms.len() == c.lin.terms.len()
                && d.lin.terms.iter().zip(&c.lin.terms).all(|((n,k),(m,j))|
                    n == m && k.is_positive() != j.is_positive() && *k == -j)
                && &d.lin.constant + &c.lin.constant == -&Int::from(2))
        }) {
            return None;
        }
        let mut ts = c.lin.terms.iter();
        let (Atom::Sym(x), p) = ts.next()? else {
            return None;
        };
        let (Atom::Sym(y), q) = ts.next()? else {
            return None;
        };
        let forbidden = &-&c.lin.constant - &Int::ONE;
        let domain = |n: &str| -> Option<(Int, Int)> {
            let v = self.get(n);
            if classed(&v) || v.ints().len() != 1 {
                return None;
            }
            let (End::Fin(lo), End::Fin(hi)) = v.ints().bounds()? else {
                return None;
            };
            Some((Int::from(lo), Int::from(hi)))
        };
        let (xd, yd) = (domain(x)?, domain(y)?);
        let mut row: Option<&Con> = None;
        let mut pendant: Option<&Con> = None;
        for f in &b.cons {
            let Formula::Con(r) = &**f else { return None };
            if r.rel != Rel::Ge {
                return None;
            }
            if b.leaf
                .as_ref()
                .is_some_and(|n| r.lin.terms.contains_key(&Atom::Sym(n.clone())))
            {
                if pendant.replace(r).is_some() {
                    return None;
                }
            } else if r.lin.terms.len() == 1 {
                let (Atom::Sym(n), k) = r.lin.terms.iter().next()? else {
                    return None;
                };
                let v = self.get(n);
                if classed(&v) {
                    return None;
                }
                let (lo, hi) = v.ints().bounds()?;
                let End::Fin(e) = (if k.is_positive() { lo } else { hi }) else {
                    return None;
                };
                if &r.lin.constant + &(k * &Int::from(e)) < Int::ZERO {
                    return None;
                }
            } else {
                if r.lin
                    .terms
                    .keys()
                    .any(|a| !matches!(a, Atom::Sym(n) if n == x || n == y))
                {
                    return None;
                }
                row = Some(match row {
                    Some(old) if old.lin.terms != r.lin.terms => return None,
                    Some(old) if old.lin.constant < r.lin.constant => old,
                    _ => r,
                });
            }
        }
        let coefficient = |r: &Con, n: &Arc<str>| {
            r.lin
                .terms
                .get(&Atom::Sym(n.clone()))
                .cloned()
                .unwrap_or(Int::ZERO)
        };
        let (a, d, e) = row
            .map(|r| (coefficient(r, x), coefficient(r, y), r.lin.constant.clone()))
            .unwrap_or((Int::ZERO, Int::ZERO, Int::ZERO));
        // The feasible fiber in v when u is fixed, using integer floor/ceiling.
        let fiber = |u: &Int, au: &Int, av: &Int, bounds: &(Int, Int)| -> Option<(Int, Int)> {
            let mut lo = bounds.0.clone();
            let mut hi = bounds.1.clone();
            let t = -&(&e + &(au * u));
            if av.is_positive() {
                lo = lo.max(-&(-&t).div_floor(av));
            } else if av.is_negative() {
                hi = hi.min(t.div_floor(av));
            } else if t.is_positive() {
                return None;
            }
            (lo <= hi).then_some((lo, hi))
        };
        for (u, v, pu, pv, au, av) in [(&xd, &yd, p, q, &a, &d), (&yd, &xd, q, p, &d, &a)] {
            // Half-plane projection is an interval; supported ends support its interior.
            fiber(&u.0, au, av, v)?;
            fiber(&u.1, au, av, v)?;
            for edge in [&v.0, &v.1] {
                let t = &forbidden - &(pv * edge);
                if t.mod_floor(pu) != Int::ZERO {
                    continue;
                }
                let at = t.div_floor(pu);
                if at < u.0 || at > u.1 {
                    continue;
                }
                let (lo, hi) = fiber(&at, au, av, v)?;
                if lo == hi && &lo == edge {
                    return Some(false);
                }
            }
        }
        if let Some(r) = pendant {
            let leaf = b.leaf.as_ref()?;
            if coefficient(r, leaf) != Int::ONE {
                return None;
            }
            let lp = self.get(leaf);
            if classed(&lp) || lp.ints().len() != 1 {
                return None;
            }
            let (End::Fin(low), End::PosInf) = lp.ints().bounds()? else {
                return None;
            };
            // Construct one minimising box edge, clamped by the base half-plane.
            let cx = coefficient(r, x);
            let cy = coefficient(r, y);
            let vx = if cx.is_negative() { &xd.0 } else { &xd.1 };
            let (lo, hi) = fiber(vx, &a, &d, &yd)?;
            let vy = if cy.is_negative() { lo } else { hi };
            if &(p * vx) + &(q * &vy) == forbidden {
                return Some(false);
            }
            let mut value = &r.lin.constant + &Int::from(low);
            for (atom, k) in &r.lin.terms {
                let Atom::Sym(n) = atom else { return None };
                if n == leaf {
                    continue;
                }
                let v = if n == x {
                    vx.clone()
                } else if n == y {
                    vy.clone()
                } else {
                    let (lo, hi) = domain(n)?;
                    if k.is_negative() { lo } else { hi }
                };
                value = &value + &(k * &v);
            }
            if value < Int::ZERO {
                return Some(false);
            }
        }
        Some(true)
    }

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
        // The text of `part`, each name as written, with the names of the scope it mentions,
        // made once, and only when a question about it is refused.
        let mut text: Option<(Arc<str>, Vec<Arc<str>>)> = None;
        let mut refuse = |s: &mut Scope, asked: Asked, cause: presburger::Refusal, kept: Kept| {
            let (constraint, on) = text.get_or_insert_with(|| {
                let written: Arc<str> = part.written(written_name).into();
                let on = mentioned(&written, syms_of(part));
                (written, on)
            });
            let r = Refused {
                constraint: constraint.clone(),
                asked,
                cause: cause.into(),
            };
            s.refuse(r, kept, on);
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
    ///
    /// Returns whether the names may have changed: false only when no constraint was
    /// enumerated and the scope is not exact, so that [`Scope::reduce_with`] need not look
    /// for the names it changed.
    fn enumerate(&mut self) -> bool {
        let now = (
            self.names.view().clone(),
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
            return self.exact;
        }
        self.enumerate_on(pending);
        true
    }

    fn enumerate_on(&mut self, pending: Vec<(Term, Vec<Arc<str>>, Enumerated)>) {
        let int = Type::int();
        for (c, open, key) in pending {
            let at = |extra: Option<(&Arc<str>, i64)>| {
                #[cfg(feature = "counts")]
                super::preimage::counts::EVALUATIONS
                    .set(super::preimage::counts::EVALUATIONS.get() + 1);
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
            // A constraint that gives neither `true` nor `false` at a root of an obligation's
            // equation is reported, since it then cannot say whether the root is reached
            // ([`Scope::zero_reached`]); as at any other member, the member is not kept.
            match &open[..] {
                [] => {
                    let gave = at(None);
                    if !matches!(gave, Ok(Value::Bool(_)))
                        && let Some((n, Value::Int(v))) =
                            key.1.iter().find(|(n, _)| self.rooted.contains(n))
                    {
                        self.root_failures
                            .insert(root_failure(&key, n, *v, gave.clone()));
                    }
                    if let Ok(v) = gave
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
                    let rooted = self.rooted.contains(n);
                    let mut kept: Vec<i64> = Vec::with_capacity(vs.len());
                    for &v in &vs {
                        match at(Some((n, v))) {
                            Ok(Value::Bool(true)) => kept.push(v),
                            Ok(Value::Bool(false)) => {}
                            gave if rooted => {
                                self.root_failures.insert(root_failure(&key, n, v, gave));
                            }
                            _ => {}
                        }
                    }
                    if kept.len() < vs.len() {
                        let x = IntervalSet::from_pieces(
                            kept.iter().map(|&v| (End::of(v), End::of(v))).collect(),
                        );
                        let p = self.names.get_mut(n).expect("a name in scope");
                        let prem = p.premises();
                        p.meet_ints(x, &prem);
                    }
                    // One member kept makes `n` static, and the constraint then has another
                    // key, with `n` among its static names: it gave `true` there just now, so
                    // it is not evaluated at that member a second time.
                    if let [v] = kept[..] {
                        let mut statics: BTreeMap<Arc<str>, Value> =
                            key.1.iter().cloned().collect();
                        statics.insert(n.clone(), Value::Int(v));
                        self.enumerated
                            .insert((key.0.clone(), statics.into_iter().collect()));
                    }
                }
                _ => continue,
            }
            self.enumerated.insert(key);
        }
    }
}

/// The report that the written constraint of `key` gave `gave`, neither `true` nor `false`,
/// at the root `v` of `n` ([`Scope::zero_reached`]): the constraint as written.
fn root_failure(
    key: &Enumerated,
    n: &Arc<str>,
    v: i64,
    gave: Result<Value, zed_kernel::KernelError>,
) -> RootFailure {
    let k = key.0.term();
    let free = stage::free(k);
    RootFailure {
        name: written_name(n).into(),
        root: v,
        constraint: print::written(k, written_name, &|x| free.contains(x)).into(),
        gave: match gave {
            Ok(w) => w.to_string(),
            Err(e) => e.to_string(),
        }
        .into(),
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
        // Complexity tradeoff: naive version, each atom's text written, about 10,000
        // instructions for `n > 3`, though texts are read only to order two atoms of one
        // height. Used: a tree of one atom writes none, the order of one node being fixed;
        // a tree of two atoms or more writes each once, as before, O(s) for `s` parts. Test:
        // `l01_39_reduced_product::deep_let::the_arms_of_a_deep_block_scale`, COMPLEXITY.md
        // row PA-bind-cost.
        let ordered = nodes
            .iter()
            .filter(|n| matches!(n.kind, Kind::Atom))
            .count()
            > 1;
        let mut height = vec![0usize; nodes.len()];
        let mut texts = vec![String::new(); nodes.len()];
        for i in (0..nodes.len()).rev() {
            let below = |k: &(usize, bool)| height[k.0] + 1;
            height[i] = match &nodes[i].kind {
                Kind::Nest(_, sides) => sides.iter().map(below).max().unwrap_or(1),
                Kind::If(arms) => arms.iter().map(below).max().unwrap_or(1),
                Kind::Atom => {
                    if ordered {
                        texts[i] = nodes[i].term.to_string();
                    }
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
                    balanced(p, sides.iter().map(|&s| take(s)).collect())
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

/// `t`, or `!t` when `pol` is false.
fn signed(t: Term, pol: bool) -> Term {
    if pol {
        t
    } else {
        Term::Prim(Prim::Not, vec![t])
    }
}

/// `t`, or when `negate` its negation as a program would write it: a comparison turned
/// around (`x < 1` for `!(x >= 1)`), `&&` and `||` by De Morgan's laws, a `!` dropped, and
/// any other test under a `!`. For the texts of a message, which name the alternatives of a
/// test that narrows by its `false` outcome. O(the size of `t`).
fn negated_if(t: &Term, negate: bool) -> Term {
    if !negate {
        return t.clone();
    }
    match t {
        Term::Prim(p, a) if a.len() == 2 => {
            let q = match p {
                Prim::Lt => Prim::Ge,
                Prim::Le => Prim::Gt,
                Prim::Gt => Prim::Le,
                Prim::Ge => Prim::Lt,
                Prim::Eq => Prim::Ne,
                Prim::Ne => Prim::Eq,
                Prim::And => Prim::Or,
                Prim::Or => Prim::And,
                _ => return Term::Prim(Prim::Not, vec![t.clone()]),
            };
            let a = match q {
                Prim::And | Prim::Or => a.iter().map(|x| negated_if(x, true)).collect(),
                _ => a.clone(),
            };
            Term::Prim(q, a)
        }
        Term::Prim(Prim::Not, a) if a.len() == 1 => a[0].clone(),
        _ => Term::Prim(Prim::Not, vec![t.clone()]),
    }
}

/// `t` written as a program writes it, with the parentheses the operators' precedence needs
/// and no others: `x - y >= 1 || x >= 0`. Comparisons, `+`, `-`, `*`, `-x`, `&&`, `||`, `!`,
/// names and integers are written here; any other term is `other` of it, in parentheses
/// below an operator. O(the size of `t`) besides `other`.
fn plain_text(t: &Term, other: &dyn Fn(&Term) -> String) -> String {
    /// `t` inside an operator of precedence `at`: 1 `||`, 2 `&&`, 3 comparisons, 4 `+ -`,
    /// 5 `*`, 6 a prefix operator.
    fn go(t: &Term, at: u8, other: &dyn Fn(&Term) -> String, out: &mut String) {
        let binary = |p: Prim| match p {
            Prim::Or => Some((1, "||")),
            Prim::And => Some((2, "&&")),
            Prim::Eq => Some((3, "==")),
            Prim::Ne => Some((3, "!=")),
            Prim::Lt => Some((3, "<")),
            Prim::Le => Some((3, "<=")),
            Prim::Gt => Some((3, ">")),
            Prim::Ge => Some((3, ">=")),
            Prim::Add => Some((4, "+")),
            Prim::Sub => Some((4, "-")),
            Prim::Mul => Some((5, "*")),
            _ => None,
        };
        let (p, a): (Prim, Vec<&Term>) = match t {
            Term::Prim(p, a) => (*p, a.iter().collect()),
            Term::If(..) => match connective(t) {
                Some((and, [(x, px), (y, py)])) if py => {
                    let x = if px { x.clone() } else { negated_if(x, true) };
                    let op = if and { Prim::And } else { Prim::Or };
                    return go(&Term::Prim(op, vec![x, y.clone()]), at, other, out);
                }
                _ => return paren(&other(t), at, out),
            },
            Term::Var(n) => return out.push_str(written_name(n)),
            Term::Lit(Value::Int(k)) => return out.push_str(&k.to_string()),
            _ => return paren(&other(t), at, out),
        };
        match (p, &a[..]) {
            (Prim::Neg | Prim::Not, [x]) => {
                out.push(if p == Prim::Neg { '-' } else { '!' });
                go(x, 6, other, out);
            }
            (_, [x, y]) if binary(p).is_some() => {
                let (q, op) = binary(p).expect("matched");
                if q < at {
                    out.push('(');
                }
                // Comparisons do not chain, and `-` is not associative: the right side of
                // either, and the left side of a comparison, are one level up.
                go(x, if q == 3 { 4 } else { q }, other, out);
                out.push_str(&format!(" {op} "));
                go(
                    y,
                    if q == 3 || p == Prim::Sub { q + 1 } else { q },
                    other,
                    out,
                );
                if q < at {
                    out.push(')');
                }
            }
            _ => paren(&other(t), at, out),
        }
    }
    fn paren(s: &str, at: u8, out: &mut String) {
        match at > 0 && s.contains(' ') && !(s.starts_with('(') && s.ends_with(')')) {
            true => out.push_str(&format!("({s})")),
            false => out.push_str(s),
        }
    }
    let mut out = String::new();
    go(t, 0, other, &mut out);
    out
}

/// The connective `p` over `sides`, nested in a balanced way: depth logarithmic in their
/// number. `sides` is not empty.
fn balanced(p: Prim, mut level: Vec<Term>) -> Term {
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

/// The join of `cases`, each reduced, in pairs, so that no case is copied through more than
/// `log k` joins of `k` cases. No join is reduced: each case is reduced already, and every
/// caller reduces the scope the narrowing gives ([`Scope::assume`], [`Scope::assume_case`],
/// and each case of [`Scope::cases`]); [`Scope::narrow_linear`] puts the test's relation in
/// place of the join's first.
///
/// Complexity tradeoff: the naive method reduced each join that is joined again. A join at
/// level `j` holds the disjunction of `2^j` cases, and reducing it projects every side again,
/// each projection asking `O(log k)` questions of the hull's bisection, so that the joins cost
/// `Θ(k log² k)` projections of sides for `k` cases (bytes 14.3 times from 32 to 256 live
/// sides `n + m >= -i`, above the limit of 14.1). Here the joins are only joined, `O(k log k)`
/// for the copies of the cases' conjuncts, and the one reduction is the caller's. Given up:
/// nothing; over the groups that narrow by disjunctions, every answer is the same with and
/// without the reductions of the joins (NARROW-many-relational-sides).
fn join_cases(mut cases: Vec<Scope>) -> Scope {
    while cases.len() > 1 {
        let mut it = std::mem::take(&mut cases).into_iter();
        while let Some(l) = it.next() {
            cases.push(match it.next() {
                Some(r) => l.join(&r),
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
/// it, excluded by complement in the type, the interval and the finite set. Gives whether the
/// interval changed.
fn equality(p: &mut Product, v: &Value, equal: bool, prem: &Premises) -> bool {
    if equal {
        let lit = Product::literal(v);
        p.ty.meet(&lit.ty.element, prem);
        p.cell.finite.meet(&lit.cell.finite.element, prem);
        let mut met = false;
        if let Some(n) = int_lit(v) {
            met = p.meet_ints(IntervalSet::point(n.clone()), prem);
            p.cell.congruence.meet(&Congruence::single(n), prem);
        }
        return met;
    }
    if let Some(lit) = Type::lit(v) {
        p.ty.meet(&!&lit, prem);
    }
    let mut met = false;
    if let Value::Int(n) = v {
        let x = IntervalSet::single(*n).complement_in(p.ints());
        met = p.meet_ints(x, prem);
    }
    if let FiniteSet::Set(vs) = &p.cell.finite.element {
        let mut vs = vs.clone();
        vs.remove(v);
        p.cell.finite.meet(&FiniteSet::Set(vs), prem);
    }
    met
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
///
/// Complexity tradeoff: naive version, plain recursion on the thread's stack, O(d) time and
/// O(d) stack frames for a term d deep, which overflowed a 2 MiB thread at about 670 bindings.
/// Used: the same calls in the same order as boxed futures on a heap stack, O(d) time and
/// O(d) heap, no depth limit (COMPLEXITY.md row PA-let-stack). Tradeoffs: one allocation and
/// one `RefCell` check per frame, a constant factor; measured at equal sizes on a 4 GiB stack
/// the two were within a factor of 1.4 either way (arms of 8,000 tests 3.18 s recursive
/// against 2.27 s here, forward of a block of 100,000 4.51 s against 4.52 s).
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
    /// The premise of each test the walk has met, in the order met ([`Run::walk_value_at`]).
    premises: RefCell<Vec<Premises>>,
    /// Whether [`Run::walk_value`] takes the value of an `if` with a literal in each arm from
    /// the arms it reached; off only in the reference walk of the test that checks it
    /// (`arms_and_value_by_transfer`, built with the feature `preimage-ref`).
    shortcut: bool,
}

impl<'m> Run<'m> {
    fn new(scope: &'m mut Scope) -> Self {
        Run {
            stack: Stack::default(),
            outer: RefCell::new(scope),
            inner: RefCell::new(Vec::new()),
            out: RefCell::new(Vec::new()),
            count: std::cell::Cell::new(0),
            premises: RefCell::new(Vec::new()),
            shortcut: true,
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
            Term::If(c, a, b)
                if self.shortcut && matches!((&**a, &**b), (Term::Lit(_), Term::Lit(_))) =>
            {
                let reached = self.walk_if(c, a, b).await;
                let value = |reached: bool, arm: &Term| match arm {
                    Term::Lit(v) if reached => Product::literal(v),
                    _ => Product::bottom(),
                };
                let mut p = value(reached[0], a);
                p.join(&value(reached[1], b));
                p
            }
            // Each arm's value is found as the walk walks it, in the arm's scope, which holds
            // the premises of the tests met since the walk entered this `if`; the value of the
            // transfer, which assumes those tests with no premise, is the join without them.
            // A union only adds premises, and a premise changes no element, so the transfer's
            // value has the same elements and the premises of this one but those.
            //
            // Complexity tradeoff: the naive value walks the arms and then reads the whole
            // `if` again with the transfer (`Run::forward`), which binds each `let` below once
            // more: `O(d²)` bindings for `d` such `if`s nested in arms, each binding read again
            // by each `if` above it. Here each arm is read once, and the premises of the tests
            // below are dropped from the value (`Premises::without`), which enters only the
            // parts of its premises made since the walk entered the `if`: `O(1)` a level when
            // each level's value rests on its own test and those above. Given up: none in the
            // elements; a value whose premises below are many unions pays for entering them at
            // each `if` above that does not drop them first. Trigger: an `if` whose arms are
            // not each a literal. Test:
            // `l01_39_reduced_product::if_shortcut::one_pass_and_transfer_scale_on_deep_nests`,
            // COMPLEXITY.md row PA-walk-nest-cost. The reference walk
            // (`arms_and_value_by_transfer`) keeps the naive value.
            Term::If(c, a, b) if self.shortcut => {
                let from = self.premises.borrow().len();
                let [p, q] = self.walk_if_value(c, a, b).await;
                let mut p = p;
                p.join(&q);
                let premises = self.premises.borrow();
                p.without(&premises[from..])
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
        self.walk_arms(c, a, b, false)
            .await
            .map(|(reached, _)| reached)
    }

    /// [`Run::walk_if`], with the value of each arm in its scope ([`Run::walk_value`]), the
    /// true arm first.
    async fn walk_if_value(&'m self, c: &'m Term, a: &'m Term, b: &'m Term) -> [Product; 2] {
        (self.walk_arms(c, a, b, true).await).map(|(_, p)| p.unwrap_or_else(Product::bottom))
    }

    /// The walk of [`Run::walk_if`], each arm walked for its value too when `value` is set.
    async fn walk_arms(
        &'m self,
        c: &'m Term,
        a: &'m Term,
        b: &'m Term,
        value: bool,
    ) -> [(bool, Option<Product>); 2] {
        let count = self.count.get();
        self.count.set(count + 1);
        let at = FactAddress {
            node: NodeAddress(Vector::unit(Position::root().child(count))),
            keypath: Vector::new(),
        };
        let prem = Premises::one(Premise::Constraint(at));
        self.premises.borrow_mut().push(prem.clone());
        let mut out = [(false, None), (false, None)];
        // Complexity tradeoff: naive version, the test printed for each arm, twice an `if`,
        // about 10,000 instructions each for `(n > 37)`. Used: printed once and copied for the
        // true arm, the same text. Test:
        // `l01_39_reduced_product::deep_let::the_arms_of_a_deep_block_scale`, COMPLEXITY.md row
        // PA-bind-cost.
        let mut guard = c.to_string();
        for (i, (o, arm)) in [(true, a), (false, b)].into_iter().enumerate() {
            let s = self.scope(|s| s.assume(c, o, &prem));
            out[i].0 = !s.bottom;
            self.out.borrow_mut().push(Arm {
                guard: if o {
                    guard.clone()
                } else {
                    std::mem::take(&mut guard)
                },
                outcome: o,
                scope: s.clone(),
            });
            self.inner.borrow_mut().push(s);
            if value {
                out[i].1 = Some(self.walk_value(arm).await);
            } else {
                self.walk(arm).await;
            }
            self.inner.borrow_mut().pop();
        }
        out
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

/// The arms of `term` ([`arms`]) and its value, as the walk finds both in one pass: an `if`
/// with a literal in each arm takes its value from the arms the walk reached, and a `let`
/// binds its value once. For the test that compares this with [`arms_and_value_by_transfer`]
/// (PA-if-shortcut-diff). Built only with the feature `preimage-ref`.
#[cfg(feature = "preimage-ref")]
#[doc(hidden)]
pub fn arms_and_value(term: &Term, scope: &Scope) -> (Vec<Arm>, Product) {
    let mut scope = scope.clone();
    let run = Run::new(&mut scope);
    let p = run.stack.run(run.walk_value(term));
    (run.out.take(), p)
}

/// The arms of `term` and its value as the walk finds them without its shortcut for an `if`
/// with a literal in each arm: such an `if`, as any other, is walked for its arms and then
/// given its value by the forward transfer ([`forward`]), which assumes its test again, with no
/// premise. Each `let` binds its value once, as in [`arms_and_value`], so the two cost the same
/// order. The reference for the test of the shortcut (PA-if-shortcut-diff); built only with the
/// feature `preimage-ref`.
#[cfg(feature = "preimage-ref")]
#[doc(hidden)]
pub fn arms_and_value_by_transfer(term: &Term, scope: &Scope) -> (Vec<Arm>, Product) {
    let mut scope = scope.clone();
    let mut run = Run::new(&mut scope);
    run.shortcut = false;
    let p = run.stack.run(run.walk_value(term));
    (run.out.take(), p)
}

#[cfg(feature = "preimage-ref")]
impl Product {
    /// One round of the reductions between the product's own domains; whether one changed a
    /// domain. For the test that compares this flag with a comparison of the product before
    /// and after (PA-if-shortcut-diff).
    #[doc(hidden)]
    pub fn reduce_domains_once(&mut self) -> bool {
        self.reduce_domains()
    }
}

/// Whether `p` has a class other than all integers, or than the one value its interval is.
/// The leaf and row of `(x - y >= gap && y >= start) || y <= low` with `low < start`, the
/// sides and the conjuncts in either order ([`PendantRow`]). O(1): two sides of two conjuncts.
fn pendant_row(f: &Formula) -> Option<(Arc<str>, PendantRow)> {
    let Formula::Or(sides) = f else {
        return None;
    };
    let [a, b] = &sides[..] else {
        return None;
    };
    let one = |c: &Con| -> Option<(Arc<str>, Int)> {
        let [(Atom::Sym(n), k)] = c.lin.terms.iter().collect::<Vec<_>>()[..] else {
            return None;
        };
        (c.rel == Rel::Ge).then(|| (n.clone(), k.clone()))
    };
    for (upper, both) in [(a, b), (b, a)] {
        let (Formula::Con(upper), Formula::And(both)) = (upper, both) else {
            continue;
        };
        // `low - y >= 0`.
        let Some((leaf, k)) = one(upper) else {
            continue;
        };
        if k != Int::from(-1) {
            continue;
        }
        let low = upper.lin.constant.clone();
        let [c, d] = &both[..] else {
            continue;
        };
        for (lower, edge) in [(c, d), (d, c)] {
            let (Formula::Con(lower), Formula::Con(edge)) = (lower, edge) else {
                continue;
            };
            // `y - start >= 0`.
            if one(lower) != Some((leaf.clone(), Int::from(1))) {
                continue;
            }
            let start = -&lower.lin.constant;
            // `x - y - gap >= 0`.
            if edge.rel != Rel::Ge || edge.lin.terms.len() != 2 {
                continue;
            }
            if edge.lin.terms.get(&Atom::Sym(leaf.clone())) != Some(&Int::from(-1)) {
                continue;
            }
            let Some(hub) = edge.lin.terms.iter().find_map(|(a, k)| match a {
                Atom::Sym(n) if *n != leaf && *k == Int::from(1) => Some(n.clone()),
                _ => None,
            }) else {
                continue;
            };
            if low >= start {
                continue;
            }
            let gap = -&edge.lin.constant;
            return Some((
                leaf,
                PendantRow {
                    hub,
                    low,
                    start,
                    gap,
                },
            ));
        }
    }
    None
}

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
/// interval or none: `O(1)`, kept by the set ([`IntervalSet::max_gap`]).
fn hole_gap(ints: &IntervalSet) -> Int {
    Int::from(&ints.max_gap())
}

/// The greatest integer of `ints` at or below `z`, if any, in O(log p) for its `p` pieces.
fn snap_down(ints: &IntervalSet, z: &Int) -> Option<Int> {
    let v = End::Fin(Num::from(z));
    let (_, hi) = ints.piece_at_or_below(&v)?;
    Some(match hi {
        End::Fin(h) if *hi < v => Int::from(h),
        _ => z.clone(),
    })
}

/// The least integer of `ints` at or above `z`, if any, in O(log p) for its `p` pieces.
fn snap_up(ints: &IntervalSet, z: &Int) -> Option<Int> {
    let v = End::Fin(Num::from(z));
    let (lo, _) = ints.piece_at_or_above(&v)?;
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
    !(plain && ints.len() == 1)
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

/// Marginals of lower threshold clauses with at most one upper unit-sum row.
/// Under x+y<=c, x>=a || y>=b excludes (c-b,a) from x and its reflection
/// (c-a,b) from y. Starting with intervals, paired deletions preserve support
/// at y=c-x, clamped to the original endpoints. With unchanged endpoints and
/// both arms feasible, the union of these gaps gives the exact marginals.
// Complexity tradeoff: replaying k parts and recording their snapshots in each
// case costs O(k) projections and O(k log k) records per test. Apply only the
// new clause's two gaps in O(log k) persistent interval-tree work; an upper
// sum added after k clauses creates their gaps once in O(k log k). No earlier
// part or snapshot is visited: reflected supports prove it cannot narrow.
// A certificate is used only while the whole relation and both domains match;
// otherwise the original worklist, including its again rule, runs unchanged.
#[derive(Clone, Default, PartialEq, Debug)]
struct LowerGaps {
    relation: imbl::OrdSet<Arc<Formula>>,
    pairs: imbl::OrdMap<NamePair, usize>,
    other: imbl::OrdSet<Arc<Formula>>,
    upper: imbl::OrdMap<Arc<Formula>, Int>,
    at: Option<(NamePair, IntervalSet, IntervalSet)>,
}

/// Avoid constructing a second linear relation for tests outside the fragment.
fn lower_gap_syntax(test: &Term) -> bool {
    let unary = |t: &Term| {
        matches!(t, Term::Prim(Prim::Ge, a)
        if matches!(&a[..], [Term::Var(_), Term::Lit(Value::Int(_) | Value::Big(_))]))
    };
    match test {
        Term::Prim(Prim::Or, a) => matches!(&a[..], [x, y] if unary(x) && unary(y)),
        Term::Prim(Prim::Le, a) => {
            matches!(&a[..], [Term::Prim(Prim::Add, ns), Term::Lit(Value::Int(_) | Value::Big(_))]
            if matches!(&ns[..], [Term::Var(_), Term::Var(_)]))
        }
        _ => false,
    }
}

/// A lower threshold disjunction on distinct names, in name order.
fn lower_row(g: &Formula) -> Option<(NamePair, Int, Int)> {
    let Formula::Or(arms) = g else { return None };
    let [left, right] = &arms[..] else {
        return None;
    };
    let unary = |g: &Formula| {
        let Formula::Con(c) = g else { return None };
        if c.rel != Rel::Ge {
            return None;
        }
        let mut ts = c.lin.terms.iter();
        let (Some((Atom::Sym(n), k)), None) = (ts.next(), ts.next()) else {
            return None;
        };
        k.is_positive()
            .then(|| (n.clone(), -&c.lin.constant.div_floor(k)))
    };
    let ((x, a), (y, b)) = (unary(left)?, unary(right)?);
    if x < y {
        Some(((x, y), a, b))
    } else if y < x {
        Some(((y, x), b, a))
    } else {
        None
    }
}

fn upper_sum(g: &Formula) -> Option<(NamePair, Int)> {
    let Formula::Con(c) = g else { return None };
    if c.rel != Rel::Ge {
        return None;
    }
    let mut ts = c.lin.terms.iter();
    let (Some((Atom::Sym(x), p)), Some((Atom::Sym(y), q)), None) =
        (ts.next(), ts.next(), ts.next())
    else {
        return None;
    };
    (*p == -&Int::ONE && *q == -&Int::ONE).then(|| ((x.clone(), y.clone()), c.lin.constant.clone()))
}

impl LowerGaps {
    fn sync(&mut self, relation: &Conjuncts) {
        let changes: Vec<_> = self
            .relation
            .diff(relation.set())
            .map(|d| match d {
                imbl::ordset::DiffItem::Add(g) => (g.clone(), true),
                imbl::ordset::DiffItem::Remove(g) => (g.clone(), false),
            })
            .collect();
        if !changes.is_empty() {
            self.at = None;
        }
        for (g, add) in changes {
            let pair = if let Some((pair, _, _)) = lower_row(&g) {
                Some(pair)
            } else if let Some((pair, c)) = upper_sum(&g) {
                if add {
                    self.upper.insert(g.clone(), c);
                } else {
                    self.upper.remove(&g);
                }
                Some(pair)
            } else {
                if add {
                    self.other.insert(g.clone());
                } else {
                    self.other.remove(&g);
                }
                None
            };
            if let Some(pair) = pair {
                if add {
                    *self.pairs.entry(pair).or_default() += 1;
                } else if let Some(k) = self.pairs.get_mut(&pair) {
                    *k -= 1;
                    if *k == 0 {
                        self.pairs.remove(&pair);
                    }
                }
            }
        }
        self.relation = relation.set().clone();
    }

    fn holds(&self, relation: &Conjuncts, names: &imbl::OrdMap<Arc<str>, Product>) -> bool {
        self.at.as_ref().is_some_and(|((x, y), a, b)| {
            self.relation == *relation.set()
                && names.get(x).is_some_and(|p| !classed(p) && p.ints() == a)
                && names.get(y).is_some_and(|p| !classed(p) && p.ints() == b)
        })
    }
}

impl Scope {
    fn lower_gap_test(&mut self, body: &Formula, prem: &Premises) -> bool {
        if !self.written.is_empty() {
            return false;
        }
        let lower = lower_row(body);
        let upper = upper_sum(body);
        let pair = match (&lower, &upper) {
            (Some((pair, ..)), _) | (_, Some((pair, _))) => pair.clone(),
            _ => return false,
        };
        self.gaps.sync(&self.relation);
        // A bare upper sum has no reflected gaps to aggregate. Keep its ordinary
        // projection and history; start this certificate when a lower clause
        // arrives. This removes an unnecessary subcase (and the startup R rise
        // on peq), rather than switching at an input size.
        if upper.is_some() && self.gaps.pairs.is_empty() {
            return false;
        }
        if !self.gaps.other.is_empty()
            || self.gaps.upper.len() > 1
            || self.gaps.pairs.keys().any(|p| p != &pair)
        {
            return false;
        }
        let (px, py) = (self.get(&pair.0), self.get(&pair.1));
        if classed(&px) || classed(&py) {
            return false;
        }
        let (Some(xends), Some(yends)) = (px.ints().bounds(), py.ints().bounds()) else {
            return false;
        };
        // An unrelated change ends the certificate; restart only from a convex box.
        if !self.gaps.holds(&self.relation, &self.names) {
            // Begin the reflected-gap invariant only at convex domains, with no
            // lower clause already present. A sum alone is already projected.
            if self.gaps.relation.len() != self.gaps.upper.len()
                || px.ints().len() != 1
                || py.ints().len() != 1
            {
                return false;
            }
        }
        let mut x = px.ints().clone();
        let mut y = py.ints().clone();
        let mut rows = Vec::new();
        let c = if let Some((_, c)) = upper {
            if !self.gaps.upper.is_empty() {
                return false;
            }
            rows.extend(self.gaps.relation.iter().filter_map(|g| lower_row(g)));
            Some(c)
        } else {
            rows.extend(lower);
            self.gaps.upper.values().next().cloned()
        };
        if let Some(c) = &c {
            for (domain, other) in [(&mut x, yends.0), (&mut y, xends.0)] {
                if let End::Fin(lo) = other {
                    domain.clone_from(&domain.meet(&IntervalSet::range(
                        End::NegInf,
                        End::Fin(Num::from(&(c - &Int::from(lo)))),
                    )));
                }
            }
        }
        for (_, a, b) in rows {
            if xends.1 < &End::Fin(Num::from(&a)) || yends.1 < &End::Fin(Num::from(&b)) {
                return false;
            }
            if let Some(c) = &c {
                let (xl, xh) = (&(c - &b) + &Int::ONE, &a - &Int::ONE);
                let (yl, yh) = (&(c - &a) + &Int::ONE, &b - &Int::ONE);
                x = x.minus(&IntervalSet::range(
                    End::Fin(Num::from(&xl)),
                    End::Fin(Num::from(&xh)),
                ));
                y = y.minus(&IntervalSet::range(
                    End::Fin(Num::from(&yl)),
                    End::Fin(Num::from(&yh)),
                ));
            }
        }
        if x.bounds() != Some(xends) || y.bounds() != Some(yends) {
            return false;
        }
        // Unchanged lower ends keep the upper sum projected too.
        if let Some(p) = self.names.get_mut(&pair.0) {
            p.meet_ints(x.clone(), prem);
        }
        if let Some(p) = self.names.get_mut(&pair.1) {
            p.meet_ints(y.clone(), prem);
        }
        self.relation.and(body.clone());
        self.gaps.sync(&self.relation);
        self.gaps.at = Some((pair, x, y));
        true
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

/// Whether a name of product `p` is bounded below and above: a name with no product is
/// unbounded, and an empty product is bounded.
fn sides(p: Option<&Product>) -> (bool, bool) {
    match p.map(|p| p.ints().bounds()) {
        Some(Some((lo, hi))) => (*lo != End::NegInf, *hi != End::PosInf),
        Some(None) => (true, true),
        None => (false, false),
    }
}

/// The two names of `c` and its normal over them, when it has exactly two atoms, both names.
fn two_names(c: &Con) -> Option<(Factor, Factor, [Int; 2])> {
    let mut it = c.lin.terms.iter();
    let (Some((Atom::Sym(u), a)), Some((Atom::Sym(v), b)), None) =
        (it.next(), it.next(), it.next())
    else {
        return None;
    };
    Some((
        Factor::Sym(u.clone()),
        Factor::Sym(v.clone()),
        [a.clone(), b.clone()],
    ))
}

/// `a × b`, the cross product of two vectors of the plane.
fn cross(a: &[Int; 2], b: &[Int; 2]) -> Int {
    &(&a[0] * &b[1]) - &(&a[1] * &b[0])
}

/// Whether `t` is a nonnegative combination of `gens`, vectors of the plane. By Carathéodory's
/// theorem for cones it is one of at most two of them, and the two that bound it most closely
/// on each side span it if any pair does: O(m) for m vectors.
fn in_cone(t: &[Int; 2], gens: &[[Int; 2]]) -> bool {
    let mut left: Option<&[Int; 2]> = None;
    let mut right: Option<&[Int; 2]> = None;
    for g in gens {
        let s = cross(t, g);
        if s.is_zero() {
            let dot = &(&t[0] * &g[0]) + &(&t[1] * &g[1]);
            if dot.is_positive() {
                return true;
            }
        } else if s.is_positive() {
            if left.is_none_or(|l| cross(g, l).is_positive()) {
                left = Some(g);
            }
        } else if right.is_none_or(|r| cross(r, g).is_positive()) {
            right = Some(g);
        }
    }
    matches!((right, left), (Some(r), Some(l)) if cross(r, l).is_positive())
}

/// The constraints among the conjuncts of `f`.
fn rows(f: &Formula) -> impl Iterator<Item = &Con> + Clone {
    let gs = match f {
        Formula::And(gs) => gs,
        _ => std::slice::from_ref(f),
    };
    gs.iter().filter_map(|g| match g {
        Formula::Con(c) => Some(c),
        _ => None,
    })
}

/// The directions `d` holds with one name's term left out, each with that name: the name's
/// end that the direction reads is finite in `names`, so the rest of the row is bounded in
/// that direction too. `z - y - 1 >= 0` with `y >= -8` holds `z >= -7`, a row on `z` alone; an
/// equality gives both directions. The constant is kept as it was: [`Block::bounds`] reads
/// only the directions of rows. LAZY-hub-unsolved (seed 108).
fn dropped(d: &Con, names: &imbl::OrdMap<Arc<str>, Product>) -> Vec<(Con, Atom)> {
    if d.lin.terms.len() < 2 {
        return Vec::new();
    }
    let signs: &[i64] = if d.rel == Rel::Eq { &[1, -1] } else { &[1] };
    let mut out = Vec::new();
    for &s in signs {
        let lin = d.lin.times(Int::from(s));
        for (w, k) in &lin.terms {
            let Atom::Sym(n) = w else { continue };
            let Some((lo, hi)) = names.get(n).and_then(|p| p.ints().bounds()) else {
                continue;
            };
            // `k * w` is at most `k` times `w`'s upper end when `k` is positive.
            if matches!(if k.is_positive() { hi } else { lo }, End::Fin(_)) {
                let mut lin = lin.clone();
                lin.terms.remove(w);
                out.push((Con { lin, rel: Rel::Ge }, w.clone()));
            }
        }
    }
    out
}

/// Each sum of `r` and a row of `with` that holds a name `r` lacks, times
/// positive numbers (of either sign for an equality), in which a name they share cancels.
fn cancelled<'a>(r: &Con, with: impl Iterator<Item = &'a Con>) -> Vec<(Con, Atom)> {
    let mut out = Vec::new();
    let new = |c: &&Con| c.lin.terms.keys().any(|x| !r.lin.terms.contains_key(x));
    for c in with.filter(new) {
        for (x, a) in &r.lin.terms {
            let Some(b) = c.lin.terms.get(x) else {
                continue;
            };
            let (l, m) = if a.is_positive() != b.is_positive() {
                (b.abs(), a.abs())
            } else if c.rel == Rel::Eq {
                (b.abs(), -&a.abs())
            } else if r.rel == Rel::Eq {
                (-&b.abs(), a.abs())
            } else {
                continue;
            };
            let rel = if r.rel == c.rel { r.rel } else { Rel::Ge };
            out.push((
                Con {
                    lin: r.lin.times(l).plus(&c.lin.times(m)),
                    rel,
                },
                x.clone(),
            ));
        }
    }
    out
}

/// Where a disjunction stands in [`Block::bounds`]: two names in order, an end of one of them
/// (0 and 1 the lower and upper end of the first, 2 and 3 of the second), and whether a
/// constraint that bounds it turns from that end to the left (`true`) or to the right.
type BoundsKey = (Arc<str>, Arc<str>, u8, bool);
type NamePair = (Arc<str>, Arc<str>);
type Normals = Vec<[Int; 2]>;

/// A direction of the plane, ordered by its angle in (-π, π] from the positive first axis;
/// two directions are equal when they are the same however long. Directions are in the frame
/// of an end ([`turned`]), where that end is the positive first axis.
#[derive(Clone, Debug)]
struct Turn([Int; 2]);

impl Turn {
    /// The half of the circle `self` is in, in the order of the angles: below the first axis,
    /// on its positive half, above it, on its negative half.
    fn half(&self) -> u8 {
        let [x, y] = &self.0;
        if y.is_negative() {
            0
        } else if y.is_zero() && x.is_positive() {
            1
        } else if y.is_positive() {
            2
        } else {
            3
        }
    }
}

impl Ord for Turn {
    fn cmp(&self, other: &Turn) -> std::cmp::Ordering {
        // Within a half, the angle from a to b is less than π, so the sign of a × b orders them.
        self.half()
            .cmp(&other.half())
            .then_with(|| Int::from(0).cmp(&cross(&self.0, &other.0)))
    }
}

impl PartialOrd for Turn {
    fn partial_cmp(&self, other: &Turn) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Turn {
    fn eq(&self, other: &Turn) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for Turn {}

/// The normal `n` over two names in the frame of end `end` ([`BoundsKey`]), turned so that the
/// direction in which a constraint bounds that end is the positive first axis: a constraint
/// `n · (u, v) + k >= 0` bounds the lower end of `u` when `(1, 0)` is a nonnegative
/// combination of its normal and others, and the upper end when `(-1, 0)` is.
fn turned(end: u8, n: &[Int; 2]) -> [Int; 2] {
    let [a, b] = n;
    match end {
        0 => [a.clone(), b.clone()],
        1 => [-a, -b],
        2 => [b.clone(), -a],
        _ => [-b, a.clone()],
    }
}

/// One arm's rows grouped in one pass. Unary directions are reduced to their signs;
/// positive scaling preserves the cone, so many rows on one name occupy at most two slots.
#[derive(Default)]
struct ArmNormals {
    pairs: BTreeMap<NamePair, Normals>,
    unary: BTreeMap<Arc<str>, Signs>,
}

/// How many rows on one name bound it below and above, in all and among those reached by
/// eliminating each other name ([`ArmNormals::of`]).
#[derive(Default)]
struct Signs {
    all: [usize; 2],
    cut: BTreeMap<Atom, [usize; 2]>,
}

/// A row and the names eliminated to reach it.
type Derived = (Con, Vec<Atom>);

/// Each row of `rows` with each row `step` makes from it added, which also eliminates its name.
fn derive(rows: &mut Vec<Derived>, step: impl Fn(&Con) -> Vec<(Con, Atom)>) {
    let more: Vec<Derived> = (rows.iter())
        .flat_map(|(d, cut)| {
            let step = step(d).into_iter();
            step.map(|(e, x)| (e, cut.iter().cloned().chain([x]).collect()))
        })
        .collect();
    rows.extend(more);
}

impl ArmNormals {
    /// The rows of `arm`, each also added to a row of `context` and then to an equality of
    /// `context`, cancelling a name they share ([`cancelled`]), and then each of those with a
    /// name left out whose end it reads is finite in `names` ([`dropped`]).
    fn of(arm: &Formula, context: &[&Con], names: &imbl::OrdMap<Arc<str>, Product>) -> Self {
        let eqs = || context.iter().copied().filter(|c| c.rel == Rel::Eq);
        let mut out = Self::default();
        for r in rows(arm) {
            let mut ds = vec![(r.clone(), Vec::new())];
            derive(&mut ds, |d| cancelled(d, context.iter().copied()));
            derive(&mut ds, |d| cancelled(d, eqs()));
            derive(&mut ds, |d| dropped(d, names));
            for (c, cut) in &ds {
                out.add(c, cut);
            }
        }
        out
    }

    fn add(&mut self, c: &Con, cut: &[Atom]) {
        let mut it = c.lin.terms.iter();
        match (it.next(), it.next(), it.next()) {
            (Some((Atom::Sym(u), a)), Some((Atom::Sym(v), b)), None) => {
                let ns = self.pairs.entry((u.clone(), v.clone())).or_default();
                ns.push([a.clone(), b.clone()]);
                if c.rel == Rel::Eq {
                    ns.push([-a, -b]);
                }
            }
            (Some((Atom::Sym(u), a)), None, None) if !a.is_zero() => {
                let below = a.is_positive() || c.rel == Rel::Eq;
                let above = a.is_negative() || c.rel == Rel::Eq;
                let count = |counts: &mut [usize; 2]| {
                    counts[0] += usize::from(below);
                    counts[1] += usize::from(above);
                };
                let signs = self.unary.entry(u.clone()).or_default();
                count(&mut signs.all);
                for x in cut {
                    count(signs.cut.entry(x.clone()).or_default());
                }
            }
            _ => {}
        }
    }

    /// The normals of the arm's rows on `u` and `v`: those on the pair, and those on one of
    /// them alone that were not reached by eliminating the other. On the pair, a row on `u`
    /// reached by eliminating `v` through `with` reads `with`'s bound on `v`, which a
    /// constraint on `u` and `v` may narrow: at seed 108, the arm `a >= -3` with
    /// `3 * a <= z + 2` holds `z >= -11`, which the case `z >= 2 * a` narrows to `z >= -6`.
    fn on(&self, u: &Arc<str>, v: &Arc<str>) -> Vec<[Int; 2]> {
        let mut out = self
            .pairs
            .get(&(u.clone(), v.clone()))
            .cloned()
            .unwrap_or_default();
        for (axis, n, other) in [(0, u, v), (1, v, u)] {
            let Some(signs) = self.unary.get(n) else {
                continue;
            };
            let cut = signs.cut.get(&Atom::Sym(other.clone()));
            for (side, sign) in [(0, 1), (1, -1)] {
                if signs.all[side] > cut.map_or(0, |c| c[side]) {
                    let mut p = [Int::ZERO, Int::ZERO];
                    p[axis] = Int::from(sign);
                    out.push(p);
                }
            }
        }
        out
    }
}

/// The entries of the disjunction `g`, projected with `with`, in [`Block::bounds`]: for two
/// names of a row of an arm on two names (or two names of the arms' rows on one name: when
/// there are just two, or when a row of `with` is on them), and each end of each, when some
/// arm does not bound that end by its rows on the two names alone, the directions of a
/// constraint on them that makes every arm bound it. An arm's rows are its constraints, each
/// also added to a constraint of `with` and then to an equality of `with` so that a name
/// cancels, and then with a name left out whose end the row reads is finite
/// ([`ArmNormals::of`]): rows that hold in the arm
/// projected with `with`, so that a constraint reaches the part through `with` as through the
/// arm. With `x + 3 * z >= 1`, the arm `3 * x <= y` holds `y + 9 * z >= 3`, so in the case
/// `y >= 2 * z + 2` it bounds `y` below, as the arm `z >= 1` does. The constraints of `with`
/// so used are those on the names of `g`, and for each name of `g` one equality of two names
/// that holds it, which gives the arm's rows on the other name: with `a == x + 2`, the arm
/// `2 * a <= y + 1` holds `2 * x <= y - 3`, a row on `x` and `y`.
///
/// In the frame of the end ([`turned`]), an arm whose normals `N` do not hold `(1, 0)` in their
/// cone holds it in the cone of `N` and `q` exactly when `(1, 0)` lies in the cone of `q` and
/// one normal `n` of `N` (Carathéodory's theorem for cones of the plane), that is when `q`
/// lies strictly within π of `n` on the other side of the axis. The directions so allowed are
/// an open arc about the axis, from `-l` to `-r` for `l` the normal above the axis nearest it
/// and `r` the one below, closed at the axis on a side with no normal. Every arm's arc holds
/// the axis, so the arcs of the arms meet in one arc, from the greatest `-l` to the least `-r`.
/// The entry of a side is that end of the arc, none when the arc stops at the axis there.
// Complexity tradeoff: rescanning m rows for p pairs costs O(p*m); even grouping rows and
// then reading a slots per pair costs O(p*a). Grouping each arm once and counting the arms
// with rows on each pair and on each name alone costs O(m log m), and the arms are read only
// for a pair whose counts reach a, O(a) each. A missing arm contributes no entry: a non-axis
// query alone cannot bound an axis. The rows added from `with`: naive version, Fourier-Motzkin
// elimination of every other name from the arm and `with` for each pair, exponential in the
// names; or each row of the arm added to every row of `with`, O(m * w) for w rows of `with`,
// which made `persist` grow faster (R 51.0 to 55.9: its w rows `x + j * y >= -1000` sit on the
// arm's own pair), and then to every equality, O(m * w * e): a block made anew at each of k
// tests `a + b - zi == i` (its equalities change) held k of them in `with`, O(k^2) rows per
// test and O(k^3) in all (the pendants scale test, 172 times the bytes at 8n). Used: the rows
// of `with` on the names of `g` and one equality of two names for each name of `g`, chosen in
// one pass, O(w * t log s) for rows of t names and s names of `g`, so that what is added does
// not grow with the rows of `with` on other names; of those, the w' that hold a name the
// arm's row lacks, which are the ones that can carry it to a new pair, give O(m * w') rows,
// then one equality each, O(m * w' * e'), then each of those with one name left out,
// O(m * w' * e' * t). Lost: a bound that needs two inequalities of `with` chained, or a row
// of `with` with a name outside `g` other than an equality of two names (`b - zi` from
// `a + b - zi == i` and the arm `a <= 2`), or another such equality of the same name. No input
// is known that loses a bound to the last rule: LAZY-hub-cleanups compared 15 rows of a case
// on the name of a second equality with the oracle; the answers differed only at the oracle's
// window, in congruences, or in one bound that adding every such equality does not give
// either (`families::two_eq_case_against_the_oracle`, PRODUCT-two-eq-round).
// Pairs of names that only rows on one name reach: naive version, every pair
// of such names, O(s^2) for s names, quadratic on two arms of s bounds each. Used: the pair
// when there are just two, and the pairs a row of `with` is on, O(w log s); lost: a pair no
// row of `with` relates, which a case's constraint on it alone would make bound. The entries
// are kept with the part and made again when `with` changes, which already makes the part
// due (`Block::reframe`); lost: an end that becomes finite after that, until `with` changes
// again. LAZY-hub-unsolved.
fn bounds_at(
    g: &Formula,
    with: &PartWith,
    names: &imbl::OrdMap<Arc<str>, Product>,
) -> Vec<(BoundsKey, Turn)> {
    let Formula::Or(arms) = g else {
        return Vec::new();
    };
    let own = g.atoms();
    let mut context = Vec::new();
    let mut renamed = BTreeSet::new();
    // When the block has no equalities and `g` has two names, which every row of every arm
    // holds both of, the rows of `with` change no entry: the rows kept from `with` are then on
    // `g`'s two names alone (an equality is kept on other names, and the block has none: its
    // splits all share the equalities, `Block::reframe`, so `with.1` holds none when `with.0`
    // is empty), such a row holds no name an arm's row lacks, so [`cancelled`] adds no row,
    // and the pair of names it gives below is the arms' own pair, there already.
    // Complexity tradeoff: naive version, every row of `with` read and kept, then read again
    // for each row of each arm, O(w) per call for w rows of `with`: `persist`'s k disjunctions
    // on `x` and `y`, made due by each of its k constraints `x + j*y >= -1000` in their group,
    // read all of them each time, O(k^2) per test and O(k^3) in all (`bounds_at` took 14.2M
    // instructions at k = 16). Used: the arms' rows read first, O(r) for r rows, and `with`
    // not read when the rule above holds; otherwise as before. No entry changes, so no part is
    // due other than before and no answer changes. Measured (`probe_l139`, persist, k = 16):
    // 7.0M instructions fewer. Prior work: none beyond skipping a scan whose result is known.
    // The entries then read `names` only through whether the ends of the two names are finite
    // ([`dropped`]), which is what lets [`Block::reframe`] keep them when only `with` changed
    // ([`Part::pure_two_sym`]).
    let closed = with.0.is_empty()
        && own.len() == 2
        && own.iter().all(|x| matches!(x, Atom::Sym(_)))
        && arms.iter().all(|a| {
            rows(a).all(|r| r.lin.terms.len() == 2 && r.lin.terms.keys().all(|x| own.contains(x)))
        });
    if !closed {
        let with_rows: Vec<&Con> = match &with.1 {
            WithCons::None => Vec::new(),
            WithCons::Base(f) => rows(f).collect(),
            WithCons::Shared(set) => set.iter().collect(),
        };
        for c in with.0.iter().chain(with_rows) {
            let mut on = c.lin.terms.keys();
            if on.clone().all(|x| own.contains(x))
                || (c.rel == Rel::Eq
                    && c.lin.terms.len() == 2
                    && on.any(|x| own.contains(x) && renamed.insert(x.clone())))
            {
                context.push(c);
            }
        }
    }
    let grouped: Vec<ArmNormals> = arms
        .iter()
        .map(|a| ArmNormals::of(a, &context, names))
        .collect();
    // The number of arms with rows on each pair of names, and on each name alone.
    let mut held: BTreeMap<NamePair, usize> = BTreeMap::new();
    let mut ones: BTreeMap<&Arc<str>, usize> = BTreeMap::new();
    for a in &grouped {
        a.pairs
            .keys()
            .for_each(|p| *held.entry(p.clone()).or_default() += 1);
        a.unary
            .keys()
            .for_each(|n| *ones.entry(n).or_default() += 1);
    }
    // The pairs of names of rows on one name that a row of `with` is on.
    for c in &context {
        let mut it = c.lin.terms.keys();
        if let (Some(Atom::Sym(u)), Some(Atom::Sym(v)), None) = (it.next(), it.next(), it.next())
            && ones.contains_key(&u)
            && ones.contains_key(&v)
        {
            held.entry((u.clone(), v.clone())).or_default();
        }
    }
    if let [u, v] = &ones.keys().collect::<Vec<_>>()[..] {
        held.entry((Arc::clone(u), Arc::clone(v))).or_default();
    }
    let mut out = Vec::new();
    for ((u, v), k) in held {
        // An arm with no row on `u` and `v` is bounded at no end by a constraint on them.
        let alone = |n: &Arc<str>| ones.get(n).copied().unwrap_or(0);
        if k + alone(&u) + alone(&v) < arms.len() {
            continue;
        }
        let normals: Vec<Normals> = grouped.iter().map(|a| a.on(&u, &v)).collect();
        if normals.iter().any(Vec::is_empty) {
            continue;
        }
        // The direction of each end, which [`turned`] turns to the positive first axis.
        let axes = [[1, 0], [-1, 0], [0, 1], [0, -1]];
        for end in 0..4u8 {
            let axis = axes[usize::from(end)].map(Int::from);
            let (mut lo, mut hi) = (Some(None::<Turn>), Some(None::<Turn>));
            let mut gained = false;
            for ns in &normals {
                if in_cone(&axis, ns) {
                    continue;
                }
                gained = true;
                let ns = ns.iter().map(|n| turned(end, n));
                let above = ns.clone().filter(|n| n[1].is_positive());
                let below = ns.filter(|n| n[1].is_negative());
                // The nearest normal above the axis is the one no other is clockwise of.
                let l = above.min_by(|a, b| Turn(a.clone()).cmp(&Turn(b.clone())));
                let r = below.max_by(|a, b| Turn(a.clone()).cmp(&Turn(b.clone())));
                let lo_arm = l.map(|n| Turn([-&n[0], -&n[1]]));
                let hi_arm = r.map(|n| Turn([-&n[0], -&n[1]]));
                lo = match (lo, lo_arm) {
                    (Some(was), Some(now)) => Some(Some(match was {
                        Some(was) if was > now => was,
                        _ => now,
                    })),
                    _ => None,
                };
                hi = match (hi, hi_arm) {
                    (Some(was), Some(now)) => Some(Some(match was {
                        Some(was) if was < now => was,
                        _ => now,
                    })),
                    _ => None,
                };
            }
            if !gained {
                continue;
            }
            if let Some(Some(t)) = lo {
                out.push(((u.clone(), v.clone(), end, false), t));
            }
            if let Some(Some(t)) = hi {
                out.push(((u.clone(), v.clone(), end, true), t));
            }
        }
    }
    out
}

/// A persistent AVL tree of `x >= a || y <= b`, keyed by `(b, a)`. Each subtree
/// keeps its greatest `a`, so a prefix bound and a minimax bound take one search path.
/// Every tree walk follows children of strictly decreasing height, a topological order.
#[derive(Clone, Default)]
struct Staircase(Option<Arc<StairNode>>);

#[derive(Clone)]
struct StairNode {
    key: (Int, Int),
    count: usize,
    height: usize,
    size: usize,
    max_a: Int,
    left: Staircase,
    right: Staircase,
}

impl Staircase {
    /// Whether `self` and `other` are one tree in memory, so hold the same rows. A tree is
    /// never changed in place, and each holder keeps its root alive, so the address names
    /// the tree for as long as either is held. Used for identity only, never for order.
    fn same(&self, other: &Staircase) -> bool {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            (None, None) => true,
            _ => false,
        }
    }

    fn height(&self) -> usize {
        self.0.as_ref().map_or(0, |n| n.height)
    }
    fn size(&self) -> usize {
        self.0.as_ref().map_or(0, |n| n.size)
    }
    fn max_a(&self) -> Option<&Int> {
        self.0.as_ref().map(|n| &n.max_a)
    }
    fn node(key: (Int, Int), count: usize, left: Self, right: Self) -> Self {
        let mut max_a = key.1.clone();
        for v in [left.max_a(), right.max_a()].into_iter().flatten() {
            if *v > max_a {
                max_a = v.clone();
            }
        }
        Self(Some(Arc::new(StairNode {
            max_a,
            height: 1 + left.height().max(right.height()),
            size: count + left.size() + right.size(),
            key,
            count,
            left,
            right,
        })))
    }
    fn balanced(key: (Int, Int), count: usize, mut left: Self, mut right: Self) -> Self {
        if left.height() > right.height() + 1 {
            let l = left.0.as_ref().expect("a taller left child exists");
            if l.right.height() > l.left.height() {
                let r = l.right.0.as_ref().expect("the taller inner child exists");
                left = Self::node(
                    r.key.clone(),
                    r.count,
                    Self::node(l.key.clone(), l.count, l.left.clone(), r.left.clone()),
                    r.right.clone(),
                );
            }
            let l = left.0.as_ref().expect("rotation preserves the left child");
            return Self::node(
                l.key.clone(),
                l.count,
                l.left.clone(),
                Self::node(key, count, l.right.clone(), right),
            );
        }
        if right.height() > left.height() + 1 {
            let r = right.0.as_ref().expect("a taller right child exists");
            if r.left.height() > r.right.height() {
                let l = r.left.0.as_ref().expect("the taller inner child exists");
                right = Self::node(
                    l.key.clone(),
                    l.count,
                    l.left.clone(),
                    Self::node(r.key.clone(), r.count, l.right.clone(), r.right.clone()),
                );
            }
            let r = right
                .0
                .as_ref()
                .expect("rotation preserves the right child");
            return Self::node(
                r.key.clone(),
                r.count,
                Self::node(key, count, left, r.left.clone()),
                r.right.clone(),
            );
        }
        Self::node(key, count, left, right)
    }
    // Complexity tradeoff: a sorted vector copied at every insertion costs O(k^2) over k
    // parts. Path-copying an AVL tree with subtree maxima costs O(log k) per update and
    // O(log k) per query, including deletion and persistent versions used by case splits.
    fn insert(&self, key: (Int, Int)) -> Self {
        let Some(n) = &self.0 else {
            return Self::node(key, 1, Self::default(), Self::default());
        };
        match key.cmp(&n.key) {
            std::cmp::Ordering::Less => {
                Self::balanced(n.key.clone(), n.count, n.left.insert(key), n.right.clone())
            }
            std::cmp::Ordering::Greater => {
                Self::balanced(n.key.clone(), n.count, n.left.clone(), n.right.insert(key))
            }
            std::cmp::Ordering::Equal => {
                Self::node(n.key.clone(), n.count + 1, n.left.clone(), n.right.clone())
            }
        }
    }
    fn remove(&self, key: &(Int, Int), all: bool) -> Self {
        let Some(n) = &self.0 else {
            return self.clone();
        };
        match key.cmp(&n.key) {
            std::cmp::Ordering::Less => Self::balanced(
                n.key.clone(),
                n.count,
                n.left.remove(key, all),
                n.right.clone(),
            ),
            std::cmp::Ordering::Greater => Self::balanced(
                n.key.clone(),
                n.count,
                n.left.clone(),
                n.right.remove(key, all),
            ),
            std::cmp::Ordering::Equal if n.count > 1 && !all => {
                Self::node(n.key.clone(), n.count - 1, n.left.clone(), n.right.clone())
            }
            std::cmp::Ordering::Equal => {
                if n.left.0.is_none() {
                    return n.right.clone();
                }
                let Some(mut first) = n.right.0.as_ref() else {
                    return n.left.clone();
                };
                while let Some(l) = first.left.0.as_ref() {
                    first = l;
                }
                Self::balanced(
                    first.key.clone(),
                    first.count,
                    n.left.clone(),
                    n.right.remove(&first.key, true),
                )
            }
        }
    }
    /// `max { a : b < y }`.
    fn lower_x(&self, y: &Int) -> Option<Int> {
        let (mut at, mut best) = (&self.0, None::<Int>);
        while let Some(n) = at {
            if n.key.0 < *y {
                for a in [Some(&n.key.1), n.left.max_a()].into_iter().flatten() {
                    best = Some(best.map_or_else(|| a.clone(), |b| b.max(a.clone())));
                }
                at = &n.right.0;
            } else {
                at = &n.left.0;
            }
        }
        best
    }
    /// `min { b : a > x }`.
    fn upper_y(&self, x: &Int) -> Option<Int> {
        let mut at = &self.0;
        while let Some(n) = at {
            if n.left.max_a().is_some_and(|a| a > x) {
                at = &n.left.0;
            } else if n.key.1 > *x {
                return Some(n.key.0.clone());
            } else {
                at = &n.right.0;
            }
        }
        None
    }
    /// `min_i max(b_i, floor((c - p*a_i)/q))`, for positive `p,q`.
    fn upper_case(&self, p: &Int, q: &Int, c: &Int) -> Option<Int> {
        debug_assert!(p.is_positive() && q.is_positive());
        self.upper_dec(|a: &Int| Some((c - &(p * a)).div_floor(q)))
    }
    /// `min_i max(b_i, f(max_{j <= i} a_j))` over the rows in order of `b`, for `f` that does
    /// not increase, `None` standing for no bound: the least upper bound on y that the rows
    /// `x >= a_i || y <= b_i` and `y <= f(x)` allow.
    // Complexity tradeoff: evaluating the bound at every row costs O(k) per call for k rows;
    // the descent keeps the prefix maximum of `a` and calls `f` once per level, O(log k)
    // calls of `f`.
    fn upper_dec(&self, f: impl Fn(&Int) -> Option<Int>) -> Option<Int> {
        let le = |v: Option<Int>, b: &Int| v.is_some_and(|v| v <= *b);
        let (mut at, mut prefix, mut best) = (&self.0, None::<Int>, None::<Int>);
        while let Some(n) = at {
            let mut a = prefix
                .clone()
                .map_or_else(|| n.key.1.clone(), |a| a.max(n.key.1.clone()));
            if let Some(l) = n.left.max_a() {
                a = a.max(l.clone());
            }
            if le(f(&a), &n.key.0) {
                best = Some(n.key.0.clone());
                at = &n.left.0;
            } else {
                prefix = Some(a);
                at = &n.right.0;
            }
        }
        if let Some(v) = prefix.and_then(|a| f(&a)) {
            best = Some(best.map_or(v.clone(), |b| b.min(v)));
        }
        best
    }
}

/// A threshold part's lower name, upper name, lower threshold, and upper threshold.
fn stair_row(g: &Formula) -> Option<(Arc<str>, Arc<str>, Int, Int)> {
    let Formula::Or(gs) = g else {
        return None;
    };
    if gs.len() != 2 {
        return None;
    }
    let mut lo = None;
    let mut hi = None;
    for g in gs.iter() {
        let Formula::Con(c) = g else {
            return None;
        };
        if c.rel != Rel::Ge {
            return None;
        }
        let mut terms = c.lin.terms.iter();
        let (Some((Atom::Sym(n), k)), None) = (terms.next(), terms.next()) else {
            return None;
        };
        if k.is_positive() {
            lo = Some((n.clone(), -&c.lin.constant.div_floor(k)));
        } else if k.is_negative() {
            hi = Some((n.clone(), c.lin.constant.div_floor(&-k)));
        }
    }
    let ((x, a), (y, b)) = (lo?, hi?);
    (x != y).then_some((x, y, a, b))
}

impl Scope {
    /// Exact box marginals for threshold rows and positive upper half-planes on their two
    /// names. Other disjunctions are still projected normally. Refuses classes, holes,
    /// equalities, a third name, and other half-plane directions; the ordinary rule then runs.
    // Complexity tradeoff: projecting k threshold rows separately costs O(k) per case.
    // The aggregate query costs O((r + 1) log k) for r base rows. The caller shares the
    // threshold rows' snapshot and walks only ordinary users after a name change. Ordinary
    // users, leaving the handled shape, and the existing raw projection still cost their
    // entries; this is not a global bound on the reduced product (R1-CODEX-01).
    fn cover_staircase(&mut self, b: &mut Block) -> Option<(Arc<str>, Arc<str>)> {
        let ((x, y), tree) = b.stair_pair()?;
        let (x, y, tree) = (&x.clone(), &y.clone(), &tree.clone());
        let px = self.get(x);
        let py = self.get(y);
        if classed(&px) || classed(&py) || px.ints().len() > 1 || py.ints().len() > 1 {
            return None;
        }
        let (mut xl, mut xh) = px.ints().bounds().map(|(l, h)| (l.clone(), h.clone()))?;
        let (mut yl, mut yh) = py.ints().bounds().map(|(l, h)| (l.clone(), h.clone()))?;
        let mut planes = Vec::new();
        for g in &b.cons {
            let (p, q, v) = stair_con(g, x, y)?;
            let v = &v;
            match (p.is_zero(), q.is_zero()) {
                (true, true) => {
                    if v.is_negative() {
                        self.empty_at(x);
                        return Some((x.clone(), y.clone()));
                    }
                }
                (false, true) => {
                    if p.is_positive() {
                        xh = xh.min(End::Fin(Num::from(&v.div_floor(&p))));
                    } else {
                        xl = xl.max(End::Fin(Num::from(&-&v.div_floor(&-&p))));
                    }
                }
                (true, false) => {
                    if q.is_positive() {
                        yh = yh.min(End::Fin(Num::from(&v.div_floor(&q))));
                    } else {
                        yl = yl.max(End::Fin(Num::from(&-&v.div_floor(&-&q))));
                    }
                }
                (false, false) => planes.push((p, q, v.clone())),
            }
        }
        if let End::Fin(l) = &yl {
            let l = Int::from(l);
            if let Some(a) = tree.lower_x(&l) {
                xl = xl.max(End::Fin(Num::from(&a)));
            }
            for (p, q, c) in &planes {
                let h = (c - &(q * &l)).div_floor(p);
                xh = xh.min(End::Fin(Num::from(&h)));
            }
        }
        if let End::Fin(h) = &xh
            && let Some(v) = tree.upper_y(&Int::from(h))
        {
            yh = yh.min(End::Fin(Num::from(&v)));
        }
        for (p, q, c) in &planes {
            if let Some(v) = tree.upper_case(p, q, c) {
                yh = yh.min(End::Fin(Num::from(&v)));
            }
            if let End::Fin(l) = &xl {
                let h = (c - &(p * &Int::from(l))).div_floor(q);
                yh = yh.min(End::Fin(Num::from(&h)));
            }
        }
        // The upper disjunctions bound y and x through `UpperBounds`, which depends only on
        // the staircase, the lower ends of x and y, and the disjunctions.
        // Complexity tradeoff: reading each of the u upper disjunctions at each call costs
        // O(u (a log k)) per call for disjunctions of a arms, O(k u) over k tests that each
        // move only an upper end; the block keeps the bounds and takes in each disjunction
        // as it enters, O(a log k), and reads them all again, O(u (a log k)), only when the
        // staircase or a lower end changes or a disjunction leaves.
        let fresh = b.upper_bounds.as_ref().is_some_and(|u| {
            &u.pair.0 == x && &u.pair.1 == y && u.tree.same(tree) && u.xl == xl && u.yl == yl
        });
        if !fresh {
            let mut u = UpperBounds {
                pair: (x.clone(), y.clone()),
                tree: tree.clone(),
                xl: xl.clone(),
                yl: yl.clone(),
                y: None,
                x: None,
            };
            for at in b.of_role(Role::Upper) {
                u.take(&at.1);
            }
            b.upper_bounds = Some(u);
        }
        if let Some(u) = &b.upper_bounds {
            if let Some(v) = &u.y {
                yh = yh.min(End::Fin(Num::from(v)));
            }
            if let Some(v) = &u.x {
                xh = xh.min(End::Fin(Num::from(v)));
            }
        }
        let changes = px.ints() != &IntervalSet::range(xl.clone(), xh.clone())
            || py.ints() != &IntervalSet::range(yl.clone(), yh.clone());
        // A changing threshold aggregate must also solve the other lower cohort
        // in this prospective box. Otherwise preserve all individual movements.
        if changes && !b.rays.is_empty() {
            let mut probe = self.names.view().clone();
            for (n, l, h) in [(x, &xl, &xh), (y, &yl, &yh)] {
                if let Some(p) = probe.get_mut(n) {
                    let prem = p.premises();
                    p.meet_ints(IntervalSet::range(l.clone(), h.clone()), &prem);
                }
            }
            b.ray_high(&probe)?;
        }
        for (n, l, h) in [(x, xl, xh), (y, yl, yh)] {
            if l > h {
                self.empty_at(n);
            } else {
                self.meet_own(n, IntervalSet::range(l, h));
            }
        }
        Some((x.clone(), y.clone()))
    }
}

impl Block {
    /// Whether the exact threshold calculation handles every base row and both name domains.
    fn manages_stairs(&self, names: &imbl::OrdMap<Arc<str>, Product>) -> bool {
        let Some(((x, y), _)) = self.stair_pair() else {
            return false;
        };
        for n in [x, y] {
            let Some(p) = names.get(n) else {
                return false;
            };
            if classed(p) || p.ints().len() != 1 {
                return false;
            }
        }
        self.cons.iter().all(|g| stair_con(g, x, y).is_some())
    }

    /// The names and staircase of the threshold aggregate when it may hold: every part but
    /// the constraints' is a threshold row or an upper disjunction on two names, and the
    /// threshold rows are on one pair of them.
    fn stair_pair(&self) -> Option<(&NamePair, &Staircase)> {
        if !self.aggregable() || self.stairs.len() != 1 {
            return None;
        }
        self.stairs.iter().next()
    }
}

/// The constraint `g` of a threshold block on the names `x` and `y` as `(p, q, c)` for
/// `p*x + q*y <= c`, when [`Scope::cover_staircase`] reads it: an inequality on no names but
/// these, with `p` and `q` both positive when it has both. Its coefficients are never zero
/// ([`Lin`]).
fn stair_con(g: &Formula, x: &Arc<str>, y: &Arc<str>) -> Option<(Int, Int, Int)> {
    let Formula::Con(c) = g else {
        return None;
    };
    if c.rel != Rel::Ge {
        return None;
    }
    let (mut p, mut q) = (Int::ZERO, Int::ZERO);
    for (a, k) in &c.lin.terms {
        match a {
            Atom::Sym(n) if n == x => p = -k,
            Atom::Sym(n) if n == y => q = -k,
            _ => return None,
        }
    }
    let both = !p.is_zero() && !q.is_zero();
    (!both || (p.is_positive() && q.is_positive())).then(|| (p, q, c.lin.constant.clone()))
}

/// An integer support shared by ordinary parts on one ordered pair. An arm
/// `x - j*y >= d`, j >= 0, supports every y <= H at x = d + j*y.
/// The multiset holds each distinct `(j, d)` with its count.
/// Complexity tradeoff: projecting k parts per case costs O(k) projections; this
/// persistent multiset costs O(log k) per insertion or deletion, and a case reads
/// its R distinct `(j, d)` pairs, O(R) arithmetic with no projection
/// ([`Block::ray_high`]). No witness coordinates or copies of the block's rows are stored.
#[derive(Clone, Default)]
struct RayGroup {
    rays: imbl::OrdMap<(Int, Int), usize>,
}

impl RayGroup {
    fn add(&mut self, j: &Int, d: &Int) {
        *self.rays.entry((j.clone(), d.clone())).or_insert(0) += 1;
    }

    fn remove(&mut self, j: &Int, d: &Int) {
        let key = (j.clone(), d.clone());
        if let Some(count) = self.rays.get_mut(&key) {
            *count -= 1;
            if *count == 0 {
                self.rays.remove(&key);
            }
        }
    }
}

/// Half-plane arms on two names, all with unit positive x coefficient and
/// the same constant. At y <= 0 the least y coefficient dominates all others.
fn ray_row(g: &Formula) -> Option<(Arc<str>, Arc<str>, Int, Int)> {
    let Formula::Or(arms) = g else {
        return None;
    };
    let ns = syms(g);
    let [x, y] = &ns[..] else {
        return None;
    };
    let mut slope: Option<Int> = None;
    let mut limit: Option<Int> = None;
    for arm in arms.iter() {
        let Formula::Con(c) = arm else {
            return None;
        };
        if c.rel != Rel::Ge {
            return None;
        }
        let (mut a, mut b) = (Int::ZERO, Int::ZERO);
        for (atom, k) in &c.lin.terms {
            match atom {
                Atom::Sym(n) if n == x => a = k.clone(),
                Atom::Sym(n) if n == y => b = k.clone(),
                _ => return None,
            }
        }
        if a != Int::ONE || limit.as_ref().is_some_and(|d| d != &-&c.lin.constant) {
            return None;
        }
        limit = Some(-&c.lin.constant);
        slope = Some(match slope {
            Some(old) => old.min(b),
            None => b,
        });
    }
    let slope = slope?;
    if !slope.is_negative() {
        return None;
    }
    Some((x.clone(), y.clone(), -&slope, limit?))
}

impl Block {
    /// The parts of `role`, in order.
    fn of_role(&self, role: Role) -> impl Iterator<Item = &PartAt> {
        self.roles.get(&role).into_iter().flatten()
    }

    /// Whether an aggregate may hold: the block has two names, and every part but the
    /// constraints' is read by one ([`Role`]).
    fn aggregable(&self) -> bool {
        !self.roles.contains_key(&Role::Other) && self.users.len() == 2
    }

    /// Whether an aggregate that holds stands for `p`, which is then not projected by itself.
    fn managed(&self, p: &Part) -> bool {
        (self.stair_managed && p.role.stair()) || (self.ray_managed && p.role == Role::Ray)
    }

    /// The parts an aggregate stood for while it held (`stair`, `ray`) and that none stands for
    /// now: each is projected by itself again, the upper disjunctions as the threshold rows.
    fn released(&self, stair: bool, ray: bool) -> impl Iterator<Item = &PartAt> {
        let (stair, ray) = (stair && !self.stair_managed, ray && !self.ray_managed);
        (self.roles.iter())
            .filter(move |(r, _)| (stair && r.stair()) || (ray && **r == Role::Ray))
            .flat_map(|(_, ats)| ats)
    }

    /// The parts that mention `n` and that no aggregate that holds stands for, in order.
    fn due_users(&self, n: &str) -> impl Iterator<Item = &PartAt> {
        (self.users.get(n).into_iter()).flat_map(|u| u.due(self.stair_managed, self.ray_managed))
    }

    /// Common-ray bound while y <= 0: each member is equivalent to x >= d+j*y,
    /// and a row p*x+q*y <= c with p >= 0 then gives y <= (c-p*d)/(p*j+q)
    /// at integer floors; the least such bound over the distinct (j, d) holds.
    /// Complexity tradeoff: reading the r rows against the R distinct (j, d) at each run
    /// costs O(r R) per run, O(k^2) over k tests that each add a ray; the block keeps the
    /// least bound ([`RayLeast`]) and takes in each ray as it enters, O(r), and each row,
    /// O(R), so a run costs O(r) for the rows and the lower end of x. A ray or row that
    /// leaves makes the next run read them all again, O(r R). Construction and removals
    /// cost O(log k) per member.
    fn ray_high(&self, names: &imbl::OrdMap<Arc<str>, Product>) -> Option<(Arc<str>, Int)> {
        if !self.aggregable() || self.rays.len() != 1 {
            return None;
        }
        let ((x, y), group) = self.rays.iter().next()?;
        if self
            .stairs
            .keys()
            .any(|pair| pair != &(x.clone(), y.clone()))
        {
            return None;
        }
        if group.rays.is_empty() {
            return None;
        }
        let (px, py) = (names.get(x)?, names.get(y)?);
        if classed(px) || classed(py) || px.ints().len() != 1 || py.ints().len() != 1 {
            return None;
        }
        let (xl, End::PosInf) = px.ints().bounds()? else {
            return None;
        };
        let (End::NegInf, End::Fin(h)) = py.ints().bounds()? else {
            return None;
        };
        let mut h = Int::from(h);
        if h.is_positive() {
            return None;
        }
        let least = self
            .ray_least
            .get_or_init(|| RayLeast::of(&self.cons, x, y, group));
        let RayLeast::Least(least) = least else {
            return None;
        };
        if let Some(v) = least {
            h = h.min(v.clone());
        }
        if let End::Fin(l) = xl {
            let l = Int::from(l);
            for g in &self.cons {
                let (p, q, c) = ray_con(g, x, y)?;
                h = h.min((&c - &(&p * &l)).div_floor(&q));
            }
        }
        Some((y.clone(), h))
    }
}

/// A row `p*x + q*y <= c` of [`Block::ray_high`] as `(p, q, c)`, when `g` is one with `p >= 0`
/// and `q > 0` on the names `x` and `y` alone.
fn ray_con(g: &Formula, x: &Arc<str>, y: &Arc<str>) -> Option<(Int, Int, Int)> {
    let Formula::Con(c) = g else {
        return None;
    };
    if c.rel != Rel::Ge {
        return None;
    }
    let (mut p, mut q) = (Int::ZERO, Int::ZERO);
    for (a, k) in &c.lin.terms {
        match a {
            Atom::Sym(n) if n == x => p = -k,
            Atom::Sym(n) if n == y => q = -k,
            _ => return None,
        }
    }
    (!p.is_negative() && q.is_positive()).then(|| (p, q, c.lin.constant.clone()))
}

/// The bound a row `p*x + q*y <= c` gives over a ray `(j, d)` in [`Block::ray_high`].
fn ray_bound((p, q, c): &(Int, Int, Int), j: &Int, d: &Int) -> Int {
    (c - &(p * d)).div_floor(&(&(p * j) + q))
}

/// The least of `x` and `y`, either of which may be missing.
fn least_of(x: Option<Int>, y: Option<Int>) -> Option<Int> {
    match (x, y) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (x, None) => x,
        (None, y) => y,
    }
}

/// The least bound the rows of a block give over the rays of its one ray group
/// ([`Block::ray_high`]).
#[derive(Clone)]
enum RayLeast {
    /// A row is not `p*x + q*y <= c` with `p >= 0` and `q > 0` on the group's two names.
    Unsupported,
    /// The least [`ray_bound`] over the rows and rays, none when there is no row.
    Least(Option<Int>),
}

impl RayLeast {
    /// Reads the rows `cons` against every ray of `group` on `x` and `y`, O(r R).
    fn of(cons: &imbl::OrdSet<Arc<Formula>>, x: &Arc<str>, y: &Arc<str>, group: &RayGroup) -> Self {
        let mut least = None;
        for g in cons {
            let Some(row) = ray_con(g, x, y) else {
                return RayLeast::Unsupported;
            };
            for (j, d) in group.rays.keys() {
                least = least_of(least, Some(ray_bound(&row, j, d)));
            }
        }
        RayLeast::Least(least)
    }

    /// Takes in the row `g` against every ray of `group` on `x` and `y`, O(R).
    fn take_con(&mut self, g: &Formula, x: &Arc<str>, y: &Arc<str>, group: &RayGroup) {
        let RayLeast::Least(least) = self else {
            return;
        };
        let Some(row) = ray_con(g, x, y) else {
            *self = RayLeast::Unsupported;
            return;
        };
        for (j, d) in group.rays.keys() {
            *least = least_of(least.take(), Some(ray_bound(&row, j, d)));
        }
    }

    /// Takes in the ray `(j, d)` on `x` and `y` against every row of `cons`, O(r).
    fn take_ray(
        &mut self,
        cons: &imbl::OrdSet<Arc<Formula>>,
        x: &Arc<str>,
        y: &Arc<str>,
        j: &Int,
        d: &Int,
    ) {
        let RayLeast::Least(least) = self else {
            return;
        };
        for g in cons {
            // Every row was read when the bound was first found; a row of another form
            // made it `Unsupported` then.
            if let Some(row) = ray_con(g, x, y) {
                *least = least_of(least.take(), Some(ray_bound(&row, j, d)));
            }
        }
    }
}

/// What the upper disjunctions of a block give in [`Scope::cover_staircase`] for the
/// staircase `tree` of the names `pair` and the lower ends `xl` of x and `yl` of y: the least
/// upper end of y and of x over the disjunctions, none where no disjunction bounds it.
#[derive(Clone)]
struct UpperBounds {
    pair: NamePair,
    tree: Staircase,
    xl: End,
    yl: End,
    y: Option<Int>,
    x: Option<Int>,
}

impl UpperBounds {
    /// Takes in the upper disjunction `g`, O(a log k) for a arms and k threshold rows.
    ///
    /// An upper disjunction `p1*x + q1*y <= c1 || p2*x + q2*y <= c2 || ...` on x and y, every
    /// p and q positive ([`upper_disjunction`]), bounds y at each x by the largest of its
    /// arms' lines, a function of x that does not increase. The staircase descent gives the
    /// least y the threshold rows and that function allow; the lower ends of x and y bound the
    /// other name through the same lines. A disjunction on other names gives nothing.
    fn take(&mut self, g: &Formula) {
        let Some(arms) = upper_arms(g, &self.pair.0, &self.pair.1) else {
            return;
        };
        let y_at = |a: &Int| {
            arms.iter()
                .map(|(p, q, c)| (c - &(p * a)).div_floor(q))
                .max()
        };
        let mut y = self.tree.upper_dec(y_at);
        if let End::Fin(l) = &self.xl {
            y = least_of(y, y_at(&Int::from(l)));
        }
        self.y = least_of(self.y.take(), y);
        if let End::Fin(l) = &self.yl {
            let l = Int::from(l);
            let x = arms
                .iter()
                .map(|(p, q, c)| (c - &(q * &l)).div_floor(p))
                .max();
            self.x = least_of(self.x.take(), x);
        }
    }
}

impl Scope {
    /// Applies the aggregates of `b` to the names as they are, the staircase
    /// ([`Scope::cover_staircase`]) when `stair` and then the common ray ([`Scope::cover_rays`]),
    /// and records in `b` which of them hold; the staircase's names when it holds.
    // Complexity tradeoff: `Scope::project_block` calls this after each projection, so up to
    // four times per block and once per part due. Calling it only when the names changed
    // since the last call that changed nothing gives the same answers (each call reads only
    // the names and the block), but the two aggregates are each O(r) for the block's r rows,
    // and a profile (perf, k = 64 of stair_cover, coordmix and hub_eqs) puts them together
    // under 0.3% of the run, all that skipping calls could save; so every call is made.
    // COMPLEXITY.md row LAZY-hub-cleanups.
    fn cover(&mut self, b: &mut Block, stair: bool) -> Option<(Arc<str>, Arc<str>)> {
        let covered = if stair { self.cover_staircase(b) } else { None };
        b.stair_managed = covered.is_some();
        b.ray_managed = self.cover_rays(b);
        covered
    }

    fn cover_rays(&mut self, b: &Block) -> bool {
        let Some((y, h)) = b.ray_high(&self.names) else {
            return false;
        };
        if let Some(p) = self.names.get_mut(&y) {
            let prem = p.premises();
            p.meet_ints(
                IntervalSet::range(End::NegInf, End::Fin(Num::from(&h))),
                &prem,
            );
        }
        true
    }
}

/// Closed upper half-plane disjunctions stay within the monotone two-name
/// fragment. Other ordinary operators retain the original queue: collapsing
/// threshold movements beside arbitrary operators can suppress its whole-block
/// exit.
/// Complexity tradeoff: classify each new description once, O(description size),
/// rather than scan k descriptions in each of k cases, O(k^2). The persistent
/// set records unsupported parts and answers the guard in O(1).
fn upper_disjunction(g: &Formula) -> bool {
    let Formula::Or(arms) = g else {
        return false;
    };
    arms.iter().all(|a| {
        matches!(a, Formula::Con(c) if c.rel==Rel::Ge && c.lin.terms.len()==2
            && c.lin.terms.iter().all(|(a,k)| matches!(a,Atom::Sym(_)) && k.is_negative()))
    })
}

/// The arms of the upper disjunction `g` as `(p, q, c)` for `p*x + q*y <= c`, when every arm
/// is on the names `x` and `y` alone. [`upper_disjunction`] makes `p` and `q` positive.
fn upper_arms(g: &Formula, x: &Arc<str>, y: &Arc<str>) -> Option<Vec<(Int, Int, Int)>> {
    let Formula::Or(arms) = g else {
        return None;
    };
    arms.iter()
        .map(|arm| {
            let Formula::Con(c) = arm else {
                return None;
            };
            let (mut p, mut q) = (Int::ZERO, Int::ZERO);
            for (a, k) in &c.lin.terms {
                match a {
                    Atom::Sym(n) if n == x => p = -k,
                    Atom::Sym(n) if n == y => q = -k,
                    _ => return None,
                }
            }
            (p.is_positive() && q.is_positive()).then(|| (p, q, c.lin.constant.clone()))
        })
        .collect()
}

/// An atom `sum of k * name + c >= 0`.
type Row = (BTreeMap<Arc<str>, Num>, Num);

/// The atom `s * lin + t >= 0`, when `lin` reads only names.
fn row(lin: &Lin, s: i64, t: i64) -> Option<Row> {
    let s = Num::from(s);
    let mut terms = BTreeMap::new();
    for (a, k) in &lin.terms {
        let Atom::Sym(m) = a else { return None };
        terms.insert(m.clone(), &s * &Num::from(k));
    }
    Some((terms, &(&s * &Num::from(&lin.constant)) + &Num::from(t)))
}

/// The atoms of `c` with the value `value`, as a union of conjunctions, when it reads only
/// names.
fn atoms_of(c: &Con, value: bool) -> Option<Vec<Vec<Row>>> {
    let r = |s, t| row(&c.lin, s, t);
    Some(match (c.rel, value) {
        (Rel::Ge, true) => vec![vec![r(1, 0)?]],
        (Rel::Ge, false) => vec![vec![r(-1, -1)?]],
        (Rel::Eq, true) => vec![vec![r(1, 0)?, r(-1, 0)?]],
        (Rel::Eq, false) => vec![vec![r(1, -1)?], vec![r(-1, -1)?]],
    })
}

/// `rows` with each name other than `keep` that they bound from both sides eliminated, or
/// `None` when such a name's interval has a hole or a class. The ends of its interval join
/// the rows as bounds of coefficient 1, and each pair of a lower and an upper bound gives its
/// dark shadow (Pugh 1991): when all hold, the pair of the greatest lower and least upper
/// bound has an integer between them, and it meets every other bound.
fn eliminate(
    mut rows: Vec<Row>,
    keep: Option<&Arc<str>>,
    get: &impl Fn(&str) -> Product,
) -> Option<Vec<Row>> {
    // Complexity tradeoff: unrestricted Fourier-Motzkin may grow doubly
    // exponentially (seen in review round 3 on pendants.rs's equalities to hubs). Add finite box ends once, normalize
    // parallel integer rows, and eliminate only when p*q <= p+q. Thus each step
    // replaces at least as many rows as it makes; at most the initial number of
    // names disappear and the row count never exceeds its initial value.
    // This is a structural refusal of the certificate, with no size cutoff.
    // Pugh, The Omega test, Supercomputing '91 (1991), supplies the dark shadow;
    // its sufficient integer-witness argument is unchanged by refusing a step.
    let ns = both(&rows);
    for n in ns.into_iter().filter(|n| Some(n) != keep) {
        let p = get(&n);
        let (lo, hi) = p.ints().only().filter(|_| !classed(&p))?;
        for (k, e) in [(1, lo), (-1, hi)] {
            if let End::Fin(e) = e {
                rows.push((
                    BTreeMap::from([(n.clone(), Num::from(k))]),
                    if k == 1 { -e } else { e.clone() },
                ));
            }
        }
    }
    rows = parallel_rows(rows);
    loop {
        let mut counts: BTreeMap<Arc<str>, (usize, usize)> = BTreeMap::new();
        for (ts, _) in &rows {
            for (n, k) in ts {
                let c = counts.entry(n.clone()).or_default();
                if k.signum() > 0 {
                    c.0 += 1;
                } else {
                    c.1 += 1;
                }
            }
        }
        let mut unary: BTreeMap<Arc<str>, (Option<Num>, Option<Num>)> = BTreeMap::new();
        for (ts, c) in &rows {
            if ts.len() == 1 {
                let (n, k) = ts.iter().next()?;
                let u = unary.entry(n.clone()).or_default();
                if *k == Num::ONE {
                    u.0 = Some(c.clone());
                }
                if *k == -&Num::ONE {
                    u.1 = Some(c.clone());
                }
            }
        }
        let mut needed = false;
        let m = counts.into_iter().find_map(|(n, (p, q))| {
            if Some(&n) == keep || p == 0 || q == 0 {
                return None;
            }
            needed = true;
            // A consistent pair of unit unary bounds makes the true constant
            // upper-lower>=0, discarded by parallel_rows. Count that output as
            // absent before deciding whether this step can grow.
            let trivial = unary.get(&n).is_some_and(|(l, h)| {
                matches!((l,h),
                (Some(l),Some(h)) if l+h >= Num::ZERO)
            });
            (p.checked_mul(q)
                .is_some_and(|pairs| pairs - usize::from(trivial) <= p + q))
            .then_some(n)
        });
        let Some(m) = m else {
            return (!needed).then_some(rows);
        };
        let (mut lower, mut upper) = (vec![], vec![]);
        for r in std::mem::take(&mut rows) {
            match r.0.get(&m).map(|k| k.signum()) {
                Some(1) => lower.push(r),
                Some(-1) => upper.push(r),
                _ => rows.push(r),
            }
        }
        let rest = |t: &BTreeMap<Arc<str>, Num>, f: &Num| -> Vec<(Arc<str>, Num)> {
            t.iter()
                .filter(|(x, _)| **x != m)
                .map(|(x, k)| (x.clone(), f * k))
                .collect()
        };
        for (lt, lc) in &lower {
            let a = &lt[&m];
            for (ut, uc) in &upper {
                let b = &-&ut[&m];
                let mut terms: BTreeMap<Arc<str>, Num> = BTreeMap::new();
                for (x, k) in [rest(lt, b), rest(ut, a)].concat() {
                    let v = &terms.remove(&x).unwrap_or(Num::ZERO) + &k;
                    if !v.is_zero() {
                        terms.insert(x, v);
                    }
                }
                let slack = &(a - &Num::ONE) * &(b - &Num::ONE);
                rows.push((terms, &(&(a * uc) + &(b * lc)) - &slack));
            }
        }
        rows = parallel_rows(rows);
    }
}

// Complexity tradeoff: group equal primitive term maps in O(T log r), retaining
// their tightest constant. For integer variables gcd division with floor preserves
// each row exactly. This is parallel-row normalization from Pugh's Omega test
// (Supercomputing '91, 1991); no pairwise redundancy search is needed.
fn parallel_rows(rows: Vec<Row>) -> Vec<Row> {
    let mut out: BTreeMap<BTreeMap<Arc<str>, Num>, Num> = BTreeMap::new();
    for (mut terms, mut c) in rows {
        let d = terms.values().fold(Num::ZERO, |d, k| d.gcd(k));
        if d > Num::ONE {
            for k in terms.values_mut() {
                *k = k.div_floor(&d);
            }
            c = c.div_floor(&d);
        }
        if terms.is_empty() && c >= Num::ZERO {
            continue;
        }
        out.entry(terms)
            .and_modify(|old| *old = old.clone().min(c.clone()))
            .or_insert(c);
    }
    out.into_iter().collect()
}

/// The names that `rows` bound from both sides.
fn both(rows: &[Row]) -> BTreeSet<Arc<str>> {
    let mut sign: BTreeMap<&Arc<str>, bool> = BTreeMap::new();
    let mut out = BTreeSet::new();
    for (m, k) in rows.iter().flat_map(|r| r.0.iter()) {
        if *sign.entry(m).or_insert(k.signum() > 0) != (k.signum() > 0) {
            out.insert(m.clone());
        }
    }
    out
}

/// The value of `k * end` for the end of `p` that most raises it, `None` when infinite;
/// `None` outside when `p` is empty or has a class.
fn top(k: &Num, p: &Product) -> Option<Option<Num>> {
    let (lo, hi) = p.ints().bounds().filter(|_| !classed(p))?;
    Some(match if k.signum() > 0 { hi } else { lo } {
        End::Fin(v) => Some(k * v),
        _ => None,
    })
}

/// For each row, its greatest value over the box given by `get` and how many of its names
/// are unbounded on the side that raises it; `None` when a name's interval is empty.
fn sums(rows: &[Row], get: &impl Fn(&str) -> Product) -> Option<Vec<(Num, usize)>> {
    rows.iter()
        .map(|(terms, c)| {
            terms
                .iter()
                .try_fold((c.clone(), 0), |(s, free), (x, k)| match top(k, &get(x))? {
                    Some(v) => Some((&s + &v, free)),
                    None => Some((s, free + 1)),
                })
        })
        .collect()
}

/// The values of `n` at which every row holds at one integer point of the box of the other
/// names, given each row's greatest value over the box ([`sums`]), when every other name has
/// one sign in all rows: then the box's corner that most raises one row most raises them all,
/// and each row bounds `n` from one side at that corner.
fn range(rows: &[Row], sums: &[(Num, usize)], n: &Arc<str>, p: &Product) -> Option<(End, End)> {
    let (mut up, mut down) = (End::NegInf, End::PosInf);
    for ((terms, _), (s, free)) in rows.iter().zip(sums) {
        let Some(c) = terms.get(n) else {
            if *free == 0 && s.signum() < 0 {
                return None;
            }
            continue;
        };
        let (m, free) = match top(c, p)? {
            Some(v) => (s - &v, *free),
            None => (s.clone(), free - 1),
        };
        match c.signum() {
            _ if free > 0 => {}
            1 => up = up.max(End::Fin(-&m.div_floor(c))),
            _ => down = down.min(End::Fin(m.div_floor(&-c))),
        }
    }
    (up <= down).then_some((up, down))
}

/// Appends to `out` conjunctions of rows, with `atoms`, whose union holds every point at
/// which `f` has the value `value` and `atoms` hold: `f` is read as a union of conjunctions
/// of atoms, a conjunction kept only where at most one of its members is no atom and does
/// not have the value asked at every point of the box given by `get`; any other is dropped.
fn conjunctions(
    f: &Formula,
    value: bool,
    atoms: &mut Vec<Row>,
    get: &impl Fn(&str) -> Product,
    out: &mut Vec<Vec<Row>>,
) {
    match f {
        Formula::Con(c) => {
            for conj in atoms_of(c, value).into_iter().flatten() {
                out.push([atoms.clone(), conj].concat());
            }
        }
        Formula::Not(g) => conjunctions(g, !value, atoms, get, out),
        Formula::And(gs) | Formula::Or(gs) if matches!(f, Formula::And(_)) == value => {
            let k = atoms.len();
            let mut rest = vec![];
            for g in gs.iter().filter(|g| !fixed(g, value, get)) {
                match g {
                    Formula::Con(c) => match atoms_of(c, value).as_deref() {
                        Some([conj]) => atoms.extend(conj.iter().cloned()),
                        _ => rest.push(g),
                    },
                    _ => rest.push(g),
                }
            }
            match rest[..] {
                [] => out.push(atoms.clone()),
                [g] => conjunctions(g, value, atoms, get, out),
                _ => {}
            }
            atoms.truncate(k);
        }
        Formula::And(gs) | Formula::Or(gs) => {
            for g in gs.iter() {
                conjunctions(g, value, atoms, get, out);
            }
        }
    }
}

/// Whether the union of `spans` holds every integer from `lo` to `hi`.
fn covers(mut spans: Vec<(End, End)>, lo: &End, hi: &End) -> bool {
    spans.sort();
    let mut need = lo.clone();
    for (a, b) in spans {
        if a <= need && b >= need {
            let End::Fin(b) = b else { return true };
            need = End::Fin(&b + &Num::ONE);
        }
    }
    &need > hi
}

/// The least (`up` false) or greatest value of `lin` over the hulls of its names' intervals
/// given by `get`, when every end it reads is finite.
fn lin_end(lin: &Lin, up: bool, get: &impl Fn(&str) -> Product) -> Option<Num> {
    let mut sum = Num::from(&lin.constant);
    for (a, k) in &lin.terms {
        let Atom::Sym(n) = a else { return None };
        let p = get(n);
        let (lo, hi) = p.ints().bounds()?;
        let End::Fin(v) = (if k.is_positive() == up { hi } else { lo }) else {
            return None;
        };
        sum = &sum + &(&Num::from(k) * v);
    }
    Some(sum)
}

/// Whether `f` has the value `value` at every point of the hulls of its names' intervals
/// given by `get`.
fn fixed(f: &Formula, value: bool, get: &impl Fn(&str) -> Product) -> bool {
    match f {
        Formula::Con(c) => {
            let (lo, hi) = (
                || lin_end(&c.lin, false, get),
                || lin_end(&c.lin, true, get),
            );
            let zero = &Num::ZERO;
            match (c.rel, value) {
                (Rel::Ge, true) => lo().is_some_and(|v| &v >= zero),
                (Rel::Ge, false) => hi().is_some_and(|v| &v < zero),
                (Rel::Eq, true) => {
                    lo().is_some_and(|v| &v >= zero) && hi().is_some_and(|v| &v <= zero)
                }
                (Rel::Eq, false) => {
                    lo().is_some_and(|v| &v > zero) || hi().is_some_and(|v| &v < zero)
                }
            }
        }
        Formula::Not(g) => fixed(g, !value, get),
        Formula::And(gs) if value => gs.iter().all(|g| fixed(g, value, get)),
        Formula::Or(gs) if !value => gs.iter().all(|g| fixed(g, value, get)),
        Formula::And(gs) | Formula::Or(gs) => gs.iter().any(|g| fixed(g, value, get)),
    }
}

impl Scope {
    /// Whether projecting `part` of `b` leaves each name of its formula as it is: no name has
    /// a class, and for every value of each name some integer point of the box of the others
    /// satisfies the part's formula ([`conjunctions`], [`range`]). Each conjunction's rows
    /// are eliminated and summed once for all names it bounds from one side.
    fn idle(&self, b: &Block, part: &Part) -> bool {
        // Complexity tradeoff: consult cached structural indexes before reading
        // the base. A constraint-only part is considered only for a free leaf,
        // and a base with names outside this part and leaf is left to the existing
        // pendant projector. A base with equalities uses that route too.
        // Thus peq/pleaves never scan a growing collection of sibling leaves in
        // this certificate. These are fragment refusals, not count thresholds;
        // subset testing costs O(|part| log |part|) and never scans extra names.
        // An empty base is tested like any other (the part's own rows alone):
        // refusing it, as the review round's version did, projected star_extra's
        // split parts again at each new split, 1,773,848 against 2,405,039
        // allocations at k = 32 (8n ratio 14.0 against 17.9 allocations).
        if !b.split.eqs.is_empty() {
            return false;
        }
        let (g, free_two_base) = if let Some(g) = part.of.as_deref() {
            (g, false)
        } else if let Some(leaf) = &b.leaf {
            let p = self.get(leaf);
            if classed(&p) || !matches!(p.ints().only(), Some((_, End::PosInf))) {
                return false;
            }
            (&*part.key.0, false)
        } else if b.split.group.len() <= 2
            && b.split.group.keys().all(|f| matches!(f, Factor::Sym(_)))
        {
            // Complexity tradeoff: naive version, the base of a block with no leaf refused here,
            // so it was projected again at each wake, one `project_each` per wake. Used: when the
            // block's constraints hold at most two names, all plain, the base is tested like a
            // part, by the same elimination over its rows, O(r log r) for r rows; the test reads
            // every name of the base, so no name its projection could narrow is left out. Gemini
            // seat, round 3.
            (&*part.key.0, true)
        } else {
            return false;
        };
        if !free_two_base {
            let mut allowed = factors(g);
            if let Some(n) = &b.leaf {
                allowed.insert(Factor::Sym(n.clone()));
            }
            if b.split.group.len() > allowed.len()
                || !b.split.group.keys().all(|n| allowed.contains(n))
            {
                return false;
            }
        }
        let get = |m: &str| self.get(m);
        let (f, mut conjs) = (b.formula(part), vec![]);
        conjunctions(&f, true, &mut vec![], &get, &mut conjs);
        let names = syms(&f);
        let mut spans: BTreeMap<&Arc<str>, Vec<(End, End)>> = BTreeMap::new();
        for rows in conjs {
            let two = both(&rows);
            let shared =
                eliminate(rows.clone(), None, &get).and_then(|r| Some((sums(&r, &get)?, r)));
            for n in &names {
                let own = two
                    .contains(n)
                    .then(|| eliminate(rows.clone(), Some(n), &get));
                let own = own.map(|r| r.and_then(|r| Some((sums(&r, &get)?, r))));
                let Some((s, r)) = own.as_ref().unwrap_or(&shared) else {
                    continue;
                };
                spans.entry(n).or_default().extend(range(r, s, n, &get(n)));
            }
        }
        names.iter().all(|n| {
            let p = self.get(n);
            let Some((lo, hi)) = p.ints().bounds() else {
                return false;
            };
            !classed(&p) && covers(spans.remove(n).unwrap_or_default(), lo, hi)
        })
    }

    /// Whether the part `part` at `at` of `b` is idle, read from the least part of its chain
    /// key ([`Block::chains`]) when that one's ends lie at or below its own and it is idle,
    /// and otherwise from [`Scope::idle`]. `certified` holds the verdicts found since the
    /// names last moved, and takes the new ones.
    ///
    /// Proof. Let Q be the least part and P this one, with one key and ends q <= p in every
    /// place. A row atom `t + c_q >= 0` implies `t + c_p >= 0` for c_q <= c_p; an absolute
    /// value `F + b_q|y| + c_q >= 0` implies `F + b_p|y| + c_p >= 0` for b_q <= b_p and
    /// c_q <= c_p, as |y| >= 0. So each atom of Q implies the atom of P at its place, Q
    /// implies P, and Q and the base imply P and the base ([`Split::formula`]). The atoms
    /// hold the same names, so both formulas have the same names and refusals of the
    /// group's names. When `idle` holds for Q, every value of each name in the box has an
    /// integer point of Q and the base, which is a point of P and the base, and no name is
    /// classed; so P's exact projection covers the box, and a sound projection of P meets
    /// it to itself, as when `idle` holds for P. The names' products are those projecting P
    /// leaves. As with `idle` itself, a refusal that projecting P would have reported is not
    /// reported; that happens only where `idle` refuses P and holds for Q.
    fn idle_by_chain(
        &self,
        b: &Block,
        at: &PartAt,
        part: &Part,
        certified: &mut BTreeMap<PartAt, bool>,
        certified_chains: &mut BTreeMap<Arc<Vec<ChainAtom>>, Vec<Int>>,
    ) -> bool {
        // Complexity tradeoff: naive version, `idle_by_chain` compared only against the single
        // global minimum `b.chains[k].get_min()`; when that minimum failed Omega's dark shadow
        // (`split_on_y(1)` in `persist` Arm 2), every subsequent member `split_on_y(2..j-1)` ran
        // `self.idle` individually (`48.6M` instructions at k = 16, Gemini seat, round 3).
        // Used: record the least ends certified idle so far in `certified_chains`, subsuming all
        // higher members in O(e) comparisons (Gemini seat's prototype: `idle_calls` 269 -> 79 at k = 16).
        // Reference: W. Pugh, "The Omega test: a fast and practical integer programming algorithm
        // for dependence analysis", Communications of the ACM 35(8), 1992, pp. 102-114.
        if let Some((k, ends)) = &part.chain
            && let Some(q_ends) = certified_chains.get(k)
            && chain_below(q_ends, ends)
        {
            return true;
        }
        let mut verdict = |q: &PartAt, p: &Part| match certified.get(q) {
            Some(v) => *v,
            None => {
                let v = self.idle(b, p);
                certified.insert(q.clone(), v);
                if v && let Some((ck, c_ends)) = &p.chain {
                    certified_chains
                        .entry(ck.clone())
                        .and_modify(|cur| {
                            if chain_below(c_ends, cur) {
                                *cur = c_ends.clone();
                            }
                        })
                        .or_insert_with(|| c_ends.clone());
                }
                v
            }
        };
        if let Some((k, ends)) = &part.chain
            && let Some((least, q)) = b.chains.get(k).and_then(|set| set.get_min())
            && q != at
            && chain_below(least, ends)
            && let Some(qp) = b.parts.get(q)
            && verdict(q, qp)
        {
            return true;
        }
        verdict(at, part)
    }
}

// Complexity tradeoff: carry r common-intercept two-name inequalities into every
// projection, versus retain just the two extreme slopes per intercept in O(r log r).
// A middle row is a convex combination of its extremes, so removing it preserves all
// real and integer points. This is the common-intercept case of the envelope method
// named in plan row PERF-l139-family (F. P. Preparata and M. I. Shamos, Computational Geometry: An Introduction, Springer-Verlag, 1985),
// using ordered grouping rather than a dynamic general half-plane hull. Projection
// syntax may still affect refusals; this is tested by families::projection_shortcut_cases.
// Measured in review round 3 (allocator calls, 8n ratio), persist: without this rule R=26.29, with it R=12.66;
// compact_abs is also present in both measurements.
fn extreme_base(cons: &[&Arc<Formula>]) -> Formula {
    let eligible = |g: &&&Arc<Formula>| {
        matches!(&****g,Formula::Con(c)
        if c.rel == Rel::Ge && c.lin.terms.len() == 2
            && c.lin.terms.keys().all(|a| matches!(a,Atom::Sym(_))))
    };
    let mut candidates = cons.iter().filter(eligible);
    if candidates.next().is_none() || candidates.next().is_none() {
        return Formula::and(cons.iter().map(|g| (***g).clone()).collect());
    }
    let mut groups: BTreeMap<(&Atom, &Atom, &Int, &Int), (&Con, &Con)> = BTreeMap::new();
    let mut out = vec![];
    for g in cons {
        let Formula::Con(c) = &***g else {
            out.push((***g).clone());
            continue;
        };
        let mut terms = c.lin.terms.iter();
        match (c.rel, terms.next(), terms.next(), terms.next()) {
            (Rel::Ge, Some((x @ Atom::Sym(_), a)), Some((y @ Atom::Sym(_), b)), None) => {
                let key = (x, y, a, &c.lin.constant);
                let (lo, hi) = groups.entry(key).or_insert((c, c));
                if b < &lo.lin.terms[y] {
                    *lo = c;
                }
                if b > &hi.lin.terms[y] {
                    *hi = c;
                }
            }
            _ => out.push(Formula::Con(c.clone())),
        }
    }
    for (lo, hi) in groups.into_values() {
        if lo != hi {
            out.push(Formula::Con(hi.clone()));
        }
        out.push(Formula::Con(lo.clone()));
    }
    Formula::and(out)
}

/// The clauses of one form `F + |b y| + c >= 0` (key: `F`'s terms and `y`), by `|b|`, each
/// with its least constant `c` and its formula.
type AbsGroups = BTreeMap<(BTreeMap<Atom, Int>, Atom), BTreeMap<Int, (Int, Formula)>>;

// Complexity tradeoff: the again projection previously carried every repeated absolute
// linear lower bound into the integer solver. The two arms F+b*y>=0 or F-b*y>=0
// mean F+|b*y|>=0. At fixed nonconstant F and y, a smaller |b| and smaller constant
// imply a clause with larger ones. Sort and keep the Pareto frontier in O(T log r)
// for T input terms in r clauses, rather than O(r^2) pairwise implication checks.
// No arm combinations or values are searched. This algebraic redundancy test is used
// instead of plan row PERF-l139-family's general half-plane hull, which does not apply to disjunctions.
// Equivalence preserves integer points; families::projection_shortcut_cases compares the approximate
// projector's outputs, since equivalence alone does not establish equal refusals.
// Measured in review round 3 (allocator calls, 8n ratio) without/with: coordmix_floor 26.64/11.97, persist 15.94/12.66.
fn compact_abs(part: &Formula) -> Formula {
    let mut groups = AbsGroups::new();
    let mut out = vec![];
    for g in distinct_conjuncts(part) {
        let shaped = (|| {
            let Formula::Or(gs) = &g else { return None };
            let [Formula::Con(a), Formula::Con(b)] = &gs[..] else {
                return None;
            };
            if a.rel != Rel::Ge
                || b.rel != Rel::Ge
                || a.lin.constant != b.lin.constant
                || a.lin.terms.len() != b.lin.terms.len()
            {
                return None;
            }
            let mut rest = a.lin.terms.clone();
            let mut changed = None;
            for (y, k) in &a.lin.terms {
                let h = b.lin.terms.get(y)?;
                if k != h {
                    if changed.is_some() || *k != -h {
                        return None;
                    }
                    changed = Some((y.clone(), k.abs()));
                    rest.remove(y);
                }
            }
            let (y, k) = changed?;
            Some(((rest, y), k, a.lin.constant.clone()))
        })();
        match shaped {
            Some((key, k, c)) => {
                let rows = groups.entry(key).or_default();
                if rows.get(&k).is_none_or(|(old, _)| c < *old) {
                    rows.insert(k, (c, g));
                }
            }
            None => out.push(g),
        }
    }
    for rows in groups.into_values() {
        let mut least = None;
        for (c, g) in rows.into_values() {
            if least.as_ref().is_none_or(|old| c < *old) {
                least = Some(c);
                out.push(g);
            }
        }
    }
    Formula::and(out)
}

impl Scope {
    // Complexity tradeoff: the generic integer projector repeatedly asks about a
    // free unit-sum leaf even when its minimum is minus infinity. For a two-name
    // box and one half-plane, the recession cone has only axis rays and the two
    // orientations of the row's kernel. A feasible ray with negative unit-sum
    // objective proves an unbounded minimum. Project the hubs by the one-row
    // corner formula in O(r) arithmetic; refuse if none of these rays certifies
    // unboundedness. Measured in review round 3, star: R=7.19, against 7.60 without this
    // certificate; work at 8n falls from 666544 to 447009 allocations. This
    // elementary recession-cone certificate replaces general half-plane hull construction (Preparata and Shamos, Computational Geometry: An Introduction,
    // Springer-Verlag, 1985) on this fragment, without enumerating integer points.
    fn unbounded_unit(
        &self,
        p: &Pendant,
        rest: &[Formula],
    ) -> Option<Vec<(Arc<str>, IntervalSet)>> {
        if p.s != 1
            || p.sigma != -1
            || p.eq
            || !matches!(self.get(&p.x).ints().bounds()?.1, End::PosInf)
        {
            return None;
        }
        // The one-disjunction caller and name-only atoms ensure conjunctions
        // returns the whole union here, rather than a partial support cover.
        if rest.iter().any(|g| {
            g.cons()
                .iter()
                .any(|c| c.lin.terms.keys().any(|a| !matches!(a, Atom::Sym(_))))
        }) {
            return None;
        }
        let mut ns = vec![];
        let mut signs = vec![];
        let mut domains = BTreeMap::new();
        for (a, k) in &p.form.terms {
            let Atom::Sym(n) = a else { return None };
            if k.abs() != Int::ONE {
                return None;
            }
            let v = self.get(n);
            if classed(&v) || v.ints().only().is_none() {
                return None;
            }
            ns.push(n.clone());
            signs.push(Num::from(k));
            domains.insert(n.clone(), v.ints().clone());
        }
        let [x, y] = &ns[..] else { return None };
        if !ns.iter().zip(&signs).any(|(n, k)| {
            domains[n].bounds().is_some_and(|(l, h)| {
                (k.signum() > 0 && *l == End::NegInf) || (k.signum() < 0 && *h == End::PosInf)
            })
        }) {
            return None;
        }
        let mut conjs = vec![];
        conjunctions(
            &Formula::and(rest.to_vec()),
            true,
            &mut vec![],
            &|n| self.get(n),
            &mut conjs,
        );
        let mut out: BTreeMap<Arc<str>, IntervalSet> = ns
            .iter()
            .chain(std::iter::once(&p.x))
            .map(|n| (n.clone(), IntervalSet::empty()))
            .collect();
        for rows in conjs {
            let mut dom = domains.clone();
            let mut wide = None;
            let mut empty = false;
            for (ts, c) in rows {
                if ts.is_empty() {
                    empty |= c < Num::ZERO;
                    continue;
                }
                if ts.len() == 1 {
                    let (n, k) = ts.iter().next()?;
                    let bound = if k.signum() > 0 {
                        IntervalSet::range(End::Fin(-&c.div_floor(k)), End::PosInf)
                    } else {
                        IntervalSet::range(End::NegInf, End::Fin(c.div_floor(&-k)))
                    };
                    let d = dom.get_mut(n)?;
                    *d = d.meet(&bound);
                    empty |= d.is_empty();
                } else {
                    if wide.is_some() || ts.keys().any(|n| !dom.contains_key(n)) {
                        return None;
                    }
                    wide = Some((ts, c));
                }
            }
            if empty {
                continue;
            }
            let r = wide.unwrap_or_else(|| (BTreeMap::new(), Num::ZERO));
            let get = |n: &str| {
                let mut v = self.get(n);
                let prem = v.premises();
                v.meet_ints(dom[n].clone(), &prem);
                v
            };
            let ss = sums(std::slice::from_ref(&r), &get)?;
            if ss[0].1 == 0 && ss[0].0 < Num::ZERO {
                continue;
            }
            let k = [
                r.0.get(x).cloned().unwrap_or(Num::ZERO),
                r.0.get(y).cloned().unwrap_or(Num::ZERO),
            ];
            let allowed = |i: usize, d: &Num| -> bool {
                let Some((l, h)) = dom[&ns[i]].bounds() else {
                    return false;
                };
                d.is_zero()
                    || (d.signum() > 0 && *h == End::PosInf)
                    || (d.signum() < 0 && *l == End::NegInf)
            };
            let rays = [
                [Num::ONE, Num::ZERO],
                [-&Num::ONE, Num::ZERO],
                [Num::ZERO, Num::ONE],
                [Num::ZERO, -&Num::ONE],
                [k[1].clone(), -&k[0]],
                [-&k[1], k[0].clone()],
            ];
            if !rays.into_iter().any(|d| {
                allowed(0, &d[0])
                    && allowed(1, &d[1])
                    && &(&signs[0] * &d[0]) + &(&signs[1] * &d[1]) < Num::ZERO
                    && &(&k[0] * &d[0]) + &(&k[1] * &d[1]) >= Num::ZERO
            }) {
                return None;
            }
            for n in &ns {
                let (l, h) = range(std::slice::from_ref(&r), &ss, n, &get(n))?;
                let d = dom[n].meet(&IntervalSet::range(l, h));
                let old = out.get_mut(n)?;
                *old = old.join(&d);
            }
            out.insert(p.x.clone(), IntervalSet::top());
        }
        Some(out.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod bench;

    /// The groups `Split::update` keeps as constraints come and go, linking the factors of
    /// each constraint as a path ([`count_links`]), are those `Split::new` finds anew from the
    /// constraints left by a union of all their factors ([`linked`]): constraints of one to
    /// six names among eight, so that a removal often splits a group and a wide constraint
    /// holds names its path does not link directly. The order of the groups is not compared.
    #[test]
    fn the_groups_kept_by_path_links_are_the_groups_found_anew() {
        let names: Vec<Atom> = (0..8).map(|i| Atom::Sym(format!("n{i}").into())).collect();
        let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
        let mut next = |m: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % m
        };
        let partition = |s: &Split| -> BTreeSet<BTreeSet<Factor>> {
            s.groups.values().map(|(fs, _)| fs.clone()).collect()
        };
        let (mut splits, mut wide) = (0, 0);
        for _ in 0..200 {
            let mut cons: imbl::OrdSet<Arc<Formula>> = imbl::OrdSet::new();
            let mut split = Split::new(&[], None);
            for _ in 0..12 {
                let remove = !cons.is_empty() && next(3) == 0;
                let (removed, added) = if remove {
                    let i = next(cons.len() as u64) as usize;
                    let g = cons.iter().nth(i).cloned().expect("a constraint");
                    cons.remove(&g);
                    (vec![g], vec![])
                } else {
                    let v = 1 + next(6) as usize;
                    let mut lin = Lin::constant(next(5) as i64);
                    for _ in 0..v {
                        let x = Lin::atom(names[next(8) as usize].clone());
                        lin = lin.plus(&x.times(1 + next(3) as i64));
                    }
                    wide += usize::from(lin.terms.len() >= 3);
                    let g = Arc::new(Formula::Con(Con::ge(&lin, &Lin::constant(0))));
                    if cons.insert(g.clone()).is_some() {
                        continue;
                    }
                    (vec![], vec![g])
                };
                let before = partition(&split).len();
                split = split.update(&cons, &removed, &added);
                let fresh = Split::new(&cons.iter().collect::<Vec<_>>(), None);
                assert_eq!(partition(&split), partition(&fresh), "{cons:?}");
                splits += usize::from(remove && partition(&split).len() > before);
            }
        }
        assert!(
            splits >= 20 && wide >= 200,
            "{splits} splits, {wide} wide constraints"
        );
    }

    /// The due users of a name are the parts of every set but those of the aggregates that
    /// hold, each once, in the order of the parts: the order the worklist takes them in.
    #[test]
    fn due_users_are_the_parts_of_the_aggregates_that_do_not_hold_in_order() {
        let at = |k: i64| -> PartAt {
            let x = Lin::atom(Atom::Sym("x".into()));
            (
                false,
                Arc::new(Formula::Con(Con::ge(&x, &Lin::constant(k)))),
            )
        };
        let mut users = Users::default();
        for (k, role) in [
            (5, Role::Other),
            (1, Role::Stair),
            (3, Role::Ray),
            (0, Role::Constraints),
            (4, Role::Upper),
            (2, Role::Ray),
            (6, Role::Stair),
        ] {
            users.of_role(role).insert(at(k));
        }
        for (stair, ray) in [(false, false), (true, false), (false, true), (true, true)] {
            let mut want: BTreeSet<PartAt> = users.plain.iter().cloned().collect();
            if !stair {
                want.extend(users.stair.iter().cloned());
            }
            if !ray {
                want.extend(users.ray.iter().cloned());
            }
            let got: Vec<PartAt> = users.due(stair, ray).cloned().collect();
            assert_eq!(got, want.into_iter().collect::<Vec<_>>(), "{stair} {ray}");
        }
        assert_eq!(users.due(false, false).count(), 7);
    }

    /// Gives `pot` a new component without names, ranked by [`Potential::rank_after`] at
    /// `place` in `list`, the components in the order of their ranks, and returns the number
    /// of other components ranked again.
    fn rank_at(pot: &mut Potential, list: &mut Vec<u64>, place: usize) -> usize {
        let c = pot.next;
        pot.next += 1;
        let part = Component {
            rank: 0,
            names: imbl::OrdSet::new(),
            ends: imbl::OrdSet::new(),
        };
        pot.parts.insert(c, part);
        let after = place.checked_sub(1).map(|k| pot.rank(list[k]));
        let moved = pot.rank_after(c, after);
        list.insert(place, c);
        moved
    }

    /// The ranks of `pot` are those of `list`, in order, each its component's, and within
    /// `0..RANKS`.
    fn check_ranks(pot: &Potential, list: &[u64]) {
        assert_eq!(pot.order.values().copied().collect::<Vec<u64>>(), list);
        for (&r, &c) in &pot.order {
            assert_eq!(pot.rank(c), r);
            assert!((0..RANKS).contains(&r), "{r}");
        }
    }

    /// Components ranked first, last and between two, the empty potential first, keep the
    /// order they were given in, and their ranks are their components'.
    #[test]
    fn ranks_keep_the_order_they_are_given_in() {
        let mut pot = Potential::default();
        let mut list = Vec::new();
        assert_eq!(pot.last(), None);
        assert_eq!(rank_at(&mut pot, &mut list, 0), 0);
        check_ranks(&pot, &list);
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        for k in 0..1500 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let place = match k % 4 {
                0 => 0,
                1 => list.len(),
                _ => seed as usize % (list.len() + 1),
            };
            rank_at(&mut pot, &mut list, place);
            check_ranks(&pot, &list);
        }
    }

    /// Ranks given one after another at either end, 10,000 of them, rank no other component
    /// again, each at most `END_STEP` from the one before; ranks then put between the last
    /// two halve that step, the order kept.
    #[test]
    fn ranks_given_one_after_another_at_an_end_rank_no_other_again() {
        for last in [false, true] {
            let mut pot = Potential::default();
            let mut list = Vec::new();
            for k in 0..10_000 {
                let place = if last { list.len() } else { 0 };
                let moved = rank_at(&mut pot, &mut list, place);
                assert_eq!(moved, 0, "{last}: rank {k} ranked {moved} others again");
            }
            check_ranks(&pot, &list);
            let ranks: Vec<i64> = pot.order.keys().copied().collect();
            assert!(ranks.windows(2).all(|w| w[1] - w[0] <= END_STEP), "{last}");
            for _ in 0..20 {
                let place = if last { list.len() - 1 } else { 1 };
                assert_eq!(rank_at(&mut pot, &mut list, place), 0, "{last}");
            }
            check_ranks(&pot, &list);
        }
    }

    /// A rank given at an end of `0..RANKS` that is taken ranks a range again, the order
    /// kept, and ranks given at that end after it keep their order.
    #[test]
    fn ranks_given_at_either_end_rank_a_full_range_again() {
        for last in [false, true] {
            let mut pot = Potential::default();
            let mut list = Vec::new();
            rank_at(&mut pot, &mut list, 0);
            // The one component moved to the end of the ranks.
            let c = list[0];
            pot.rerank(c, if last { RANKS - 1 } else { 0 });
            let place = if last { list.len() } else { 0 };
            assert!(rank_at(&mut pot, &mut list, place) > 0, "{last}");
            check_ranks(&pot, &list);
            for _ in 0..200 {
                let place = if last { list.len() } else { 0 };
                rank_at(&mut pot, &mut list, place);
            }
            check_ranks(&pot, &list);
        }
    }

    /// Components ranked each right after the first, 500 of them, keep their order, and the
    /// ranks between run out, past the 62 halvings of the ranks between two neighbors, and are
    /// given again; components ranked each at the front keep their order. The benchmark
    /// `bench::ranks_given_in_one_place_scale` measures the count ranked again.
    #[test]
    fn ranks_given_in_one_place_keep_their_order() {
        for front in [false, true] {
            let mut pot = Potential::default();
            let mut list = Vec::new();
            rank_at(&mut pot, &mut list, 0);
            let moved: usize = (0..500)
                .map(|_| rank_at(&mut pot, &mut list, usize::from(!front)))
                .sum();
            check_ranks(&pot, &list);
            assert!(front || moved > 0, "no component ranked again");
        }
    }
}

/// The comparison of the tests `Scope::extend_path` admits and the rows
/// `Scope::extend_threshold` certifies with the solver's scope for the same test (item
/// ST-walk-checker-admit): while it is on, on this thread, each admitted test also runs the
/// solver's path on a copy of the scope it started from, with no test admitted on the way,
/// and records where the two scopes differ: `bottom`, the settled product of each name
/// ([`Scope::settled`]), the relation, the ends tests gave single names, and the refusals. Built
/// only with the feature `preimage-ref`; the tests of step L1.39 turn it on around the checker
/// and around `Run::walk_arms`.
#[cfg(feature = "preimage-ref")]
#[doc(hidden)]
pub mod path_check {
    use super::*;
    use std::cell::{Cell, RefCell};

    thread_local! {
        static ON: Cell<bool> = const { Cell::new(false) };
        static REFERENCE: Cell<bool> = const { Cell::new(false) };
        static ADMITTED: Cell<u64> = const { Cell::new(0) };
        static DIFFERENCES: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
    }

    /// Starts comparing on this thread, with no admission counted and no difference found.
    pub fn start() {
        ON.set(true);
        ADMITTED.set(0);
        DIFFERENCES.take();
    }

    /// Stops comparing: the tests admitted since [`start`] and the differences found.
    pub fn stop() -> (u64, Vec<String>) {
        ON.set(false);
        (ADMITTED.take(), DIFFERENCES.take())
    }

    /// Whether the solver's path is being run for a comparison, so that no test is admitted.
    pub(super) fn reference() -> bool {
        REFERENCE.get()
    }

    /// `f` run as the solver's path, with no test admitted.
    pub(super) fn as_reference<T>(f: impl FnOnce() -> T) -> T {
        let was = REFERENCE.replace(true);
        let out = f();
        REFERENCE.set(was);
        out
    }

    fn on() -> bool {
        if !ON.get() || REFERENCE.get() {
            return false;
        }
        ADMITTED.set(ADMITTED.get() + 1);
        true
    }

    fn record(d: String) {
        DIFFERENCES.with_borrow_mut(|ds| ds.push(d));
    }

    /// Compares `new`, the scope of an admitted test, with the solver's scope `old` gives.
    pub(super) fn compare(new: &Scope, old: impl FnOnce() -> Scope) {
        if !on() {
            return;
        }
        let old = old();
        if new.bottom != old.bottom {
            return record(format!(
                "bottom {} where the solver gives {}",
                new.bottom, old.bottom
            ));
        }
        if new.bottom {
            return;
        }
        let keys = |s: &Scope| s.names.keys().cloned().collect::<Vec<_>>();
        if keys(new) != keys(&old) {
            return record(format!(
                "names {:?} where the solver has {:?}",
                keys(new),
                keys(&old)
            ));
        }
        for n in keys(&old) {
            let (a, b) = (new.settled(&n), old.settled(&n));
            if a != b {
                record(format!("{n}: {a:?} where the solver gives {b:?}"));
            }
        }
        // A relation may differ in form alone: a certified row whose first case no point of
        // the box meets keeps its live case (`Scope::extend_threshold`), as a forward order
        // does, where the solver given the conjunction at once keeps both. Two relations of
        // different forms are compared by their points, each with the other's negation.
        let whole =
            |s: &Scope| Formula::and(s.relation.set().iter().map(|f| (**f).clone()).collect());
        let within = |a: &Formula, b: &Formula| {
            let f = Formula::and(vec![a.clone(), Formula::negate(b.clone())]);
            matches!(presburger::satisfiable(&f), Ok(None))
        };
        if *new.relation != *old.relation
            && !{
                let (a, b) = (whole(new), whole(&old));
                within(&a, &b) && within(&b, &a)
            }
        {
            record(format!(
                "relation {} where the solver has {}",
                new.relation, old.relation
            ));
        }
        if new.direct != old.direct {
            record(format!(
                "direct {:?} where the solver has {:?}",
                new.direct, old.direct
            ));
        }
        if new.refusals != old.refusals {
            record(format!(
                "refusals {:?} where the solver has {:?}",
                new.refusals, old.refusals
            ));
        }
    }

    /// Compares an answer of an admitted test with the solver's.
    pub(super) fn compare_value<T: PartialEq + std::fmt::Debug>(new: T, old: impl FnOnce() -> T) {
        if !on() {
            return;
        }
        let old = old();
        if new != old {
            record(format!("{new:?} where the solver gives {old:?}"));
        }
    }
}
