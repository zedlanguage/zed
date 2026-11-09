//! The store's cells (DESIGN.md sec:domains, the engine paragraph; step L1.24).
//!
//! Every fact address owns a cell, and the cell holds one element per domain, each with the
//! premises it rests on. A premise is a written constraint, a declared type or a narrowing test,
//! named by its fact address, or a widening that gave more than the join at a component head.
//! A cell's premise set is its certificate (sec:constraints), and an element that rests on a
//! widening is not proof-grade evidence (sec:property_tracking).
//!
//! An entry's premises change with its element. A meet that narrows the element adds the
//! premises of what it met with; a meet that changes nothing adds none, since the element did
//! not need it. A join adds the premises of both sides, since the joined element holds only if
//! each side does. A widening joins, and adds the widening as a premise when it gives more
//! than the join.
//!
//! A premise set is [`Premises`], which shares what two sets have in common: a union takes
//! constant time, so a chain of `k` narrowings costs `O(k)` and not `O(k²)` (the rule of low
//! complexity, DESIGN.md Part G). The set itself is built only when it is read.
//!
//! The domains here are those of step L1.24: intervals with symbolic affine bounds,
//! congruences, finite sets of scalars and atoms, float classes and lengths. The cell's type,
//! linear relations and binding time join it, with the reduction between its domains, at step
//! L1.39.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::provenance::FactAddress;
use zed_kernel::value::{Id, fresh_id};

use super::affine::{Affine, Bounds};
use super::float::FloatClass;
use super::interval::{IntervalSet, Num};
use super::landmarks::Landmarks;
use super::lattice::{Congruence, FiniteSet, Lattice};

/// What an element rests on.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Premise {
    /// A written constraint, a declared type or a narrowing test at this address.
    Constraint(FactAddress),
    /// The widening at the component head with this address, which gave more than the join.
    Widened(FactAddress),
}

/// A set of premises whose union takes constant time: a set is one premise, or the union of
/// two sets it shares with whatever else holds them.
// Complexity tradeoff: the standard set (a `BTreeSet` copied at each narrowing and union) costs
// O(m) per union, O(n²) over a loop summary of n steps. Used: a union is a node holding both
// sides, O(1), and `Premises::set` reads the shared nodes once each by a visited set of ids,
// O(m log m) for m distinct parts; walked as a tree it would cost the number of paths, n²/2
// for a loop of n iterations and exponential in depth where every level shares (93.0 times the
// instructions at 200 → 1600 without the visited set). Tradeoffs: an `Arc` node and a `u64`
// id per union; a premise met twice is kept in the node graph until `set` dedupes it;
// `contains` and `set` cost a walk, not a lookup. Ids, never addresses, key the visited set.
// Tests: `l01_24_refinement_lattices::cell::reading_a_shared_premise_set_scales` and
// `l01_39_reduced_product::scaling`; COMPLEXITY.md rows S8 and S35.
#[derive(Clone, Default)]
pub struct Premises(Option<Arc<Node>>);

struct Node {
    /// The node's id, drawn when it is built: copies of a set share it and no other node has
    /// it, so a walk knows a shared part met again by its id, never by its address.
    id: Id,
    /// Whether a premise of the set is a widening.
    widened: bool,
    /// The greatest id of the sets of one premise the set is a union of: a part whose
    /// `newest` is below the first id [`Premises::without`] drops holds none of those it drops.
    newest: Id,
    kind: Kind,
}

enum Kind {
    One(Premise),
    Both(Premises, Premises),
}

impl Premises {
    /// The empty set.
    pub fn new() -> Premises {
        Premises(None)
    }

    /// The set of `p` alone.
    pub fn one(p: Premise) -> Premises {
        let id = fresh_id();
        Premises(Some(Arc::new(Node {
            id,
            widened: matches!(p, Premise::Widened(_)),
            newest: id,
            kind: Kind::One(p),
        })))
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// Whether a premise of the set is a widening.
    pub fn widened(&self) -> bool {
        self.0.as_ref().is_some_and(|n| n.widened)
    }

    /// Adds every premise of `other`, in constant time.
    pub fn extend(&mut self, other: &Premises) {
        match (&self.0, &other.0) {
            (_, None) => {}
            (None, Some(_)) => *self = other.clone(),
            (Some(a), Some(b)) if a.id == b.id => {}
            (Some(a), Some(b)) => {
                let widened = a.widened || b.widened;
                let newest = a.newest.max(b.newest);
                let both = Kind::Both(self.clone(), other.clone());
                *self = Premises(Some(Arc::new(Node {
                    id: fresh_id(),
                    widened,
                    newest,
                    kind: both,
                })));
            }
        }
    }

    /// The set without the premises of the sets in `drop`, each a set of one premise
    /// ([`Premises::one`]), sorted by when it was made, all made by this thread: the set a
    /// caller would have had, had it never added those, since a union only adds premises.
    /// A part is dropped by its id, so a premise equal to one of `drop` but made apart from
    /// it stays.
    ///
    /// Complexity tradeoff: the naive removal rebuilds every union of the set, `O(m)` for `m`
    /// parts, so that a walk removing the premises of each `if` it nests from the value
    /// below cost `O(d²)` for `d` nested `if`s. Here a part is entered only when it holds a
    /// set of one premise made at or after the first of `drop` (its `newest`, kept in `O(1)`
    /// a union), and each part entered once, by id: `O(e log e + e log k)` for `e` parts
    /// entered and `k` sets in `drop`. Given up: a part made by another thread after the
    /// first of `drop`, whose ids may be greater, is entered though it holds none of them;
    /// a part with no premise to drop rebuilt from parts that changed is a new union.
    /// Trigger: `if`s nested in the arms of `if`s whose value is read
    /// (`product::Run::walk_value`). Test:
    /// `l01_39_reduced_product::if_shortcut::one_pass_and_transfer_scale_on_deep_nests`,
    /// COMPLEXITY.md row PA-walk-nest-cost.
    pub fn without(&self, drop: &[Premises]) -> Premises {
        let id = |p: &Premises| p.0.as_ref().map(|n| n.id);
        let Some(first) = drop.first().and_then(id) else {
            return self.clone();
        };
        fn entered(p: &Premises, first: Id) -> Option<&Arc<Node>> {
            p.0.as_ref().filter(|n| n.newest >= first)
        }
        let mut out: HashMap<Id, Premises> = HashMap::new();
        let mut todo: Vec<(&Premises, bool)> = vec![(self, false)];
        while let Some((p, ready)) = todo.pop() {
            let Some(n) = entered(p, first) else { continue };
            if out.contains_key(&n.id) {
                continue;
            }
            match &n.kind {
                Kind::One(_) => {
                    let gone = drop.binary_search_by_key(&Some(n.id), id).is_ok();
                    out.insert(n.id, if gone { Premises::new() } else { p.clone() });
                }
                Kind::Both(a, b) if ready => {
                    let part = |q: &Premises| {
                        entered(q, first).map_or_else(|| q.clone(), |m| out[&m.id].clone())
                    };
                    let (mut x, y) = (part(a), part(b));
                    let kept = if x.same(a) && y.same(b) {
                        p.clone()
                    } else {
                        x.extend(&y);
                        x
                    };
                    out.insert(n.id, kept);
                }
                Kind::Both(a, b) => todo.extend([(p, true), (a, false), (b, false)]),
            }
        }
        entered(self, first).map_or_else(|| self.clone(), |n| out[&n.id].clone())
    }

    /// Whether both are the same shared set, or both empty: `O(1)`, where `==` compares the
    /// premises when the sets are not shared.
    pub fn same(&self, other: &Premises) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (Some(a), Some(b)) => a.id == b.id,
            _ => false,
        }
    }

    /// Adds `p`.
    pub fn insert(&mut self, p: Premise) {
        self.extend(&Premises::one(p));
    }

    /// The premises, each once, in order. It visits each shared part once, knowing it by its id,
    /// so for `m` distinct parts it costs `O(m log m)`, however many paths reach a part.
    pub fn set(&self) -> BTreeSet<Premise> {
        let mut out = BTreeSet::new();
        let mut seen = HashSet::new();
        let mut todo: Vec<&Arc<Node>> = self.0.iter().collect();
        while let Some(n) = todo.pop() {
            if !seen.insert(n.id) {
                continue;
            }
            match &n.kind {
                Kind::One(p) => {
                    out.insert(p.clone());
                }
                Kind::Both(a, b) => todo.extend(a.0.iter().chain(b.0.iter())),
            }
        }
        out
    }

    /// Whether `p` is a premise of the set.
    pub fn contains(&self, p: &Premise) -> bool {
        self.set().contains(p)
    }
}

impl Drop for Premises {
    /// Drops a long chain of unions without one stack frame per union.
    fn drop(&mut self) {
        let mut todo: Vec<Arc<Node>> = self.0.take().into_iter().collect();
        while let Some(n) = todo.pop() {
            if let Ok(mut n) = Arc::try_unwrap(n)
                && let Kind::Both(a, b) = &mut n.kind
            {
                todo.extend(a.0.take().into_iter().chain(b.0.take()));
            }
        }
    }
}

impl PartialEq for Premises {
    /// The same premises: at once when both are the same shared set or one is empty.
    fn eq(&self, other: &Premises) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (None, _) | (_, None) => false,
            (Some(a), Some(b)) => a.id == b.id || self.set() == other.set(),
        }
    }
}

impl PartialEq<BTreeSet<Premise>> for Premises {
    fn eq(&self, other: &BTreeSet<Premise>) -> bool {
        &self.set() == other
    }
}

impl fmt::Debug for Premises {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.set().fmt(f)
    }
}

impl From<BTreeSet<Premise>> for Premises {
    fn from(ps: BTreeSet<Premise>) -> Premises {
        ps.into_iter()
            .map(Premises::one)
            .fold(Premises::new(), |mut a, b| {
                a.extend(&b);
                a
            })
    }
}

/// An element and the premises it rests on.
#[derive(Clone, PartialEq, Debug)]
pub struct Entry<L> {
    /// The element.
    pub element: L,
    /// What the element rests on.
    pub premises: Premises,
}

impl<L: Lattice> Entry<L> {
    /// The element with no premise.
    pub fn new(element: L) -> Self {
        Entry {
            element,
            premises: Premises::new(),
        }
    }

    /// Meets `element`, which rests on `premises`, into the entry. Returns whether the element
    /// changed; the premises are added only then.
    pub fn meet(&mut self, element: &L, premises: &Premises) -> bool {
        let m = self.element.meet(element);
        if m == self.element {
            return false;
        }
        self.element = m;
        self.premises.extend(premises);
        true
    }

    /// Joins `other` into the entry, with both sides' premises. Returns whether the element
    /// changed.
    pub fn join(&mut self, other: &Entry<L>) -> bool {
        let j = self.element.join(&other.element);
        self.premises.extend(&other.premises);
        let changed = j != self.element;
        self.element = j;
        changed
    }

    /// Widens the entry by `other` at the component head `head`: the widening of the join,
    /// with both sides' premises and, when the widening gives more than the join, the
    /// widening itself. Returns whether the element changed.
    pub fn widen(&mut self, other: &Entry<L>, head: &FactAddress, marks: &Landmarks) -> bool {
        let joined = self.element.join(&other.element);
        let w = self.element.widen(&joined, marks);
        self.premises.extend(&other.premises);
        if w != joined {
            self.premises.insert(Premise::Widened(head.clone()));
        }
        let changed = w != self.element;
        self.element = w;
        changed
    }

    /// Whether the element rests on no widening.
    pub fn proof_grade(&self) -> bool {
        !self.premises.widened()
    }
}

/// The elements of one fact.
#[derive(Clone, PartialEq, Debug)]
pub struct Cell {
    /// The integer values.
    pub ints: Entry<Bounds>,
    /// The integer values' residue class.
    pub congruence: Entry<Congruence>,
    /// The scalar and atom values, when finitely many.
    pub finite: Entry<FiniteSet<Value>>,
    /// The float values.
    pub float: Entry<FloatClass>,
    /// The length of a string, or the cardinality of a family's level: never negative.
    pub length: Entry<Bounds>,
}

impl Cell {
    /// The cell with no information.
    pub fn top() -> Cell {
        Cell {
            ints: Entry::new(Bounds::top()),
            congruence: Entry::new(Congruence::top()),
            finite: Entry::new(FiniteSet::top()),
            float: Entry::new(FloatClass::top()),
            length: Entry::new(Cell::sizes()),
        }
    }

    /// The nonnegative integers, the top of a length.
    pub fn sizes() -> Bounds {
        Bounds::range(Some(Affine::constant(0)), None)
    }

    /// The cell of a literal: the singleton in each domain that reads its kind, and no
    /// information in the others (sec:domains, literal domains). A literal rests on nothing.
    pub fn literal(v: &Value) -> Cell {
        let mut c = Cell::top();
        c.finite.element = FiniteSet::of([v.clone()]);
        match v {
            Value::Int(n) => {
                c.ints.element = Bounds::ints(IntervalSet::single(*n));
                c.congruence.element = Congruence::single(*n);
            }
            Value::Big(n) => {
                let n = Num::from(&**n);
                c.ints.element = Bounds::ints(IntervalSet::point(n.clone()));
                c.congruence.element = Congruence::single(n);
            }
            Value::Float(x) => c.float.element = FloatClass::of(x.get()),
            Value::Str(s) => {
                c.length.element =
                    Bounds::ints(IntervalSet::point(Num::from(s.char_count() as i128)));
            }
            _ => {}
        }
        c
    }

    /// Joins `other` into the cell, entry by entry. Returns whether an element changed.
    pub fn join(&mut self, other: &Cell) -> bool {
        // Every entry joins, so no `||` short circuit.
        [
            self.ints.join(&other.ints),
            self.congruence.join(&other.congruence),
            self.finite.join(&other.finite),
            self.float.join(&other.float),
            self.length.join(&other.length),
        ]
        .contains(&true)
    }

    /// Widens the cell by `other` at the component head `head`, entry by entry. Returns
    /// whether an element changed.
    pub fn widen(&mut self, other: &Cell, head: &FactAddress, marks: &Landmarks) -> bool {
        let changed = [
            self.ints.widen(&other.ints, head, marks),
            self.congruence.widen(&other.congruence, head, marks),
            self.finite.widen(&other.finite, head, marks),
            self.float.widen(&other.float, head, marks),
            self.length.widen(&other.length, head, marks),
        ]
        .contains(&true);
        // A widening can send a length's lower end to minus infinity; a meet or a join keeps it
        // within the top, `[0..]`.
        self.length.element = self.length.element.meet(&Cell::sizes());
        changed
    }

    /// The premises of every entry: the cell's certificate.
    pub fn premises(&self) -> Premises {
        let mut out = Premises::new();
        for p in [
            &self.ints.premises,
            &self.congruence.premises,
            &self.finite.premises,
            &self.float.premises,
            &self.length.premises,
        ] {
            out.extend(p);
        }
        out
    }
}

impl fmt::Display for Cell {
    /// The entries that hold information, one per line: `ints [0..=n - 1]`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let top = Cell::top();
        if self.ints != top.ints {
            writeln!(f, "ints {}", self.ints.element)?;
        }
        if self.congruence != top.congruence {
            writeln!(f, "congruence {}", self.congruence.element)?;
        }
        if let FiniteSet::Set(s) = &self.finite.element {
            let items: Vec<String> = s.iter().map(|v| v.to_string()).collect();
            writeln!(f, "finite {{{}}}", items.join(", "))?;
        }
        if self.float != top.float {
            writeln!(f, "float {}", self.float.element)?;
        }
        if self.length != top.length {
            writeln!(f, "length {}", self.length.element)?;
        }
        Ok(())
    }
}

/// The cells of a program's facts, by fact address. An address with no cell has the top.
#[derive(Clone, Default, Debug)]
pub struct Store {
    cells: BTreeMap<FactAddress, Cell>,
}

impl Store {
    /// The empty store.
    pub fn new() -> Store {
        Store::default()
    }

    /// The cell at `addr`, the top when it has none.
    pub fn cell(&self, addr: &FactAddress) -> Cell {
        self.cells.get(addr).cloned().unwrap_or_else(Cell::top)
    }

    /// The cell at `addr`, created at the top.
    pub fn cell_mut(&mut self, addr: &FactAddress) -> &mut Cell {
        self.cells.entry(addr.clone()).or_insert_with(Cell::top)
    }

    /// The cells, in address order.
    pub fn cells(&self) -> impl Iterator<Item = (&FactAddress, &Cell)> {
        self.cells.iter()
    }
}
