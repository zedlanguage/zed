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
//! The domains here are those of step L1.24: intervals with symbolic affine bounds,
//! congruences, finite sets of scalars and atoms, float classes and lengths. The cell's type,
//! linear relations and binding time join it, with the reduction between its domains, at step
//! L1.39.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use zed_kernel::Value;
use zed_kernel::provenance::FactAddress;

use super::affine::{Affine, Bounds};
use super::float::FloatClass;
use super::interval::IntervalSet;
use super::lattice::{Congruence, FiniteSet, Lattice};

/// What an element rests on.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Premise {
    /// A written constraint, a declared type or a narrowing test at this address.
    Constraint(FactAddress),
    /// The widening at the component head with this address, which gave more than the join.
    Widened(FactAddress),
}

/// An element and the premises it rests on.
#[derive(Clone, PartialEq, Debug)]
pub struct Entry<L> {
    /// The element.
    pub element: L,
    /// What the element rests on.
    pub premises: BTreeSet<Premise>,
}

impl<L: Lattice> Entry<L> {
    /// The element with no premise.
    pub fn new(element: L) -> Self {
        Entry {
            element,
            premises: BTreeSet::new(),
        }
    }

    /// Meets `element`, which rests on `premises`, into the entry. Returns whether the element
    /// changed; the premises are added only then.
    pub fn meet(&mut self, element: &L, premises: &BTreeSet<Premise>) -> bool {
        let m = self.element.meet(element);
        if m == self.element {
            return false;
        }
        self.element = m;
        self.premises.extend(premises.iter().cloned());
        true
    }

    /// Joins `other` into the entry, with both sides' premises. Returns whether the element
    /// changed.
    pub fn join(&mut self, other: &Entry<L>) -> bool {
        let j = self.element.join(&other.element);
        self.premises.extend(other.premises.iter().cloned());
        let changed = j != self.element;
        self.element = j;
        changed
    }

    /// Widens the entry by `other` at the component head `head`: the widening of the join,
    /// with both sides' premises and, when the widening gives more than the join, the
    /// widening itself. Returns whether the element changed.
    pub fn widen(&mut self, other: &Entry<L>, head: &FactAddress) -> bool {
        let joined = self.element.join(&other.element);
        let w = self.element.widen(&joined);
        self.premises.extend(other.premises.iter().cloned());
        if w != joined {
            self.premises.insert(Premise::Widened(head.clone()));
        }
        let changed = w != self.element;
        self.element = w;
        changed
    }

    /// Whether the element rests on no widening.
    pub fn proof_grade(&self) -> bool {
        !self
            .premises
            .iter()
            .any(|p| matches!(p, Premise::Widened(_)))
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
            Value::Float(x) => c.float.element = FloatClass::of(x.get()),
            Value::Str(s) => {
                let n = s.chars().count() as i64;
                c.length.element = Bounds::ints(IntervalSet::single(n));
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
    pub fn widen(&mut self, other: &Cell, head: &FactAddress) -> bool {
        let changed = [
            self.ints.widen(&other.ints, head),
            self.congruence.widen(&other.congruence, head),
            self.finite.widen(&other.finite, head),
            self.float.widen(&other.float, head),
            self.length.widen(&other.length, head),
        ]
        .contains(&true);
        // A widening can send a length's lower end to minus infinity; a meet or a join keeps it
        // within the top, `[0..]`.
        self.length.element = self.length.element.meet(&Cell::sizes());
        changed
    }

    /// The premises of every entry: the cell's certificate.
    pub fn premises(&self) -> BTreeSet<Premise> {
        let mut out = BTreeSet::new();
        for p in [
            &self.ints.premises,
            &self.congruence.premises,
            &self.finite.premises,
            &self.float.premises,
            &self.length.premises,
        ] {
            out.extend(p.iter().cloned());
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
