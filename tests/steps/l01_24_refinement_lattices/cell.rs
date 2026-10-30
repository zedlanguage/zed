//! Cells and the premises their elements rest on.

use std::collections::BTreeSet;

use zed_kernel::Value;
use zed_kernel::provenance::{FactAddress, NodeAddress};
use zedc::store::affine::{Affine, Bounds};
use zedc::store::cell::{Cell, Entry, Premise, Premises, Store};
use zedc::store::float::{FloatClass, Kind, Width};
use zedc::store::interval::IntervalSet;
use zedc::store::lattice::{FiniteSet, Lattice};

/// The fact at node `n` with no keypath.
fn addr(n: u32) -> FactAddress {
    FactAddress {
        node: NodeAddress(vec![0, n]),
        keypath: Vec::new(),
    }
}

fn because(n: u32) -> Premises {
    Premises::one(Premise::Constraint(addr(n)))
}

#[test]
fn a_meet_adds_its_premises_only_when_it_narrows() {
    // `let i: int[0..<n] = ...`, then a test `i < 10`, then a test `i < n + 5`.
    let n = Affine::sym("n");
    let mut e = Entry::new(Bounds::top());
    assert!(e.meet(
        &Bounds::range(Some(Affine::constant(0)), n.plus(-1)),
        &because(1)
    ));
    assert!(e.meet(&Bounds::range(None, Some(Affine::constant(9))), &because(2)));
    // `n + 4` with the same terms is looser than `n - 1`, so the test changes nothing and the
    // element does not rest on it.
    assert!(!e.meet(&Bounds::range(None, n.plus(4)), &because(3)));
    assert_eq!(e.element.to_string(), "[0..=min(9, n - 1)]");
    assert_eq!(
        e.premises,
        BTreeSet::from([Premise::Constraint(addr(1)), Premise::Constraint(addr(2))])
    );
    assert!(e.proof_grade());
}

#[test]
fn a_join_rests_on_both_sides() {
    // `if c { x = 1 } else { x = y }` with `y: int[3..=5]` declared at node 4.
    let mut then = Entry::new(Bounds::ints(IntervalSet::single(1)));
    let mut other = Entry::new(Bounds::top());
    other.meet(&Bounds::ints(IntervalSet::of(3, 5)), &because(4));
    assert!(then.join(&other));
    assert_eq!(then.element.to_string(), "[1..=1, 3..=5]");
    assert_eq!(then.premises, because(4));
    // Joining a side already below adds its premises, and changes nothing else.
    let mut lit = Entry::new(Bounds::ints(IntervalSet::single(3)));
    lit.premises = because(5);
    assert!(!then.join(&lit));
    assert!(then.premises.contains(&Premise::Constraint(addr(5))));
}

#[test]
fn a_widening_past_the_join_is_a_premise_and_not_proof_grade() {
    let head = addr(7);
    // A counter at a loop head: 0, then 0 or 1, then widened.
    let mut e = Entry::new(Bounds::ints(IntervalSet::single(0)));
    let step = Entry::new(Bounds::ints(IntervalSet::of(0, 1)));
    assert!(e.widen(&step, &head));
    assert_eq!(e.element.to_string(), "[0..]");
    assert_eq!(e.premises, BTreeSet::from([Premise::Widened(head.clone())]));
    assert!(!e.proof_grade());
    // A widening that gives only the join, as in a lattice of finite height, adds nothing.
    let mut f = Entry::new(FloatClass::new(&[Kind::Finite], Width::F32));
    let g = Entry::new(FloatClass::new(&[Kind::NaN], Width::F64));
    assert!(f.widen(&g, &head));
    assert!(f.proof_grade());
    let mut s = Entry::new(FiniteSet::of([Value::str("a")]));
    assert!(s.widen(&Entry::new(FiniteSet::of([Value::str("b")])), &head));
    assert!(s.proof_grade());
}

#[test]
fn a_literal_fills_the_domains_that_read_its_kind() {
    let int = Cell::literal(&Value::Int(6));
    assert_eq!(int.to_string(), "ints [6..=6]\ncongruence 6\nfinite {6}\n");
    let s = Cell::literal(&Value::str("héllo"));
    assert_eq!(s.to_string(), "finite {\"héllo\"}\nlength [5..=5]\n");
    let x = Cell::literal(&Value::float(0.5));
    assert_eq!(x.to_string(), "finite {0.5}\nfloat f16{finite}\n");
    assert!(x.premises().is_empty());
    assert_eq!(Cell::top().to_string(), "");
}

#[test]
fn a_length_is_never_negative() {
    // `s::len <= n` for a string `s`: the length is `[0..=n]`, and a length below zero leaves
    // the cell empty.
    let mut c = Cell::top();
    let n = Affine::sym("n");
    assert!(c.length.meet(&Bounds::range(None, Some(n)), &because(1)));
    assert_eq!(c.length.element.to_string(), "[0..=n]");
    assert_eq!(Cell::top().length.element.to_string(), "[0..]");
    let mut d = Cell::top();
    d.length
        .meet(&Bounds::ints(IntervalSet::of(-3, -1)), &because(2));
    assert_eq!(d.length.element, Bounds::bottom());
    // A widening whose lower end moves goes to minus infinity, and the cell keeps the length
    // at zero or more.
    let mut e = Cell::literal(&Value::str("abc"));
    assert!(e.widen(&Cell::literal(&Value::str("ab")), &addr(8)));
    assert_eq!(e.length.element.to_string(), "[0..=3]");
}

#[test]
fn a_cell_joins_and_widens_entry_by_entry() {
    let head = addr(9);
    let mut store = Store::new();
    let a = addr(1);
    assert_eq!(store.cell(&a), Cell::top());
    *store.cell_mut(&a) = Cell::literal(&Value::Int(0));
    let one = Cell::literal(&Value::Int(1));
    assert!(store.cell_mut(&a).join(&one));
    assert_eq!(store.cell(&a).to_string(), "ints [0..=1]\nfinite {0, 1}\n");
    let two = Cell::literal(&Value::Int(2));
    assert!(store.cell_mut(&a).widen(&two, &head));
    let c = store.cell(&a);
    assert_eq!(c.to_string(), "ints [0..]\nfinite {0, 1, 2}\n");
    assert!(!c.ints.proof_grade());
    assert!(c.finite.proof_grade());
    assert_eq!(c.premises(), BTreeSet::from([Premise::Widened(head)]));
    assert_eq!(store.cells().count(), 1);
}
