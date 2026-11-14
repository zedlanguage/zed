//! Cells and the premises their elements rest on.

use std::collections::BTreeSet;

use zed_kernel::provenance::{FactAddress, NodeAddress, Position, Vector};
use zed_kernel::{Text, Value};
use zedc::store::affine::{Affine, Bounds};
use zedc::store::cell::{Cell, Entry, Premise, Premises, Store};
use zedc::store::float::{FloatClass, Kind, Width};
use zedc::store::interval::{IntervalSet, Num};
use zedc::store::landmarks::Landmarks;
use zedc::store::lattice::{FiniteSet, Lattice};

/// The fact at node `n` with no keypath.
fn addr(n: u32) -> FactAddress {
    FactAddress {
        node: NodeAddress(Vector::from(vec![
            Position::root(),
            Position::root().child(n),
        ])),
        keypath: Vector::new(),
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
        &Bounds::range(Some(Affine::constant(0)), Some(n.plus(-1))),
        &because(1)
    ));
    assert!(e.meet(&Bounds::range(None, Some(Affine::constant(9))), &because(2)));
    // `n + 4` with the same terms is looser than `n - 1`, so the test changes nothing and the
    // element does not rest on it.
    assert!(!e.meet(&Bounds::range(None, Some(n.plus(4))), &because(3)));
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
    assert!(e.widen(&step, &head, &Landmarks::none()));
    assert_eq!(e.element.to_string(), "[0..]");
    assert_eq!(e.premises, BTreeSet::from([Premise::Widened(head.clone())]));
    assert!(!e.proof_grade());
    // A widening that gives only the join, as in a lattice of finite height, adds nothing.
    let mut f = Entry::new(FloatClass::new(&[Kind::Finite], Width::F32));
    let g = Entry::new(FloatClass::new(&[Kind::NaN], Width::F64));
    assert!(f.widen(&g, &head, &Landmarks::none()));
    assert!(f.proof_grade());
    // A finite set keeps a new member that the program writes, and gives the top for one it
    // does not.
    let b = Entry::new(FiniteSet::of([Value::str("b")]));
    let mut s = Entry::new(FiniteSet::of([Value::str("a")]));
    assert!(s.widen(
        &b,
        &head,
        &Landmarks::of(std::iter::empty::<i64>(), [Value::str("b")])
    ));
    assert_eq!(s.element, FiniteSet::of([Value::str("a"), Value::str("b")]));
    assert!(s.proof_grade());
    let mut t = Entry::new(FiniteSet::of([Value::str("a")]));
    assert!(t.widen(&b, &head, &Landmarks::none()));
    assert_eq!(t.element, FiniteSet::Top);
    assert!(!t.proof_grade());
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

/// `s0 = "a"; s1 = s0 ++ s0; …`: the string doubled `k` times, `2^k` characters in `k` nodes,
/// never written out.
#[cfg(target_pointer_width = "64")]
fn doubled(k: u32) -> Value {
    let mut s = Text::from("a");
    for _ in 0..k {
        s = Text::join(&s, &s).expect("2^63 bytes fit in a usize");
    }
    Value::Str(s)
}

#[test]
#[cfg(target_pointer_width = "64")]
fn a_string_too_long_for_an_i64_has_its_exact_length() {
    // A buffer filled by doubling a block: up to 2^62 characters the length is exact.
    let s62 = Cell::literal(&doubled(62));
    assert_eq!(
        s62.length.element,
        Bounds::ints(IntervalSet::single(1 << 62))
    );
    // 2^63 characters is one past `i64::MAX`, where `len` is a big integer, and the length is
    // that one integer; a wrapped cast gave `[i64::MIN]`, negative.
    let s63 = Cell::literal(&doubled(63));
    assert_eq!(
        s63.length.element,
        Bounds::ints(IntervalSet::point(Num::from(1i128 << 63)))
    );
    assert_eq!(
        s63.length.element.to_string(),
        "[9223372036854775808..=9223372036854775808]"
    );
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
    assert!(e.widen(
        &Cell::literal(&Value::str("ab")),
        &addr(8),
        &Landmarks::none()
    ));
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
    // The program writes 1 (so 0, 1 and 2 are landmarks) and 3: the interval stops at 2, and
    // the finite set keeps 2.
    let marks = Landmarks::of([1], []);
    let mut b = store.cell(&a);
    assert!(b.widen(&two, &head, &marks));
    assert_eq!(b.to_string(), "ints [0..=2]\nfinite {0, 1, 2}\n");
    assert!(b.ints.proof_grade() && b.finite.proof_grade());
    // With no landmarks, the interval goes to infinity and the finite set to the top.
    assert!(store.cell_mut(&a).widen(&two, &head, &Landmarks::none()));
    let c = store.cell(&a);
    assert_eq!(c.to_string(), "ints [0..]\n");
    assert!(!c.ints.proof_grade());
    assert!(!c.finite.proof_grade());
    assert_eq!(c.premises(), BTreeSet::from([Premise::Widened(head)]));
    assert_eq!(store.cells().count(), 1);
}

/// The premises of a loop's summary after `n` iterations, as the store builds them: each
/// iteration's test `i < bound_k` narrows `i`, so its entry gains one premise, and the summary
/// joins the entry after each iteration into what it held. Every entry is shared by all later
/// ones and by the summary, so the set has about `3n` parts and about `n²/2` paths through
/// them. `keep` runs between the parts built, so a caller can place other allocations among
/// them.
fn loop_summary(addrs: &[FactAddress], keep: &mut dyn FnMut()) -> Premises {
    let (mut entry, mut summary) = (Premises::new(), Premises::new());
    for a in addrs {
        keep();
        entry.insert(Premise::Constraint(a.clone()));
        keep();
        summary.extend(&entry);
    }
    summary
}

/// A set's premises are found by the identity of its shared parts, never by where they are in
/// memory: the same summary built in three allocation orders has the same premises, the same
/// printed form and compares equal.
#[test]
fn premises_are_found_by_part_not_address() {
    let addrs: Vec<FactAddress> = (0..200).map(addr).collect();
    let plain = loop_summary(&addrs, &mut || {});
    let mut held: Vec<Vec<u64>> = Vec::new();
    let interleaved = loop_summary(&addrs, &mut || held.push(vec![0; 1 + held.len() % 7]));
    let mut big: Vec<Box<[u8]>> = (0..1000).map(|i| vec![0; 16 + i % 64].into()).collect();
    big.retain(|b| b.len() % 2 == 0);
    let shifted = loop_summary(&addrs, &mut || {});
    let expected: BTreeSet<Premise> = addrs.iter().cloned().map(Premise::Constraint).collect();
    for p in [&plain, &interleaved, &shifted] {
        assert_eq!(p.set(), expected);
        assert_eq!(format!("{p:?}"), format!("{expected:?}"));
        assert!(!p.widened());
    }
    assert!(plain == interleaved && plain == shifted);
    drop((held, big));
}

mod bench;
