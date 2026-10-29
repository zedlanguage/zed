//! The evidence record of `fold` and `fix`: part of the term, so part of its address, and
//! read by the checker, not by the evaluator.

use zed_kernel::term::build::{lit, var};
use zed_kernel::{Evidence, Family, Grade, Prim, Term, Value, eval};
use zed_tests::kernel::*;
use zedc::address::ContentAddress;
use zedc::canon::{Def, address};

/// The total of three sales, its `+` carrying the evidence `ev`.
fn sales_total(ev: &[(&str, Grade)]) -> Term {
    let sales = Value::Family(Family::of(
        [(0, 120), (1, 75), (2, 5)].map(|(k, x)| (Value::Int(k), Value::Int(x))),
    ));
    let mut t = fold(lit(sales), Term::PrimFn(Prim::Add), Some(lit(0)));
    if let Term::Fold { ev: slot, .. } = &mut t {
        *slot = ev.iter().map(|(p, g)| ((*p).into(), *g)).collect();
    }
    t
}

fn addr(body: Term) -> ContentAddress {
    let d = Def {
        name: "total".into(),
        domain: None,
        facets: vec![],
        body,
    };
    address(&d, &|_| None)
}

#[test]
fn the_evidence_is_part_of_the_address() {
    let axioms = [("associative", Grade::Axiom), ("commutative", Grade::Axiom)];
    let a = addr(sales_total(&axioms));
    // The same record built in another order is the same record.
    let reversed = [axioms[1], axioms[0]];
    assert_eq!(a, addr(sales_total(&reversed)));
    // A different grade, a missing property or no record at all is a different term.
    assert_ne!(
        a,
        addr(sales_total(&[
            ("associative", Grade::Axiom),
            ("commutative", Grade::Assumed),
        ]))
    );
    assert_ne!(a, addr(sales_total(&axioms[..1])));
    assert_ne!(a, addr(sales_total(&[])));
}

#[test]
fn the_evaluator_does_not_read_the_evidence() {
    let proved = sales_total(&[("associative", Grade::Proved)]);
    let assumed = sales_total(&[("associative", Grade::Assumed)]);
    assert_eq!(eval(&proved).unwrap(), Value::Int(200));
    assert_eq!(eval(&assumed).unwrap(), Value::Int(200));
}

#[test]
fn only_the_proof_grades_may_change_a_type_and_each_grade_prints_by_name() {
    let grades = [
        Grade::Axiom,
        Grade::CheckedExhaustive,
        Grade::Proved,
        Grade::Bounded,
        Grade::Obligated,
        Grade::Assumed,
    ];
    let proof: Vec<bool> = grades.iter().map(|g| g.is_proof_grade()).collect();
    assert_eq!(proof, [true, true, true, false, false, false]);
    assert_eq!(
        sales_total(&[]).to_string(),
        "fold({0 -> 120, 1 -> 75, 2 -> 5}, (+), identity: 0, depth: 1, ev: {})"
    );
    let mut t = sales_total(&[]);
    if let Term::Fold { ev, .. } = &mut t {
        *ev = grades
            .iter()
            .enumerate()
            .map(|(i, g)| (format!("p{i}").into(), *g))
            .collect();
    }
    assert!(t.to_string().ends_with(
        "ev: { p0: axiom, p1: checkedExhaustive, p2: proved, p3: bounded, p4: obligated, \
         p5: assumed })"
    ));
}

#[test]
fn a_fix_carries_its_evidence_into_the_address_too() {
    let reach = |ev: Evidence| Term::Fix {
        init: rc(var("start")),
        step: rc(var("next")),
        this: "this".into(),
        key: "k".into(),
        kind: zed_kernel::FixKind::Lattice {
            join: rc(Term::PrimFn(Prim::Union)),
        },
        ev,
    };
    let monotone: Evidence = [("monotone".into(), Grade::Proved)].into();
    assert_ne!(addr(reach(monotone)), addr(reach(Evidence::new())));
}
