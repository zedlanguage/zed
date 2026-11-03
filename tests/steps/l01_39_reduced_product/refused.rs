//! A disjunct whose projection is refused is left out, which leaves the hull wider but sound,
//! and its cause is returned with the hulls, so that the scope records it.

use std::sync::Arc;

use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, project_each};

fn sym(s: &str) -> Atom {
    Atom::Sym(Arc::from(s))
}

/// `Σ c·s + k >= 0`.
fn ge(terms: &[(&str, i128)], k: i128) -> Formula {
    let lin = terms.iter().fold(Lin::constant(k), |l, (s, c)| {
        l.plus(&Lin::atom(sym(s)).times(*c))
    });
    Formula::Con(Con::ge(&lin, &Lin::constant(0)))
}

/// Four constraints on four names whose integer points are not decided (the system of
/// `Refusal::Growth` in tests/steps/l01_38_presburger/omega.rs).
fn growth() -> Formula {
    Formula::and(vec![
        ge(&[("x", 4), ("w", -12), ("y", -10), ("z", -12)], 11),
        ge(&[("w", 4), ("x", 10), ("y", -10), ("z", -11)], -28),
        ge(&[("w", 11), ("x", 4), ("y", -1), ("z", 12)], -28),
        ge(&[("w", -8), ("x", -5), ("y", 12), ("z", -1)], 31),
    ])
}

#[test]
fn the_cause_of_a_refused_disjunct_is_returned() {
    let f = Formula::and(vec![
        ge(&[("v", 1)], 0),
        Formula::Or(vec![growth(), ge(&[("v", 1)], -5)]),
    ]);
    let (hulls, skipped) = project_each(&f, &[sym("v")]).expect("the base has a point");
    assert_eq!(skipped, vec![Refusal::Growth], "{hulls:?}");
    assert!(hulls[0].is_ok(), "{hulls:?}");
    // Without the refused disjunct, nothing is skipped.
    let f = Formula::and(vec![
        ge(&[("v", 1)], 0),
        Formula::Or(vec![ge(&[("v", 1)], -9), ge(&[("v", 1)], -5)]),
    ]);
    let (_, skipped) = project_each(&f, &[sym("v")]).expect("a point");
    assert!(skipped.is_empty(), "{skipped:?}");
}
