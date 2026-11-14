//! The cost of `satisfiable` and `decide` on small formulas (PRES-small-cost, PRES-small-front).

use std::sync::Arc;

use zed_tests::scaling::{self, Meter};
use zed_tests::step_helpers::l01_38_presburger::small_cost::{Inputs, defs, ladder, least};
use zedc::store::presburger::{Atom, decide, satisfiable};

#[test]
fn a_chain_of_definitions_at_a_point_costs_its_size() {
    // Each definition is decided by propagation from the one before, O(1) each, whether the
    // inputs are fixed by equations, by two rows whose bounds meet, or by two rows that leave
    // two values each, tried at their lower bounds.
    for inputs in [Inputs::Fixed, Inputs::Bounded, Inputs::Ranged] {
        let built = scaling::inputs(64, |n| defs(n as u32, inputs));
        for f in built.values() {
            let m = satisfiable(f).expect("answered").expect("a point");
            assert_eq!(m[&Atom::Sym(Arc::from("x"))], 6.into(), "{f}");
            assert_eq!(m[&Atom::Sym(Arc::from("y"))], 4.into(), "{f}");
            assert!(f.holds(&m), "{m:?} is no point of {f}");
            assert_eq!(decide(f), Ok(true), "{f}");
        }
        scaling::check_order(
            &format!("a chain of definitions at a point ({inputs:?}), its point found"),
            64,
            1,
            |n| {
                std::hint::black_box(satisfiable(&built[&n]).is_ok());
            },
        );
        scaling::check_order(
            &format!("a chain of definitions at a point ({inputs:?}), decided"),
            64,
            1,
            |n| {
                std::hint::black_box(decide(&built[&n]).is_ok());
            },
        );
    }
}

#[test]
fn a_chain_of_definitions_at_a_point_is_not_settled_by_the_whole_solver() {
    // Inputs bounded by two rows whose bounds meet are read by propagation as if fixed by
    // equations, at about the same cost (within 5% at eight definitions when measured). Inputs
    // left two values each are not a point; they took the whole solver, at about 70 times that
    // cost, until propagation tried them at their lower bounds (PRES-small-point), which costs
    // one more pass (within 5% when measured).
    let mut meter = Meter::new();
    let [fixed, bounded, ranged] =
        [Inputs::Fixed, Inputs::Bounded, Inputs::Ranged].map(|i| defs(8, i));
    assert_eq!(
        satisfiable(&fixed).expect("answered"),
        satisfiable(&bounded).expect("answered")
    );
    assert_eq!(
        satisfiable(&fixed).expect("answered"),
        satisfiable(&ranged).expect("answered")
    );
    let [fixed, bounded, ranged] = [&fixed, &bounded, &ranged]
        .map(|f| least(&mut meter, &|| drop(std::hint::black_box(satisfiable(f)))));
    let unit = meter.unit();
    assert!(
        bounded < 2 * fixed && ranged < 2 * fixed,
        "fixed {fixed} {unit}, bounded {bounded} {unit}, ranged {ranged} {unit}"
    );
}

#[test]
fn a_ladder_of_bounds_costs_its_size() {
    // Each round sets the rung bounded by the round before at its upper bound and continues
    // the same propagation from it, O(1) each, so the `n` rounds cost O(n) in all, not one
    // pass over the formula per round.
    let built = scaling::inputs(64, |n| ladder(n as u32));
    for f in built.values() {
        let m = satisfiable(f).expect("answered").expect("a point");
        assert!(f.holds(&m), "{m:?} is no point of {f}");
        assert_eq!(m[&Atom::Sym(Arc::from("x1"))], 6.into(), "{f}");
        assert_eq!(decide(f), Ok(true), "{f}");
    }
    scaling::check("a ladder of bounds, its point found", 64, |n| {
        std::hint::black_box(satisfiable(&built[&n]).is_ok());
    });
    scaling::check("a ladder of bounds, decided", 64, |n| {
        std::hint::black_box(decide(&built[&n]).is_ok());
    });
}
