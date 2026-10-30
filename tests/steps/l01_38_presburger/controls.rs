//! The budgets of step M0.5, and controls: each check of `random` rejects a wrong answer.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc::store::interval::IntervalSet;
use zedc::store::preimage::{Demand, preimage, relations};
use zedc::store::presburger::{
    ATOMS, Atom, Con, Entailment, Formula, Lin, Model, Relation, VARIABLES, entails, satisfiable,
};

use super::random::{check_entailment, check_model, check_points, check_projection};

fn lit(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn x() -> Term {
    Term::Var("x".into())
}

fn names() -> Vec<Arc<str>> {
    vec!["x".into(), "y".into()]
}

/// `x < 3`.
fn below_three() -> Term {
    Term::Prim(Prim::Lt, vec![x(), lit(3)])
}

#[test]
fn a_relation_past_the_budget_is_dropped_and_the_written_constraint_kept() {
    // One atom past the budget: the sum of 17 symbols.
    let sum = Formula::Con(Con {
        lin: (0..=VARIABLES).fold(Lin::constant(-50), |l, i| {
            l.plus(&Lin::atom(Atom::Sym(format!("a{i}").into())))
                .unwrap()
        }),
        rel: zedc::store::presburger::Rel::Ge,
    });
    assert!(satisfiable(&sum).is_err());
    let r = Relation::of(sum.clone());
    assert_eq!(entails(&r, &r), Entailment::Dropped);
    assert_eq!(
        entails(&r, &r).to_string(),
        "dropped: past the budget of step M0.5"
    );
    // One constraint past the budget, over one symbol.
    let many = Formula::and(
        (0..=ATOMS as i128)
            .map(|k| {
                Formula::Con(Con::ge(&Lin::atom(Atom::Sym("x".into())), &Lin::constant(k)).unwrap())
            })
            .collect(),
    );
    assert!(satisfiable(&many).is_err());
    // The preimage of a sum of 17 inputs keeps the catalog's box, sound, with no relation.
    let inputs: Vec<Arc<str>> = (0..=VARIABLES).map(|i| format!("a{i}").into()).collect();
    let total = inputs
        .iter()
        .map(|n| Term::Var(n.clone()))
        .reduce(|a, b| Term::Prim(Prim::Add, vec![a, b]))
        .unwrap();
    let t = Term::Prim(Prim::Lt, vec![total, lit(50)]);
    let doms = inputs
        .iter()
        .map(|n| (n.clone(), IntervalSet::of(0, 1000)))
        .collect();
    let p = preimage(&t, &doms, &Demand::Bool(true));
    assert!(p.relation.is_none() && !p.exact);
    assert!(
        p.domains.values().all(|d| *d == IntervalSet::of(0, 49)),
        "{:?}",
        p.domains
    );
}

#[test]
fn each_check_rejects_a_wrong_answer() {
    let ns = names();
    let t = below_three();
    let rs = relations(&[&t], &ns, false).unwrap();
    check_points(&rs[0], &t, &ns).unwrap();
    // The relation of `x < 4` in its place.
    let wrong = relations(&[&Term::Prim(Prim::Lt, vec![x(), lit(4)])], &ns, false).unwrap();
    assert!(check_points(&wrong[0], &t, &ns).is_err());
    // A model outside the test, and no model where there is one.
    assert!(check_model(Some(vec![3, 0]), &t, &ns).is_err());
    assert!(check_model(None, &t, &ns).is_err());
    check_model(Some(vec![2, 0]), &t, &ns).unwrap();
    // A projection one short, and one past the hull.
    let right = [IntervalSet::of(-5, 2), IntervalSet::of(-5, 5)];
    check_projection(&right, &t, &ns).unwrap();
    assert!(check_projection(&[IntervalSet::of(-5, 1), right[1].clone()], &t, &ns).is_err());
    assert!(check_projection(&[IntervalSet::of(-5, 3), right[1].clone()], &t, &ns).is_err());
    // A proof the window refutes, and a countermodel that is none.
    let g = Term::Prim(Prim::Lt, vec![x(), lit(2)]);
    assert!(check_entailment(&Entailment::Proved(Vec::new()), &t, &g, &ns).is_err());
    let at = |v: i128| -> Model { [(Atom::Sym("x".into()), v)].into() };
    assert!(check_entailment(&Entailment::Refuted(at(0)), &t, &g, &ns).is_err());
    check_entailment(&Entailment::Refuted(at(2)), &t, &g, &ns).unwrap();
}
