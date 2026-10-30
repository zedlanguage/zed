//! The reduced product's time against the size of the test (the rule of low complexity,
//! DESIGN.md Part G): a conjunction of disjunctions narrows a scope in time near linear in
//! its length.

use std::collections::BTreeSet;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::presburger::ATOMS;

use super::ints;

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

/// `(x + y >= 0 || x - y >= 0) && (x + y >= 1 || x - y >= 1) && …`, `k` disjunctions.
fn clauses(k: usize) -> Term {
    let clause = |j: i64| {
        let sum = prim(Prim::Add, var("x"), var("y"));
        let diff = prim(Prim::Sub, var("x"), var("y"));
        prim(
            Prim::Or,
            prim(Prim::Ge, sum, int(j)),
            prim(Prim::Ge, diff, int(j)),
        )
    };
    (1..k as i64).fold(clause(0), |a, j| prim(Prim::And, a, clause(j)))
}

#[test]
fn a_scope_keeps_a_relation_within_the_budget() {
    let s = ints(&["x".into(), "y".into()]);
    for k in [1, 4, 40] {
        let r = s.assume(&clauses(k), true, &BTreeSet::new());
        let n = r.relation.cons().len();
        assert!(
            n > 0 && n <= ATOMS,
            "{k} clauses: {n} constraints in {}",
            r.relation
        );
        // Every point that meets the test is in the scope.
        for (x, y) in [(40, 0), (0, -40), (39, 0)] {
            let env = [("x".into(), Value::Int(x)), ("y".into(), Value::Int(y))].into();
            let holds = (0..k as i64).all(|j| x + y >= j || x - y >= j);
            assert!(
                !holds || r.contains(&env),
                "{k} clauses: ({x}, {y}) left out"
            );
        }
    }
}

#[test]
fn narrowing_by_a_conjunction_of_disjunctions_scales() {
    let s = ints(&["x".into(), "y".into()]);
    scaling::check("a conjunction of disjunctions of linear tests", 8, |k| {
        s.assume(&clauses(k), true, &BTreeSet::new());
    });
}
