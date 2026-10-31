//! The reduced product's time against the size of the test (the rule of low complexity,
//! DESIGN.md Part G): a conjunction of disjunctions narrows a scope in time near linear in
//! its length.

use zedc::store::cell::Premises;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;

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
fn a_scope_keeps_every_clause_of_a_relation() {
    let s = ints(&["x".into(), "y".into()]);
    for k in [1, 4, 40] {
        let r = s.assume(&clauses(k), true, &Premises::new());
        let n = r.relation.cons().len();
        assert!(n == 3 * k, "{k} clauses: {n} constraints in {}", r.relation);
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
        s.assume(&clauses(k), true, &Premises::new());
    });
}

fn arc(t: Term) -> std::sync::Arc<Term> {
    std::sync::Arc::new(t)
}

/// `let x1 = x0 + 1 in … let xk = x(k-1) + 1 in if xk >= 0 { 1 } else { 2 }`.
fn lets(k: usize) -> Term {
    let last = format!("x{k}");
    let mut t = Term::If(
        arc(prim(Prim::Ge, var(&last), int(0))),
        arc(int(1)),
        arc(int(2)),
    );
    for i in (1..=k).rev() {
        let prev = format!("x{}", i - 1);
        t = Term::Let(
            format!("x{i}").into(),
            arc(prim(Prim::Add, var(&prev), int(1))),
            arc(t),
        );
    }
    t
}

/// `if x0 >= 0 { if x0 >= 1 { … } else { 0 } } else { 0 }`, `k` deep.
fn ifs(k: usize) -> Term {
    (0..k).rev().fold(int(1), |t, i| {
        Term::If(
            arc(prim(Prim::Ge, var("x0"), int(i as i64))),
            arc(t),
            arc(int(0)),
        )
    })
}

#[test]
fn a_chain_of_lets_and_a_nest_of_ifs_scale() {
    let x0 = ints(&["x0".into()]);
    scaling::check("a chain of `let`s", 50, |k| {
        super::arms(&lets(k), &x0);
    });
    // Each level's test implies the one before, so the relation keeps one constraint.
    scaling::check("`if`s nested on one name", 64, |k| {
        super::arms(&ifs(k), &x0);
    });
}

/// `if x >= 0 { let x = x - 100 in if x >= 0 { 1 } else { 2 } } else { 3 }`: the inner `x`
/// is the outer one less 100, so the inner false arm is reached at `x = -100`. What held of
/// the outer `x` does not hold of the inner one.
#[test]
fn a_binding_forgets_what_held_of_the_name_it_shadows() {
    let test = || prim(Prim::Ge, var("x"), int(0));
    let inner = Term::If(arc(test()), arc(int(1)), arc(int(2)));
    let body = Term::Let(
        "x".into(),
        arc(prim(Prim::Sub, var("x"), int(100))),
        arc(inner),
    );
    let t = Term::If(arc(test()), arc(body), arc(int(3)));
    let a = super::arms(&t, &ints(&["x".into()]));
    let shown: Vec<String> = a
        .iter()
        .map(|a| format!("{} {}: {}", a.guard, a.outcome, a.scope))
        .collect();
    assert_eq!(a.len(), 4, "{shown:#?}");
    let reached = &a[2];
    assert!(!reached.outcome, "{shown:#?}");
    assert!(!reached.scope.bottom, "{shown:#?}");
    let at = std::collections::BTreeMap::from([("x".into(), zed_kernel::Value::Int(-100))]);
    assert!(reached.scope.contains(&at), "{shown:#?}");
}
