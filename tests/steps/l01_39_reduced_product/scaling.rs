//! The reduced product's time against the size of the test (the rule of low complexity,
//! DESIGN.md Part G): a conjunction of disjunctions narrows a scope in time near linear in
//! its length.

use std::collections::BTreeMap;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::product::Scope;

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
        // Each clause's two sides once each: the relation of the whole test, taken before the
        // scope is narrowed, holds no copy of a side that a case of the split adds again.
        let n = r.relation.cons().len();
        assert!(n == 2 * k, "{k} clauses: {n} constraints in {}", r.relation);
        let mut got: Vec<String> = r.relation.cons().iter().map(|c| c.to_string()).collect();
        got.sort();
        let mut want: Vec<String> = (0..k)
            .flat_map(|j| {
                let diff = if j == 0 {
                    "x >= y".to_string()
                } else {
                    format!("x >= y + {j}")
                };
                [format!("x + y >= {j}"), diff]
            })
            .collect();
        want.sort();
        assert_eq!(got, want, "{k} clauses");
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

/// `(x1 == 0 && … && xk == 0) || (x1 == 1 && … && xk == 1)`.
fn all_zero_or_all_one(k: usize) -> Term {
    let all = |v: i64| {
        (2..=k).fold(prim(Prim::Eq, var("x1"), int(v)), |a, i| {
            prim(Prim::And, a, prim(Prim::Eq, var(&format!("x{i}")), int(v)))
        })
    };
    prim(Prim::Or, all(0), all(1))
}

#[test]
fn a_join_keeps_the_equalities_of_its_sides_and_scales() {
    let names = |k: usize| -> Vec<std::sync::Arc<str>> {
        (1..=k).map(|i| format!("x{i}").into()).collect()
    };
    for k in [2, 5, 10, 20] {
        let r = ints(&names(k)).assume(&all_zero_or_all_one(k), true, &Premises::new());
        let differ = prim(Prim::Ne, var("x1"), var(&format!("x{k}")));
        assert!(
            r.assume(&differ, true, &Premises::new()).bottom,
            "k = {k}: {}",
            r.relation
        );
        let x1 = prim(Prim::Eq, var("x1"), int(1));
        assert!(!r.assume(&x1, true, &Premises::new()).bottom, "k = {k}");
    }
    // The two sides, built before the timing; the join of the two, reduced, is timed.
    let sides = |k: usize| {
        let s = ints(&names(k));
        let Term::Prim(_, a) = all_zero_or_all_one(k) else {
            unreachable!("a disjunction")
        };
        let p = Premises::new();
        (s.assume(&a[0], true, &p), s.assume(&a[1], true, &p))
    };
    let built: BTreeMap<usize, (Scope, Scope)> =
        [32, 256].into_iter().map(|k| (k, sides(k))).collect();
    scaling::check("the join of two sides that fix k names, reduced", 32, |k| {
        let (l, r) = &built[&k];
        l.join(r).reduce();
    });
}

/// A random conjunction over `x1`..`x5`: bounds, differences and sums of two names, and
/// disjunctions of two of these, so that the blocks form chains, trees and cycles.
fn random_conjunction(rnd: &mut Rng) -> Term {
    let name = |rnd: &mut Rng| var(&format!("x{}", rnd.int(1, 5)));
    let atom = |rnd: &mut Rng| {
        let rel = rnd.pick(&[Prim::Lt, Prim::Le, Prim::Eq]);
        let (a, b) = (name(rnd), name(rnd));
        match rnd.below(3) {
            0 => prim(rel, a, int(rnd.int(-3, 3))),
            1 => prim(rel, a, prim(Prim::Add, b, int(rnd.int(-2, 2)))),
            _ => prim(rel, prim(Prim::Add, a, b), int(rnd.int(-4, 4))),
        }
    };
    let conjunct = |rnd: &mut Rng| {
        if rnd.below(3) == 0 {
            prim(Prim::Or, atom(rnd), atom(rnd))
        } else {
            atom(rnd)
        }
    };
    let n = rnd.int(2, 7);
    (1..n).fold(conjunct(rnd), |t, _| prim(Prim::And, t, conjunct(rnd)))
}

#[test]
fn projecting_by_blocks_keeps_what_projecting_whole_trees_keeps() {
    let names: Vec<std::sync::Arc<str>> = (1..=5).map(|i| format!("x{i}").into()).collect();
    let s = ints(&names);
    let mut rnd = Rng::new(39);
    let mut empty = 0;
    for _ in 0..zed_tests::instances::RANDOM_INSTANCES {
        let t = random_conjunction(&mut rnd);
        let a = s.assume(&t, true, &Premises::new());
        let (mut blocks, mut whole) = (a.clone(), a);
        blocks.reduce();
        whole.reduce_whole();
        assert_eq!(blocks.bottom, whole.bottom, "{t:?}");
        if blocks.bottom {
            empty += 1;
            continue;
        }
        for x in &names {
            assert_eq!(blocks.get(x), whole.get(x), "{x} in {t:?}");
        }
    }
    // Both kinds of case occur.
    assert!(
        0 < empty && empty < zed_tests::instances::RANDOM_INSTANCES,
        "{empty} empty"
    );
}

#[test]
fn a_cycle_of_strict_orders_is_empty() {
    // x < y and y < x: each bound raises the other without end unless the cycle is seen.
    let s = ints(&["x".into(), "y".into()]);
    let t = prim(
        Prim::And,
        prim(Prim::Lt, var("x"), var("y")),
        prim(Prim::Lt, var("y"), var("x")),
    );
    let mut a = s.assume(&t, true, &Premises::new());
    a.reduce();
    assert!(a.bottom, "{a}");
}

#[test]
fn an_even_number_that_is_odd_is_empty() {
    // c == 2a, c == 2b + 1, c >= 0: no bound is ever tight, only the parity is.
    let s = ints(&["a".into(), "b".into(), "c".into()]);
    let two = |x: &str| prim(Prim::Mul, int(2), var(x));
    let t = prim(
        Prim::And,
        prim(
            Prim::And,
            prim(Prim::Eq, var("c"), two("a")),
            prim(Prim::Eq, var("c"), prim(Prim::Add, two("b"), int(1))),
        ),
        prim(Prim::Le, int(0), var("c")),
    );
    let mut a = s.assume(&t, true, &Premises::new());
    a.reduce();
    assert!(a.bottom, "{a}");
}

/// `let h = (y) -> 2 * y + 1 in if h(x) >= k { k } else if h(x) >= k - 1 { k - 1 } … else { 0 }`:
/// an `else if` chain of `k` tests, each read through the function it calls.
fn helper_chain(k: usize) -> Term {
    let call = || Term::App(arc(var("h")), vec![var("x")]);
    let chain = (1..=k).fold(int(0), |t, i| {
        Term::If(
            arc(prim(Prim::Ge, call(), int(i as i64))),
            arc(int(i as i64)),
            arc(t),
        )
    });
    let h = Term::Lam(
        vec!["y".into()],
        arc(prim(Prim::Add, prim(Prim::Mul, int(2), var("y")), int(1))),
    );
    Term::Let("h".into(), arc(h), arc(chain))
}

/// `let h0 = (y) -> y + 1 in let h1 = (y) -> h0(y) + 1 in let h2 = (y) -> h1(y) + h0(y) in …
/// if hk(x) >= 0 { 1 } else { 2 }`: one test read through `k + 1` functions, each calling the
/// two before it, so a function is reached along many paths.
fn nested_helpers(k: usize) -> Term {
    let name = |i: usize| -> std::sync::Arc<str> { format!("h{i}").into() };
    let call = |f: std::sync::Arc<str>, a: Term| Term::App(arc(Term::Var(f)), vec![a]);
    let mut t = Term::If(
        arc(prim(Prim::Ge, call(name(k), var("x")), int(0))),
        arc(int(1)),
        arc(int(2)),
    );
    for i in (0..=k).rev() {
        let body = match i {
            0 => prim(Prim::Add, var("y"), int(1)),
            1 => prim(Prim::Add, call(name(0), var("y")), int(1)),
            _ => prim(
                Prim::Add,
                call(name(i - 1), var("y")),
                call(name(i - 2), var("y")),
            ),
        };
        let f = Term::Lam(vec!["y".into()], arc(body));
        t = Term::Let(name(i), arc(f), arc(t));
    }
    t
}

#[test]
fn tests_read_through_the_functions_they_call_scale() {
    let x = ints(&["x".into()]);
    // `h(x) >= 4` and below it `h(x) < 4`, `h(x) >= 3`: the test of 3 is reached where
    // `2x + 1` is 3, that of 2 never, since `2x + 1` is odd.
    let a = super::arms(&helper_chain(4), &x);
    let reach: Vec<bool> = a.iter().map(|a| a.reachable()).collect();
    assert_eq!(
        reach,
        [true, true, true, true, false, true, true, true],
        "{a:#?}"
    );
    // `h5(x)` is `8x + 13`, so the true arm holds `x >= -1`.
    let a = super::arms(&nested_helpers(5), &x);
    assert_eq!(a[0].scope.get("x").ints().to_string(), "[-1..]");
    assert_eq!(a[1].scope.get("x").ints().to_string(), "[..=-2]");
    // The terms, built before the timing; walking their arms is timed. Each test closes over
    // the functions it reaches, each once however many paths reach it, so both are linear.
    let chains: BTreeMap<usize, Term> = [64, 512]
        .into_iter()
        .map(|k| (k, helper_chain(k)))
        .collect();
    scaling::check_order(
        "an `else if` chain of k tests, each calling a function",
        64,
        1,
        |k| {
            super::arms(&chains[&k], &x);
        },
    );
    // The preimage still recurses on the depth of the term (item T2-mid), so the chain stays
    // within what a test thread's stack holds.
    let nests: BTreeMap<usize, Term> = [32, 256]
        .into_iter()
        .map(|k| (k, nested_helpers(k)))
        .collect();
    scaling::check_order(
        "one test through k functions, each calling the two before it",
        32,
        1,
        |k| {
            super::arms(&nests[&k], &x);
        },
    );
}
