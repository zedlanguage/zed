//! The reduced product's time against the size of the test (the rule of low complexity,
//! DESIGN.md Part G): a conjunction of disjunctions narrows a scope in time near linear in
//! its length.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::images::{self, TermRead};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Demand, Domains, LetIn, Lets, let_narrowing, let_summary};
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
        // The two sides of the last clause once each: the relation of the whole test, taken
        // before the scope is narrowed, holds no copy of a side that a case of the split adds
        // again, and no clause that a stronger one on the same two sides implies (clause `j`
        // follows from clause `k - 1`).
        let n = r.relation.cons().len();
        assert!(n == 2, "{k} clauses: {n} constraints in {}", r.relation);
        let mut got: Vec<String> = r.relation.cons().iter().map(|c| c.to_string()).collect();
        got.sort();
        let j = k - 1;
        let diff = if j == 0 {
            "x >= y".to_string()
        } else {
            format!("x >= y + {j}")
        };
        let mut want = vec![format!("x + y >= {j}"), diff];
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

fn arc(t: Term) -> zed_kernel::Shared {
    zed_kernel::Shared::new(t)
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
        let Term::Prim(_, a) = &all_zero_or_all_one(k) else {
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
    // The preimage still recurses on the depth of the term (item T2-mid), about 4 KB a level
    // here, so the nest runs on a stack of its own: at 256 levels it needs about as much as a
    // test thread holds (2 MiB).
    let nests: BTreeMap<usize, Term> = [32, 256]
        .into_iter()
        .map(|k| (k, nested_helpers(k)))
        .collect();
    on_big_stack(|| {
        scaling::check_order(
            "one test through k functions, each calling the two before it",
            32,
            1,
            |k| {
                super::arms(&nests[&k], &x);
            },
        )
    });
}

/// Runs `f` on a thread with a stack deep enough for the nests above (item T2-mid).
fn on_big_stack<R: Send>(f: impl FnOnce() -> R + Send) -> R {
    std::thread::scope(|s| {
        let thread = std::thread::Builder::new().stack_size(1 << 28);
        thread.spawn_scoped(s, f).unwrap().join().unwrap()
    })
}

/// `xi - yi >= 1`, or with `or` the test `xi - yi >= 1 || yi - xi >= 1`, for `i` below `k`:
/// tests on names that no other test mentions.
fn apart(k: usize, or: bool) -> (Vec<std::sync::Arc<str>>, Vec<Term>) {
    let ge = |a: &str, b: &str| prim(Prim::Ge, prim(Prim::Sub, var(a), var(b)), int(1));
    let mut names = Vec::new();
    let mut tests = Vec::new();
    for i in 0..k {
        let (x, y) = (format!("x{i}"), format!("y{i}"));
        tests.push(if or {
            prim(Prim::Or, ge(&x, &y), ge(&y, &x))
        } else {
            ge(&x, &y)
        });
        names.push(x.into());
        names.push(y.into());
    }
    (names, tests)
}

#[test]
fn tests_on_names_apart_narrow_in_time_near_their_number() {
    // A test projects the names it is linked to, not the whole relation: the scope, the
    // conjunction and the list of tests are built before the timing.
    let conjunction = |k: usize, or: bool| {
        let (names, tests) = apart(k, or);
        let all = tests
            .into_iter()
            .reduce(|a, t| prim(Prim::And, a, t))
            .expect("k > 0");
        (ints(&names), all)
    };
    let sizes = [50, 400];
    for or in [false, true] {
        let built: BTreeMap<usize, (Scope, Term)> =
            sizes.into_iter().map(|k| (k, conjunction(k, or))).collect();
        let what = if or {
            "a conjunction of k disjunctions on names apart"
        } else {
            "a conjunction of k tests on names apart"
        };
        scaling::check(what, 50, |k| {
            let (s, t) = &built[&k];
            s.assume(t, true, &Premises::new());
        });
    }
    let one_by_one: BTreeMap<usize, (Scope, Vec<Term>)> = sizes
        .into_iter()
        .map(|k| {
            let (names, tests) = apart(k, true);
            (k, (ints(&names), tests))
        })
        .collect();
    scaling::check(
        "k disjunctions on names apart, assumed one by one",
        50,
        |k| {
            let (s, tests) = &one_by_one[&k];
            let p = Premises::new();
            tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
        },
    );
    // What each kind keeps: every test of the conjunction, and each point that meets them.
    let (s, t) = conjunction(3, true);
    let r = s.assume(&t, true, &Premises::new());
    assert_eq!(r.relation.cons().len(), 6, "{}", r.relation);
    let at = |v: [i64; 6]| -> BTreeMap<std::sync::Arc<str>, Value> {
        ["x0", "y0", "x1", "y1", "x2", "y2"]
            .into_iter()
            .zip(v)
            .map(|(n, v)| (n.into(), Value::Int(v)))
            .collect()
    };
    assert!(r.contains(&at([1, 0, 0, 1, 5, -5])));
    let (s, tests) = &one_by_one[&50];
    let p = Premises::new();
    let r = tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
    assert!(!r.bottom);
    let (s, t) = conjunction(3, false);
    let r = s.assume(&t, true, &Premises::new());
    assert!(r.contains(&at([1, 0, 1, 0, 9, 8])));
    assert!(!r.contains(&at([0, 0, 1, 0, 9, 8])));
}

/// `let x1 = x0 in let x1 = x1 + 1 in … let xk = x0 in let xk = xk + 1 in if xk >= 1 { 1 }
/// else { 2 }`: each name is bound and then shadowed, so every second binding saves the
/// scope, which then holds up to `k` names.
fn shadows(k: usize) -> Term {
    let last = format!("x{k}");
    let mut t = Term::If(
        arc(prim(Prim::Ge, var(&last), int(1))),
        arc(int(1)),
        arc(int(2)),
    );
    for i in (1..=k).rev() {
        let x = format!("x{i}");
        t = Term::Let(
            x.as_str().into(),
            arc(var("x0")),
            arc(Term::Let(
                x.as_str().into(),
                arc(prim(Prim::Add, var(&x), int(1))),
                arc(t),
            )),
        );
    }
    t
}

/// `if x >= 0 { let x = x + 1 in let x = x + 1 in if x >= 2 { 1 } else { 2 } } else { 3 }`:
/// each binding reads the `x` it shadows, so the innermost `x` is at least 2 and the inner
/// false arm is never reached.
#[test]
fn a_binding_that_reads_the_name_it_shadows_keeps_what_held_of_it() {
    let inner = Term::If(
        arc(prim(Prim::Ge, var("x"), int(2))),
        arc(int(1)),
        arc(int(2)),
    );
    let step = |body: Term| {
        Term::Let(
            "x".into(),
            arc(prim(Prim::Add, var("x"), int(1))),
            arc(body),
        )
    };
    let t = Term::If(
        arc(prim(Prim::Ge, var("x"), int(0))),
        arc(step(step(inner))),
        arc(int(3)),
    );
    let a = super::arms(&t, &ints(&["x".into()]));
    let shown: Vec<String> = a
        .iter()
        .map(|a| format!("{} {}: {}", a.guard, a.outcome, a.scope))
        .collect();
    assert_eq!(a.len(), 4, "{shown:#?}");
    assert!(a[1].outcome && !a[1].scope.bottom, "{shown:#?}");
    assert!(!a[2].outcome && a[2].scope.bottom, "{shown:#?}");
}

#[test]
fn a_chain_of_shadowing_lets_scales() {
    // `arms` recurses on the depth of the term (T2-mid), so the chain runs on a thread whose
    // stack holds it: 1,600 `let`s at the larger size.
    let t = std::thread::Builder::new().stack_size(1 << 28).spawn(|| {
        let x0 = ints(&["x0".into()]);
        let terms: BTreeMap<usize, Term> = [100, scaling::FACTOR * 100]
            .into_iter()
            .map(|k| (k, shadows(k)))
            .collect();
        let a = super::arms(&terms[&100], &x0);
        assert_eq!(a.len(), 2, "both arms of the last test are reached");
        assert!(a.iter().all(|a| !a.scope.bottom));
        scaling::check("a chain of shadowing `let`s", 100, |k| {
            super::arms(&terms[&k], &x0);
        });
    });
    t.expect("a thread").join().expect("the chain scales");
}

/// `n{i}`.
fn n(i: usize) -> String {
    format!("n{i}")
}

/// `a * b mod 10 == r`.
fn ends_in(a: &str, b: &str, r: i64) -> Term {
    let ab = prim(Prim::Mul, var(a), var(b));
    prim(Prim::Eq, prim(Prim::Mod, ab, int(10)), int(r))
}

/// The scope under `@exact` of the integers `n0` to `n{k - 1}`, each within `0..=30`.
fn exact_within(k: usize) -> Scope {
    let names: Vec<std::sync::Arc<str>> = (0..k).map(|i| n(i).into()).collect();
    let int_ty = || zedc::store::product::Product::of_type(zed_kernel::types::Type::int());
    let mut s = Scope::exact(names.iter().map(|x| (x.clone(), int_ty())));
    let p = Premises::new();
    for x in &names {
        let from = prim(Prim::Ge, var(x), int(0));
        let to = prim(Prim::Le, var(x), int(30));
        s = s.assume(&prim(Prim::And, from, to), true, &p);
    }
    s
}

/// `scope` with each of `written` written and the scope reduced after each, as a body's
/// constraints are met one by one.
fn reduced_one_by_one(scope: &Scope, written: &[Term]) -> Scope {
    let mut s = scope.clone();
    for c in written {
        s.write(c.clone());
        s.reduce();
    }
    s
}

/// `n{i} * n{i} mod 10 == 9` for `i` below `k`: constraints on names apart.
fn squares_apart(k: usize) -> Vec<Term> {
    (0..k).map(|i| ends_in(&n(i), &n(i), 9)).collect()
}

/// `n{i} * n{i + 1} mod 10 == 1` for `i` below `k`: one group of constraints, linked in a chain.
fn products_in_a_chain(k: usize) -> Vec<Term> {
    (0..k).map(|i| ends_in(&n(i), &n(i + 1), 1)).collect()
}

/// What a scaling test calls a family of constraints, and its constraints by their count.
type Family = (&'static str, fn(usize) -> Vec<Term>);

#[test]
fn many_reductions_under_exact_scale() {
    // An `@exact` scope reduced after each of k written constraints: a reduction searches only
    // the constraints written since the last one and those on names that changed, and a point
    // kept from an earlier search that the new constraint extends is not searched again, so
    // the k reductions cost about k, for constraints on names apart and for one group linked
    // in a chain. The scopes and constraints are built before the timing.
    let families: [Family; 2] = [
        (
            "k reductions under @exact, each after a constraint on names apart",
            squares_apart,
        ),
        (
            "k reductions under @exact, each after a constraint of one chain",
            products_in_a_chain,
        ),
    ];
    for (what, family) in families {
        let built = scaling::inputs(32, |k| (exact_within(k + 1), family(k)));
        scaling::check(what, 32, |k| {
            let (s, cs) = &built[&k];
            assert!(!reduced_one_by_one(s, cs).bottom);
        });
    }
}

/// `x0 >= 0`, `x1 >= 1`, … `x{k-1} >= k - 1` holding one after another, and at each the test
/// `xi < i` that fails there: what a checker reading a nest of `k` tests on `k` names meets
/// when one case of each test is unreachable.
#[test]
fn a_failing_case_costs_its_test_and_not_the_names_in_scope() {
    let ge = |i: usize| prim(Prim::Ge, var(&format!("x{i}")), int(i as i64));
    let lt = |i: usize| prim(Prim::Lt, var(&format!("x{i}")), int(i as i64));
    let names =
        |k: usize| -> Vec<std::sync::Arc<str>> { (0..k).map(|i| format!("x{i}").into()).collect() };
    let built: BTreeMap<usize, (Scope, Vec<(Term, Term)>)> = [300, 2400]
        .into_iter()
        .map(|k| {
            (
                k,
                (ints(&names(k)), (0..k).map(|i| (ge(i), lt(i))).collect()),
            )
        })
        .collect();
    let p = Premises::new();
    let nest = |s: &Scope, tests: &[(Term, Term)]| {
        let mut failed = Vec::with_capacity(tests.len());
        let s = tests.iter().fold(s.clone(), |s, (holds, fails)| {
            failed.push(
                s.assume_case(holds, false, &p)
                    .assume_case(fails, false, &p),
            );
            s.assume_case(holds, true, &p)
        });
        (s, failed)
    };
    // Each failing case is unreachable, and every name reads as empty there, its own and the
    // others, though the case kept them as they were.
    let (s, tests) = &built[&300];
    let (last, failed) = nest(s, tests);
    assert!(!last.bottom);
    assert_eq!(last.get("x7").ints().to_string(), "[7..]");
    for (i, f) in failed.iter().enumerate() {
        assert!(f.bottom, "case {i}");
        assert!(f.get(&format!("x{i}")).is_empty(), "x{i} in case {i}");
        assert!(f.get("x0").is_empty() && f.get("y").is_empty(), "case {i}");
    }
    // Emptying each name of a failing case costs the names in scope: O(k²) for the nest.
    scaling::check(
        "a nest of k tests on k names, each failing in one case",
        300,
        |k| {
            let (s, tests) = &built[&k];
            nest(s, tests);
        },
    );
}

/// An eager scope of `n`, `m` and `a0`..`a(k-1)` under `n >= -1 && m >= -1` and `k` tests
/// `ai >= n && ai >= m`: `k` stars of the two hubs, each leaf `int[-1..]`.
fn stars_of_two_hubs(k: usize) -> Scope {
    let mut all: Vec<std::sync::Arc<str>> = vec!["n".into(), "m".into()];
    all.extend((0..k).map(|i| format!("a{i}").into()));
    let p = Premises::new();
    let bounds = prim(
        Prim::And,
        prim(Prim::Ge, var("n"), int(-1)),
        prim(Prim::Ge, var("m"), int(-1)),
    );
    (0..k).fold(ints(&all).assume(&bounds, true, &p), |s, i| {
        let a = format!("a{i}");
        let star = prim(
            Prim::And,
            prim(Prim::Ge, var(&a), var("n")),
            prim(Prim::Ge, var(&a), var("m")),
        );
        s.assume(&star, true, &p)
    })
}

/// `n - m <= c`, a test among the hubs of the stars of [`stars_of_two_hubs`].
fn hubs_within(c: i64) -> Term {
    prim(Prim::Le, prim(Prim::Sub, var("n"), var("m")), int(c))
}

#[test]
fn tests_among_the_hubs_of_many_stars_narrow_an_eager_scope_in_linear_time() {
    // `k` tests `n - m <= k`, …, `n - m <= 1` under the `k` stars: each replaces the one
    // before as the tighter (`Conjuncts::tight`), so each removes a conjunct among the hubs
    // and adds one, and neither moves a leaf, since `n = m = -1` meets them all. Each
    // projected every star again: `k` projections per test, 57.4 times the bytes for 8 times
    // the size (item NARROW-eager-scope). The stars of one class, the same conjuncts but for
    // the leaf, are now projected again only when the class's bound on its leaf changes
    // (`Scope::same_leaf_bound`).
    let p = Premises::new();
    let built: BTreeMap<usize, Scope> = [16, 128]
        .into_iter()
        .map(|k| (k, stars_of_two_hubs(k)))
        .collect();
    let narrow = |k: usize| {
        (1..=k as i64).rev().fold(built[&k].clone(), |s, c| {
            s.assume(&hubs_within(c), true, &p)
        })
    };
    let s = narrow(16);
    for i in 0..16 {
        assert_eq!(s.get(&format!("a{i}")).ints().to_string(), "[-1..]", "a{i}");
    }
    // A test that moves every leaf still reaches each: `n + m >= 4` with `n - m <= 1` puts
    // the least `max(n, m)` at 2.
    let up = prim(Prim::Ge, prim(Prim::Add, var("n"), var("m")), int(4));
    let s = s.assume(&up, true, &p);
    for i in 0..16 {
        assert_eq!(s.get(&format!("a{i}")).ints().to_string(), "[2..]", "a{i}");
    }
    scaling::check(
        "k tests among the hubs of k stars of two hubs, in an eager scope",
        16,
        |k| {
            narrow(k);
        },
    );
}

/// The tests of [`a_lazy_scope_settles_the_hubs_of_a_class_of_stars_in_linear_time`] at size
/// `k`: `n + m >= 1 || n - m >= 30`, then `k` stars `ai >= n + m - i`, then `k` tests
/// `n >= m - (k - i)` among the hubs, each stronger than the last.
fn a_class_of_stars(k: usize) -> (Scope, Vec<Term>) {
    let sum = || prim(Prim::Add, var("n"), var("m"));
    let diff = || prim(Prim::Sub, var("n"), var("m"));
    let mut tests = vec![prim(
        Prim::Or,
        prim(Prim::Ge, sum(), int(1)),
        prim(Prim::Ge, diff(), int(30)),
    )];
    let star = |i: usize| {
        let leaf = var(&format!("a{i}"));
        prim(Prim::Ge, leaf, prim(Prim::Sub, sum(), int(i as i64)))
    };
    let hub = |i: usize| {
        let bound = prim(Prim::Sub, var("m"), int((k - i) as i64));
        prim(Prim::Ge, var("n"), bound)
    };
    tests.extend((0..k).map(star));
    tests.extend((0..k).map(hub));
    let names: Vec<Arc<str>> = ["n", "m"]
        .into_iter()
        .map(Arc::from)
        .chain((0..k).map(|i| Arc::from(format!("a{i}"))))
        .collect();
    (ints(&names), tests)
}

#[test]
fn a_lazy_scope_settles_the_hubs_of_a_class_of_stars_in_linear_time() {
    // `k` stars on the hubs `n` and `m`, a disjunction on both, then `k` tests among the hubs.
    // Each star is a class of its own, its constant differing, and each test changes the
    // conjuncts among the hubs of all `k` classes. The lazy scope projects no star for them:
    // a star moves no hub that the hubs' own block does not, so the leaves stay stale until
    // read (item NARROW-lazy-settle). Projecting one star of each class, `k` projections per
    // test, took 73.3 times the bytes for 8 times the size (negative control, not committed).
    let inputs = scaling::inputs(16, |k| {
        let (start, tests) = a_class_of_stars(k);
        (start.lazy(), tests)
    });
    scaling::check(
        "k tests among the hubs of a class of k stars, lazy",
        16,
        |k| {
            let (start, tests) = &inputs[&k];
            let p = Premises::new();
            tests
                .iter()
                .fold(start.clone(), |s, t| s.assume(t, true, &p));
        },
    );
}

/// The tests of [`a_lazy_scope_with_many_disjunctions_among_the_hubs_of_a_star_scales`] at
/// size `k`: the star `a >= x + y`, then `k` tests `x + y >= j || x - y >= j` among its hubs.
fn disjunctions_among_the_hubs_of_a_star(k: usize) -> (Scope, Vec<Term>) {
    let sum = || prim(Prim::Add, var("x"), var("y"));
    let diff = || prim(Prim::Sub, var("x"), var("y"));
    let mut tests = vec![prim(Prim::Ge, var("a"), sum())];
    tests.extend((0..k as i64).map(|j| {
        prim(
            Prim::Or,
            prim(Prim::Ge, sum(), int(j)),
            prim(Prim::Ge, diff(), int(j)),
        )
    }));
    let names: Vec<Arc<str>> = ["a", "x", "y"].into_iter().map(Arc::from).collect();
    (ints(&names), tests)
}

/// Assumes the tests of [`disjunctions_among_the_hubs_of_a_star`] at size `k`, in a lazy scope
/// with `lazy`, under [`scaling::check`].
fn disjunctions_scale(what: &str, lazy: bool) {
    let inputs = scaling::inputs(16, |k| {
        let (start, tests) = disjunctions_among_the_hubs_of_a_star(k);
        (if lazy { start.lazy() } else { start }, tests)
    });
    scaling::check(what, 16, |k| {
        let (start, tests) = &inputs[&k];
        let p = Premises::new();
        tests
            .iter()
            .fold(start.clone(), |s, t| s.assume(t, true, &p));
    });
}

#[test]
#[ignore = "PRODUCT-lin-rows: 17.6 times the work at 16 and 128 disjunctions, over the n log n limit 15.4 since SCALE-ratio; open"]
fn a_lazy_scope_with_many_disjunctions_among_the_hubs_of_a_star_scales() {
    // A lazy scope projects the star for none of them: each test costs its own part in the
    // hubs' block (item NARROW-lazy-settle). Projecting one star of each set of hubs for each
    // test took 25.4 times the instructions (negative control, not committed).
    disjunctions_scale("k disjunctions among the hubs of a star, lazy", true);
}

#[test]
fn an_eager_scope_with_many_disjunctions_among_the_hubs_of_a_star_scales() {
    // Each test `x + y >= j || x - y >= j` implies the ones before it, which the relation
    // drops (`Conjuncts::pair`), so the star's block holds one disjunction at each test and
    // its pass over its parts costs O(1). Before item ST-B4 every disjunction stayed, and
    // that pass, `Block::of`, the due check and the snapshot of every part, ran over all `k`
    // parts at each test: 25.0 to 26.4 times the instructions for 8 times the size
    // (COMPLEXITY.md C26; META4 O6).
    disjunctions_scale("k disjunctions among the hubs of a star, eager", false);
}

/// The scope of `a` and `b` within `0..=100000`, with `a + b <= 150000` and the disjunction
/// `a < 3 || b > 7`, and the `k` tests of [`changes_of_one_block_hold_bounded_memory`]: each
/// tightens `a - b <= c`, and every fourth is followed by an `if a + 2 * b == c` whose arms
/// are joined, its first arm with one more equality in the block.
fn changes_of_one_block(k: usize) -> (Scope, Vec<(Term, bool)>) {
    let p = Premises::new();
    let (a, b) = (|| var("a"), || var("b"));
    let s = ["a", "b"]
        .iter()
        .fold(ints(&["a".into(), "b".into()]), |s: Scope, n| {
            s.assume(&prim(Prim::Ge, var(n), int(0)), true, &p).assume(
                &prim(Prim::Le, var(n), int(100_000)),
                true,
                &p,
            )
        });
    let s = s
        .assume(
            &prim(Prim::Le, prim(Prim::Add, a(), b()), int(150_000)),
            true,
            &p,
        )
        .assume(
            &prim(
                Prim::Or,
                prim(Prim::Lt, a(), int(3)),
                prim(Prim::Gt, b(), int(7)),
            ),
            true,
            &p,
        );
    let mut tests = Vec::new();
    for i in 0..k as i64 {
        let diff = prim(Prim::Sub, a(), b());
        tests.push((prim(Prim::Le, diff, int(100_000 - i)), false));
        if i % 4 == 0 {
            let sum = prim(Prim::Add, a(), prim(Prim::Mul, int(2), b()));
            tests.push((prim(Prim::Eq, sum, int(1000 + i)), true));
        }
    }
    (s, tests)
}

/// Assumes each test of [`changes_of_one_block`] on `s`, joining both arms of those marked.
fn change_one_block(s: &Scope, tests: &[(Term, bool)]) -> Scope {
    let p = Premises::new();
    tests.iter().fold(s.clone(), |s, (t, joined)| {
        if *joined {
            let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            j.reduce();
            j
        } else {
            s.assume(t, true, &p)
        }
    })
}

#[test]
fn changes_of_one_block_hold_bounded_memory() {
    // A part's last projection is kept by the part, with what it was projected with beside
    // it (`PartKey`, `PartWith`): each tightening changes the constraints the block's own part
    // is projected with, and each equality those of the disjunction's part, and the scope
    // keeps one entry for each part. Keyed by what they were projected with, the entries grew
    // by one with each change while the conjuncts stayed three: 42 then 322 entries, holding
    // 103536 then 813712 bytes, at k = 40 then 320 (negative control, not committed; item
    // ST-projected-stale). The bytes the whole scope leaves allocated still grow, by the
    // nodes of the union-find of `Blocks`, one for each change (item ST-blocks-stale).
    let n = 40;
    let inputs = scaling::inputs(n, changes_of_one_block);
    let (mut entries, mut held) = (Vec::new(), Vec::new());
    for k in [n, scaling::FACTOR * n] {
        let (s, tests) = &inputs[&k];
        let mut end = change_one_block(s, tests);
        assert!(!end.bottom, "k = {k}: the scope became empty");
        entries.push(end.projected.len());
        let map = std::mem::take(&mut end.projected);
        let ((), freed) = zed_alloc_count::live(|| drop(map));
        held.push(-freed.net);
    }
    eprintln!(
        "entries {entries:?} holding {held:?} bytes at k = {n} and {}",
        scaling::FACTOR * n
    );
    assert_eq!(
        entries[0], entries[1],
        "the parts' entries grew with the changes: {entries:?}"
    );
    assert!(
        held[1] <= held[0].max(0) + 1024,
        "the parts' entries held {} bytes after {} changes, {} after {n}",
        held[1],
        scaling::FACTOR * n,
        held[0]
    );
    scaling::check("k changes of the constraints of one block", n, |k| {
        let (s, tests) = &inputs[&k];
        change_one_block(s, tests);
    });
}

/// `let z = x1 + … + xk in if x1 >= 0 { let w1 = z + 1 in if x2 >= 0 { let w2 = z + 2 in … } }`,
/// ending in `if wk >= 0 { 1 } else { 2 }`: each binding reads the summary of `z`, over `k`
/// inputs, one more of them narrowed since the last read.
fn sums_read_as_inputs_narrow(k: usize) -> (Vec<Arc<str>>, Term) {
    let names: Vec<Arc<str>> = (1..=k).map(|i| format!("x{i}").into()).collect();
    let mut t = Term::If(
        arc(prim(Prim::Ge, var(&format!("w{k}")), int(0))),
        arc(int(1)),
        arc(int(2)),
    );
    for i in (1..=k).rev() {
        let x = format!("x{i}");
        let on_z = Term::Let(
            format!("w{i}").into(),
            arc(prim(Prim::Add, var("z"), int(i as i64))),
            arc(t),
        );
        t = Term::If(arc(prim(Prim::Ge, var(&x), int(0))), arc(on_z), arc(int(0)));
    }
    let sum = (2..=k).fold(var("x1"), |s, i| prim(Prim::Add, s, var(&format!("x{i}"))));
    (names, Term::Let("z".into(), arc(sum), arc(t)))
}

/// A binding over several inputs narrows each of them (item PA-walk-multi), and a test of it
/// reads, from the last read of the summary, only the inputs narrowed since: the leaves set in
/// the trees of what summaries read grow linearly in the number of tests, where reading
/// every input each time grows with its square.
#[test]
fn a_binding_over_many_inputs_narrows_each_and_is_read_in_linear_time() {
    // `let z = x + y in if y <= 0 { if z >= 5 { 1 } else { 2 } } else { 3 }`: in arm 1, x >= 5.
    let body = Term::Let(
        "z".into(),
        arc(prim(Prim::Add, var("x"), var("y"))),
        arc(Term::If(
            arc(prim(Prim::Le, var("y"), int(0))),
            arc(Term::If(
                arc(prim(Prim::Ge, var("z"), int(5))),
                arc(int(1)),
                arc(int(2)),
            )),
            arc(int(3)),
        )),
    );
    let a = super::arms(&body, &ints(&["x".into(), "y".into()]));
    assert_eq!(
        a[1].scope.get("x").ints().to_string(),
        "[5..]",
        "{:#?}",
        a[1]
    );
    let built: BTreeMap<usize, (Scope, Term)> = [40, 320]
        .into_iter()
        .map(|k| {
            let (names, t) = sums_read_as_inputs_narrow(k);
            (k, (ints(&names), t))
        })
        .collect();
    let counted = |k: usize| {
        let (s, t) = &built[&k];
        scaling::on_a_thread(1 << 26, || {
            let before = zedc::store::preimage::counts::image_sets();
            let a = super::arms(t, s);
            // Every `xi >= 0`, so `z >= 0` and `wk >= k`: only the false arm of `wk >= 0` is unreachable.
            // The arms in order: each `xi >= 0` true, `wk >= 0` true and false, each `xi >= 0` false.
            let unreachable: Vec<usize> = (0..a.len()).filter(|&i| !a[i].reachable()).collect();
            assert_eq!(unreachable, [k + 1], "{k} tests");
            zedc::store::preimage::counts::image_sets() - before
        })
    };
    let (small, large) = (counted(40), counted(320));
    assert!(
        large as f64 <= scaling::limit(40, 320, 1) * small as f64,
        "leaves set: {small} at 40 tests, {large} at 320"
    );
    scaling::check("tests of a binding over many inputs", 40, |k| {
        let (s, t) = &built[&k];
        super::arms(t, s);
    });
}

/// `if x1 >= 0 { if x1 <= 1 { … t … } else { -1 } } else { -1 }`: each `xi` of `1..=k` in
/// `0..=1` around `t`.
fn in_bits(k: usize, mut t: Term) -> Term {
    for i in (1..=k).rev() {
        let x = format!("x{i}");
        t = Term::If(
            arc(prim(Prim::Ge, var(&x), int(0))),
            arc(Term::If(
                arc(prim(Prim::Le, var(&x), int(1))),
                arc(t),
                arc(int(-1)),
            )),
            arc(int(-1)),
        );
    }
    t
}

/// `if test(1) { if test(2) { … if test(k) { 0 } else { k } … } else { 2 } } else { 1 }`.
fn nested(k: usize, test: impl Fn(usize) -> Term) -> Term {
    (1..=k).rev().fold(int(0), |t, i| {
        Term::If(arc(test(i)), arc(t), arc(int(i as i64)))
    })
}

/// `x1 + … + xk`.
fn sum_of(k: usize) -> Term {
    (2..=k).fold(var("x1"), |s, i| prim(Prim::Add, s, var(&format!("x{i}"))))
}

/// `if x1 >= 0 { if x1 <= 1 { … let z = x1 + … + xk in if z >= 1 { if z >= 2 { … if z >= k
/// { 0 } else { k } … } else { 2 } } else { 1 } … } else { -1 } } else { -1 }`: each `xi` in
/// `0..=1`, then `k` tests of `z`, a name over `k` inputs, each arm reachable.
fn tests_of_one_sum(k: usize) -> (Vec<Arc<str>>, Term) {
    let names: Vec<Arc<str>> = (1..=k).map(|i| format!("x{i}").into()).collect();
    let tests = nested(k, |i| prim(Prim::Ge, var("z"), int(i as i64)));
    let t = Term::Let("z".into(), arc(sum_of(k)), arc(tests));
    (names, in_bits(k, t))
}

#[test]
fn tests_of_a_name_over_many_inputs_take_the_bounds_of_the_inputs_they_narrow() {
    let built: BTreeMap<usize, (Scope, Term)> = [40, 320]
        .into_iter()
        .map(|k| {
            let (names, t) = tests_of_one_sum(k);
            (k, (ints(&names), t))
        })
        .collect();
    let counted = |k: usize| {
        let (s, t) = &built[&k];
        scaling::on_a_thread(1 << 26, || {
            let before = zedc::store::preimage::counts::term_bounds();
            let a = super::arms(t, s);
            assert!(a.iter().all(|a| a.reachable()), "{k} tests");
            zedc::store::preimage::counts::term_bounds() - before
        })
    };
    let (small, large) = (counted(40), counted(320));
    assert!(
        large as f64 <= scaling::limit(40, 320, 1) * small as f64,
        "term bounds: {small} at 40 tests, {large} at 320"
    );
}

/// `let z = x1 + … + xk in if x1 >= 2 { if z >= 1 { if z == 2 { … } } } else { 0 }` in the
/// scope where each `xi` is in `0..=1`: `k` tests of `z`, by `>=` and `==` in turn, in a scope
/// no state reaches. No test reads it, since what narrows and what excludes stop there, and the
/// arms shown below it share its names, emptied once (item PA-letpre-linear).
#[test]
fn tests_in_a_scope_no_state_reaches_read_nothing() {
    let built = scaling::inputs(40, |k| {
        let (names, _) = tests_of_one_sum(k);
        let bits = (1..=k)
            .flat_map(|i| {
                let x = format!("x{i}");
                [
                    prim(Prim::Ge, var(&x), int(0)),
                    prim(Prim::Le, var(&x), int(1)),
                ]
            })
            .reduce(|a, b| prim(Prim::And, a, b))
            .expect("k is not 0");
        let s = ints(&names).assume(&bits, true, &Premises::new());
        let test = |i: usize| {
            let p = if i.is_multiple_of(2) {
                Prim::Eq
            } else {
                Prim::Ge
            };
            prim(p, var("z"), int(i as i64))
        };
        let dead = Term::If(
            arc(prim(Prim::Ge, var("x1"), int(2))),
            arc(nested(k, test)),
            arc(int(0)),
        );
        (s, Term::Let("z".into(), arc(sum_of(k)), arc(dead)))
    });
    scaling::check(
        "k tests of a sum over k inputs in a scope no state reaches",
        40,
        |k| {
            let (s, t) = &built[&k];
            let a = super::arms(t, s);
            assert!(a.iter().any(|a| !a.reachable()), "{k} tests");
        },
    );
}

/// `if x1 >= 0 { if x1 <= 1 { … let z1 = x1 + 1 in … let zk = xk + k in if z1 >= 2 { …
/// if zk >= k + 1 { 0 } else { k } … } else { 1 } … } } }`: `k` tests, each of a summary over
/// one input, which reads that input as an input (item PA-letpre-linear).
#[test]
fn tests_of_summaries_over_one_input_read_that_input() {
    let built = scaling::inputs(40, |k| {
        let names: Vec<Arc<str>> = (1..=k).map(|i| format!("x{i}").into()).collect();
        let z = |i: usize| format!("z{i}");
        let tests = nested(k, |i| prim(Prim::Ge, var(&z(i)), int(i as i64 + 1)));
        let t = (1..=k).rev().fold(tests, |t, i| {
            let v = prim(Prim::Add, var(&format!("x{i}")), int(i as i64));
            Term::Let(z(i).into(), arc(v), arc(t))
        });
        (ints(&names), in_bits(k, t))
    });
    scaling::check("k tests, each of a summary over one input", 40, |k| {
        let (s, t) = &built[&k];
        let a = super::arms(t, s);
        assert!(a.iter().all(|a| a.reachable()), "{k} tests");
    });
    // The time of a test is mostly its binding's and its arms', so the inputs are counted too.
    let given = |k: usize| {
        let (s, t) = &built[&k];
        scaling::on_a_thread(1 << 26, || {
            let before = zedc::store::preimage::counts::inputs();
            super::arms(t, s);
            zedc::store::preimage::counts::inputs() - before
        })
    };
    let (small, large) = (given(40), given(320));
    assert!(
        large as f64 <= scaling::limit(40, 320, 1) * small as f64,
        "inputs given: {small} at 40 tests, {large} at 320"
    );
}

/// `z = x1 + … + xk` over each `xi` in `0..=1`, read through the tree of its terms' bounds, and
/// `k` tests `z >= 1`, the `i`-th given `xi` in `1..=1`, another domain than the scope's: each
/// reads that input over its own domain and the rest through the tree (item PA-letpre-linear).
#[test]
fn tests_that_give_an_input_another_domain_read_it_through_the_tree() {
    let built = scaling::inputs(40, |k| {
        let xs: Vec<Arc<str>> = (1..=k).map(|i| format!("x{i}").into()).collect();
        let names: images::Names<IntervalSet> = (xs.iter())
            .map(|x| (x.clone(), IntervalSet::range(End::of(0), End::of(1))))
            .collect();
        let doms: Domains = names.iter().map(|(x, d)| (x.clone(), d.clone())).collect();
        let s = let_summary(&sum_of(k), &doms, Lets::new()).expect("a sum of inputs");
        let leaf = |v: &Arc<str>, d: &IntervalSet| s.term_bounds(v, d);
        let tree = images::fresh(s.vars(), &names, leaf);
        let read = Arc::new(TermRead {
            names,
            vars: s.vars().clone(),
            tree,
            ints: |d| d,
        });
        (xs, s, read)
    });
    scaling::check(
        "k tests of a sum over k inputs, each giving one input its own domain",
        40,
        |k| {
            let (xs, s, read) = &built[&k];
            let test = prim(Prim::Ge, var("z"), int(1));
            for x in xs {
                let lets: Lets = [(
                    "z".into(),
                    LetIn {
                        summary: s.clone(),
                        ints: IntervalSet::top(),
                        read: Some(read.clone() as _),
                    },
                )]
                .into_iter()
                .collect();
                let over: Domains = [(x.clone(), IntervalSet::single(1))].into_iter().collect();
                let got = let_narrowing(&test, &over, lets, &Demand::Bool(true));
                assert!(got.is_some(), "{x}");
            }
        },
    );
}
