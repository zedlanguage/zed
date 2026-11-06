//! Arm tests that call the unit's definitions (DESIGN.md Part G, steps L1.25 and L1.39): a
//! test is narrowed through the calls it makes, so in
//!
//! ```text
//! clamp(positional x: int) = if x < 0 { 0 } else if x > 10 { 10 } else { x };
//! ok(x) = if clamp(x) > 10 { "over" } else if clamp(x) == 10 { "top" } else ...
//! ```
//!
//! the arm `clamp(x) > 10` is unreachable, since `clamp` never exceeds 10. A call the
//! transfer cannot follow, such as one of a function that calls itself, may leave an arm
//! reachable, but never makes a reached arm unreachable.

use std::collections::BTreeMap;
use std::sync::Arc;
use zed_kernel::Shared;

use zed_kernel::{Evaluator, Prim, Term, Value, World, on_stack};

use super::*;
use zed_tests::step_helpers::l01_16_elaboration::with_prelude;

/// The value of the function `ok` of `src` at the integer `x`.
fn run(src: &str, x: i64) -> Value {
    let u = zed_tests::step_helpers::l01_16_elaboration::elab(src)
        .unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let ok = u.get("ok").expect("a definition `ok`");
    let call = Term::App(Shared::new(ok), vec![Term::Lit(Value::Int(x))]);
    on_stack(|| Evaluator::new(World::new()).run(&with_prelude(call)))
        .unwrap_or_else(|e| panic!("{src}: ok({x}) failed: {e:?}"))
}

/// Checks the arms of an `else if` chain, whose `k`th test returns `results[k]` and whose
/// last `else` returns the last result, against the interpreter on `-30..=30`: each point
/// reaches the arms on its way to its result, and each of these arms' scopes holds it. The
/// arms some point reaches, by their indexes in `arms`.
fn reached_in_chain(src: &str, param: &Arc<str>, arms: &[Arm], results: &[&str]) -> Vec<usize> {
    assert_eq!(arms.len(), 2 * (results.len() - 1), "{src}");
    // A name not in a scope is not checked, so the parameter must be in each.
    assert!(
        arms.iter().all(|a| a.scope.names.contains_key(param)),
        "{src}"
    );
    let mut reached = std::collections::BTreeSet::new();
    for x in -30..=30 {
        let v = run(src, x);
        let r = results
            .iter()
            .position(|s| Value::Str((*s).into()) == v)
            .unwrap_or_else(|| panic!("{src}: ok({x}) = {v}"));
        // The false arms of the tests before the one taken, and the taken arm.
        let mut on_path: Vec<usize> = (0..r.min(results.len() - 2)).map(|j| 2 * j + 1).collect();
        on_path.push(if r < results.len() - 1 {
            2 * r
        } else {
            2 * r - 1
        });
        let env: BTreeMap<Arc<str>, Value> = [(param.clone(), Value::Int(x))].into();
        for i in on_path {
            assert!(
                arms[i].scope.contains(&env),
                "{src}: x = {x} reaches arm {i} ({} is {}), whose scope does not hold it:\n{}",
                arms[i].guard,
                arms[i].outcome,
                arms[i].scope
            );
            reached.insert(i);
        }
    }
    reached.into_iter().collect()
}

/// The indexes of the unreachable arms.
fn unreachable(arms: &[Arm]) -> Vec<usize> {
    (0..arms.len()).filter(|&i| !arms[i].reachable()).collect()
}

const ZONE: &str = "clamp(positional x: int) = if x < 0 { 0 } else if x > 10 { 10 } else { x };\n\
     ok(x) = if clamp(x) > 10 { \"over\" } else if clamp(x) == 10 { \"top\" } \
     else if clamp(x) == 0 { \"floor\" } else { \"middle\" };";

#[test]
fn an_arm_whose_test_calls_a_helper_that_never_meets_it_is_unreachable() {
    let (ps, _, a) = arms_of(ZONE);
    let a: Vec<Arm> = a.into_iter().rev().take(6).rev().collect();
    let reached = reached_in_chain(ZONE, &ps[0], &a, &["over", "top", "floor", "middle"]);
    // No point gives "over"; every other arm is reached.
    assert_eq!(reached, [1, 2, 3, 4, 5]);
    assert_eq!(unreachable(&a), [0], "{:#?}", a);
    assert_eq!(a[0].scope.to_string(), "unreachable\n");
}

#[test]
fn a_helper_called_in_several_arms_narrows_each_arm() {
    let (ps, _, a) = arms_of(ZONE);
    let a: Vec<Arm> = a.into_iter().rev().take(6).rev().collect();
    // The values of `x` in the arm whose test contains `guard`, taken by `outcome`.
    let x =
        |guard: &str, outcome: bool| arm(&a, guard, outcome).scope.get(&ps[0]).ints().to_string();
    // `clamp(x) == 10` holds from 10 up, `clamp(x) == 0` below 1, and the middle is 1..=9.
    assert_eq!(x("== 10", true), "[10..]");
    assert_eq!(x("== 10", false), "[..=9]");
    assert_eq!(x("== 0", true), "[..=0]");
    assert_eq!(x("== 0", false), "[1..=9]");
}

#[test]
fn a_helper_that_calls_a_helper_is_read_through_both() {
    // `double` is even and within 0..=20, so 21 and 7 are out of its reach.
    let src = "clamp(positional x: int) = if x < 0 { 0 } else if x > 10 { 10 } else { x };\n\
         double(positional x: int) = 2 * clamp(x);\n\
         ok(x) = if double(x) > 20 { \"over\" } else if double(x) == 7 { \"odd\" } \
         else if double(x) == 20 { \"top\" } else { \"rest\" };";
    let (ps, _, a) = arms_of(src);
    let a: Vec<Arm> = a.into_iter().rev().take(6).rev().collect();
    let reached = reached_in_chain(src, &ps[0], &a, &["over", "odd", "top", "rest"]);
    assert_eq!(reached, [1, 3, 4, 5]);
    assert_eq!(unreachable(&a), [0, 2], "{:#?}", a);
}

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

/// `h = (g, x) -> if x > 0 { g(g, x - 1) + 1 } else { 0 }`, which calls itself through `g`:
/// `h(h, x)` is `x` for `x >= 0` and 0 below. Recursion is rejected in source until layer
/// L6, so the kernel term is built by hand.
fn counting() -> Term {
    let call = Term::App(
        Shared::new(var("g")),
        vec![var("g"), prim(Prim::Sub, var("x"), int(1))],
    );
    let body = Term::If(
        Shared::new(prim(Prim::Gt, var("x"), int(0))),
        Shared::new(prim(Prim::Add, call, int(1))),
        Shared::new(int(0)),
    );
    Term::Lam(vec!["g".into(), "x".into()], Shared::new(body))
}

/// `h = counting; if h(h, x) > c { 1 } else { 2 }`.
fn recursive_test(c: i64) -> Term {
    let call = Term::App(Shared::new(var("h")), vec![var("h"), var("x")]);
    Term::Let(
        "h".into(),
        Shared::new(counting()),
        Shared::new(Term::If(
            Shared::new(prim(Prim::Gt, call, int(c))),
            Shared::new(int(1)),
            Shared::new(int(2)),
        )),
    )
}

#[test]
fn a_helper_that_calls_itself_never_makes_a_reached_arm_unreachable() {
    for c in [5, -1, 0] {
        let t = recursive_test(c);
        let a = arms(&t, &ints(&["x".into()]));
        // The two arms of the test, after those inside `h`, which the walk does not enter.
        let a = &a[a.len() - 2..];
        for x in -20..=20i64 {
            let env: BTreeMap<Arc<str>, Value> = [("x".into(), Value::Int(x))].into();
            let taken = usize::from(x.max(0) <= c);
            assert!(
                a[taken].scope.contains(&env),
                "c = {c}: x = {x} reaches arm {taken}, whose scope does not hold it:\n{}",
                a[taken].scope
            );
        }
    }
    // `h(h, x) < 0` is never true, but the transfer stops at the call `h` makes of itself, so
    // the arm may stay reachable; it is not required to be found unreachable.
    let call = Term::App(Shared::new(var("h")), vec![var("h"), var("x")]);
    let t = Term::Let(
        "h".into(),
        Shared::new(counting()),
        Shared::new(Term::If(
            Shared::new(prim(Prim::Lt, call, int(0))),
            Shared::new(int(1)),
            Shared::new(int(2)),
        )),
    );
    let a = arms(&t, &ints(&["x".into()]));
    assert!(a[a.len() - 1].reachable());
}

#[test]
fn a_helper_reads_the_binding_it_was_defined_under() {
    // `k = 100; f = (y) -> k; k = 0; if f(x) > 50 { 1 } else { 2 }`: `f` reads the first `k`, so
    // `f(x) > 50` always holds. Closing the test over `f` under the second `k` would read 0
    // and find the true arm unreachable; the true arm must stay reachable.
    let f = Term::Lam(vec!["y".into()], Shared::new(var("k")));
    let test = prim(
        Prim::Gt,
        Term::App(Shared::new(var("f")), vec![var("x")]),
        int(50),
    );
    let if_ = || {
        Term::If(
            Shared::new(test.clone()),
            Shared::new(int(1)),
            Shared::new(int(2)),
        )
    };
    // With no second `k`, the test is read through `f` and its false arm is unreachable.
    let once = Term::Let(
        "k".into(),
        Shared::new(int(100)),
        Shared::new(Term::Let(
            "f".into(),
            Shared::new(f.clone()),
            Shared::new(if_()),
        )),
    );
    let a = arms(&once, &ints(&["x".into()]));
    assert_eq!(a.len(), 2);
    assert!(a[0].reachable() && !a[1].reachable(), "{:#?}", a);
    let t = Term::Let(
        "k".into(),
        Shared::new(int(100)),
        Shared::new(Term::Let(
            "f".into(),
            Shared::new(f),
            Shared::new(Term::Let(
                "k".into(),
                Shared::new(int(0)),
                Shared::new(if_()),
            )),
        )),
    );
    let a = arms(&t, &ints(&["x".into()]));
    assert_eq!(a.len(), 2);
    assert!(a[0].reachable(), "{:#?}", a);
}
