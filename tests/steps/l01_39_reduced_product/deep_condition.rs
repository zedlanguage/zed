//! An `if` whose test is a chain of fallbacks nested `d` deep: a request is served at tier 0
//! when the balance `x` covers it, or else when the credit `y` covers tier 0 and the request is
//! served at tier 1, and so on, until the last tier asks `x >= d`. The two arms' scopes take
//! time near linear in `d`: each tier's formula is built once and projected once, not once
//! for each tier above it (COMPLEXITY.md, `product::arms` on a deep test).

use std::collections::BTreeMap;

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Prim, Term};
use zed_tests::scaling;
use zedc::store::product::{Arm, arms};

use super::ints;

/// `x >= 0 || (y >= 0 && (x >= 1 || (y >= 1 && … (x >= d) …)))`.
fn fallbacks(d: usize) -> Term {
    let ge = |n: &str, v: usize| prim(Prim::Ge, vec![var(n), lit(v as i64)]);
    (0..d).rev().fold(ge("x", d), |inner, i| {
        let credit = prim(Prim::And, vec![ge("y", i), inner]);
        prim(Prim::Or, vec![ge("x", i), credit])
    })
}

/// The arms of `if test then 1 else 2` over integers `x` and `y`.
fn arms_of(test: Term) -> Vec<Arm> {
    arms(&if_(test, lit(1), lit(2)), &ints(&["x".into(), "y".into()]))
}

/// `(then x, else x, then y, else y)` as the scopes print them.
fn hulls(a: &[Arm]) -> [String; 4] {
    assert_eq!(a.len(), 2);
    let get = |k: usize, n: &str| a[k].scope.get(n).ints().to_string();
    [get(0, "x"), get(1, "x"), get(0, "y"), get(1, "y")]
}

#[test]
fn every_tier_needs_a_balance_of_at_least_zero() {
    // Each tier asks `x >= i` for some `i >= 0`, so a served request has `x >= 0`, and one
    // refused at tier 0 has `x <= -1`; the credit `y` is free in both.
    for d in [1, 2, 20, 200] {
        let a = arms_of(fallbacks(d));
        assert!(a.iter().all(Arm::reachable), "d = {d}");
        let [tx, ex, ty, ey] = hulls(&a);
        assert_eq!((tx.as_str(), ex.as_str()), ("[0..]", "[..=-1]"), "d = {d}");
        assert_eq!((ty.as_str(), ey.as_str()), ("[..]", "[..]"), "d = {d}");
    }
}

#[test]
fn one_tier_is_the_balance_or_the_credit_and_the_next() {
    // `x >= 0 || (y >= 0 && x >= 1)`: the else arm has `x <= -1`, so the credit cannot help.
    let a = arms_of(fallbacks(1));
    assert_eq!(a[0].guard, a[1].guard);
    assert_eq!((a[0].outcome, a[1].outcome), (true, false));
    assert_eq!(hulls(&a)[1], "[..=-1]");
}

#[test]
fn a_constant_test_leaves_one_arm_unreachable() {
    // An empty chain is a literal: `true` takes only the first arm, `false` only the second.
    for (b, live) in [(true, 0), (false, 1)] {
        let a = arms_of(lit(b));
        assert_eq!(a.len(), 2);
        assert!(a[live].reachable() && !a[1 - live].reachable(), "{b}");
    }
}

#[test]
fn a_tier_named_once_and_asked_twice_narrows_as_if_written_out() {
    // `let t = <chain> in t && (t || x >= 5)` is `t` itself: the shared test is translated
    // once more when asked the second time, and the arms are those of the chain written out.
    let shared = let_(
        "t",
        fallbacks(20),
        prim(
            Prim::And,
            vec![
                var("t"),
                prim(
                    Prim::Or,
                    vec![var("t"), prim(Prim::Ge, vec![var("x"), lit(5)])],
                ),
            ],
        ),
    );
    let a = arms_of(shared);
    assert_eq!(a[0].scope.get("x").ints().to_string(), "[0..]");
    assert!(a[0].reachable());
}

#[test]
fn arms_of_a_deep_test_take_time_near_linear_in_its_depth() {
    // The tests are built before the measurement, so that only `arms` is measured.
    let tests: BTreeMap<usize, Term> = [60, 480].map(|d| (d, fallbacks(d))).into();
    let scope = ints(&["x".into(), "y".into()]);
    scaling::check("arms of a test nested d deep", 60, |d| {
        let t = if_(tests[&d].clone(), lit(1), lit(2));
        std::hint::black_box(arms(&t, &scope));
    });
}
