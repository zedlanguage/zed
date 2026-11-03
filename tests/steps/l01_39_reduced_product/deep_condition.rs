//! An `if` whose test is a chain of fallbacks nested `d` deep: a request is served at tier 0
//! when the balance `x` covers it, or else when the credit `y` covers tier 0 and the request is
//! served at tier 1, and so on, until the last tier asks `x >= d`. The two arms' scopes take
//! time near linear in `d`: each tier's formula is built once and projected once, not once
//! for each tier above it (COMPLEXITY.md, `product::arms` on a deep test).

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Prim, Term};
use zed_tests::scaling;
use zedc::store::preimage::relations;
use zedc::store::product::{Arm, Scope, arms};

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

/// `x >= 0 || ((y >= 0 || z >= 0) && (x >= 1 || …))`: two disjunctions at each level.
fn two_choices(d: usize) -> Term {
    let ge = |n: &str, v: usize| prim(Prim::Ge, vec![var(n), lit(v as i64)]);
    (0..d).rev().fold(ge("x", d), |inner, i| {
        let credit = prim(Prim::Or, vec![ge("y", i), ge("z", i)]);
        let next = prim(Prim::And, vec![credit, inner]);
        prim(Prim::Or, vec![ge("x", i), next])
    })
}

#[test]
fn two_choices_at_each_tier_leave_the_credits_free() {
    // As with one credit: a served request has `x >= 0`, a refused one `x <= -1`, and each
    // credit `y` or `z` is free in both arms.
    let scope = ints(&["x".into(), "y".into(), "z".into()]);
    for d in [1, 2, 20, 200] {
        let a = arms(&if_(two_choices(d), lit(1), lit(2)), &scope);
        assert!(a.iter().all(Arm::reachable), "d = {d}");
        let get = |k: usize, n: &str| a[k].scope.get(n).ints().to_string();
        assert_eq!(
            (get(0, "x"), get(1, "x")),
            ("[0..]".into(), "[..=-1]".into()),
            "d = {d}"
        );
        for n in ["y", "z"] {
            assert_eq!(
                (get(0, n), get(1, n)),
                ("[..]".into(), "[..]".into()),
                "d = {d}, {n}"
            );
        }
    }
}

/// Runs `f` on a thread whose stack holds the recursion over a term nested 2000 deep.
fn on_a_deep_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("the test passes");
}

#[test]
fn arms_of_a_deeper_test_take_time_near_linear_in_its_depth() {
    // Depths 250 and 2000, where a cost quadratic in the depth is plain.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [250, 2000]
            .map(|d| (d, if_(fallbacks(d), lit(1), lit(2))))
            .into();
        let scope = ints(&["x".into(), "y".into()]);
        scaling::check("arms of a test nested d deep", 250, |d| {
            std::hint::black_box(arms(&tests[&d], &scope));
        });
    });
}

#[test]
fn arms_of_a_test_with_two_choices_per_level_take_time_near_linear_in_its_depth() {
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [60, 480, 250, 2000]
            .map(|d| (d, if_(two_choices(d), lit(1), lit(2))))
            .into();
        let scope = ints(&["x".into(), "y".into(), "z".into()]);
        for n in [60, 250] {
            scaling::check("arms of a test with two choices per level", n, |d| {
                std::hint::black_box(arms(&tests[&d], &scope));
            });
        }
    });
}

#[test]
fn relations_of_a_deep_test_take_time_near_linear_in_its_depth() {
    // The translation of the test into the linear-relation domain, alone: each level is
    // translated once, not once for each level above it.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [250, 2000].map(|d| (d, fallbacks(d))).into();
        let names: [Arc<str>; 2] = ["x".into(), "y".into()];
        scaling::check("relations of a test nested d deep", 250, |d| {
            std::hint::black_box(relations(&[&tests[&d]], &names, false));
        });
    });
}

/// `x0 >= 0 || (y0 >= 0 && (x1 >= 1 || (y1 >= 1 && … (xd >= d) …)))`: a chain of accounts, each
/// with its own balance `xi` and credit `yi`, so each level names new symbols.
fn accounts(d: usize) -> Term {
    let ge = |n: String, v: usize| prim(Prim::Ge, vec![var(&n), lit(v as i64)]);
    (0..d).rev().fold(ge(format!("x{d}"), d), |inner, i| {
        let credit = prim(Prim::And, vec![ge(format!("y{i}"), i), inner]);
        prim(Prim::Or, vec![ge(format!("x{i}"), i), credit])
    })
}

/// The names `x0, y0, …, xd, yd` of [`accounts`].
fn account_names(d: usize) -> Vec<Arc<str>> {
    (0..=d)
        .flat_map(|i| [format!("x{i}").into(), format!("y{i}").into()])
        .collect()
}

#[test]
fn only_the_first_account_is_narrowed() {
    // A request served by account 0's balance needs nothing of the others, so in the then arm
    // every symbol is free; one refused has `x0 <= -1`, and the rest are free there too.
    for d in [1, 2, 20, 200] {
        let names = account_names(d);
        let a = arms(&if_(accounts(d), lit(1), lit(2)), &ints(&names));
        assert!(a.iter().all(Arm::reachable), "d = {d}");
        for n in &names {
            let get = |k: usize| a[k].scope.get(n).ints().to_string();
            let refused = if &**n == "x0" { "[..=-1]" } else { "[..]" };
            assert_eq!(
                (get(0).as_str(), get(1).as_str()),
                ("[..]", refused),
                "d = {d}, {n}"
            );
        }
    }
}

/// [`two_choices`] with the balance capped at `2d` below each tier:
/// `x >= 0 || ((y >= 0 || z >= 0) && x <= 2d && (x >= 1 || …))`.
fn capped(d: usize) -> Term {
    let cmp = |p: Prim, n: &str, v: usize| prim(p, vec![var(n), lit(v as i64)]);
    (0..d).rev().fold(cmp(Prim::Ge, "x", d), |inner, i| {
        let credit = prim(Prim::Or, vec![cmp(Prim::Ge, "y", i), cmp(Prim::Ge, "z", i)]);
        let cap = prim(Prim::And, vec![cmp(Prim::Le, "x", 2 * d), inner]);
        let next = prim(Prim::And, vec![credit, cap]);
        prim(Prim::Or, vec![cmp(Prim::Ge, "x", i), next])
    })
}

#[test]
fn a_cap_below_each_tier_leaves_the_balance_unbounded_above() {
    // Tier 0 asks only `x >= 0`, so the cap below it does not bound a served request.
    let scope = ints(&["x".into(), "y".into(), "z".into()]);
    for d in [1, 2, 20, 200] {
        let a = arms(&if_(capped(d), lit(1), lit(2)), &scope);
        let get = |k: usize, n: &str| a[k].scope.get(n).ints().to_string();
        assert_eq!(
            (get(0, "x"), get(1, "x")),
            ("[0..]".into(), "[..=-1]".into()),
            "d = {d}"
        );
        assert_eq!(
            (get(0, "y"), get(0, "z")),
            ("[..]".into(), "[..]".into()),
            "d = {d}"
        );
    }
}

/// `a op v` for the tests below.
fn cmp(p: Prim, n: &str, v: i64) -> Term {
    prim(p, vec![var(n), lit(v)])
}

/// The conjunction of `ts`.
fn all(ts: Vec<Term>) -> Term {
    ts.into_iter()
        .reduce(|a, b| prim(Prim::And, vec![a, b]))
        .expect("a part")
}

/// `a || b`.
fn either(a: Term, b: Term) -> Term {
    prim(Prim::Or, vec![a, b])
}

#[test]
fn two_choices_inside_a_branch_still_narrow_its_bounds() {
    // `(z >= 0 && 20 <= x <= 30) || (0 <= x <= 10 && (x >= 5 || y >= 0) && (y <= -1 || x >= 7))`:
    // in the second branch `y >= 0` needs `x >= 7` and `y <= -1` needs `x >= 5`, so `x` is in
    // `5..=10` there, though each choice alone allows `0..=10`.
    let ge = |n, v| cmp(Prim::Ge, n, v);
    let le = |n, v| cmp(Prim::Le, n, v);
    let first = all(vec![ge("z", 0), ge("x", 20), le("x", 30)]);
    let second = all(vec![
        ge("x", 0),
        le("x", 10),
        either(ge("x", 5), ge("y", 0)),
        either(le("y", -1), ge("x", 7)),
    ]);
    let names: Vec<Arc<str>> = ["x", "y", "z"].map(Into::into).into();
    let a = arms(&if_(either(first, second), lit(1), lit(2)), &ints(&names));
    assert_eq!(a[0].scope.get("x").ints().to_string(), "[5..=10, 20..=30]");
}

#[test]
fn a_branch_with_no_point_does_not_widen_the_other() {
    // The second branch asks `a` and `b` each to be both at most 0 and at least 1 in some
    // combination, so it has no point, though no single choice in it is ruled out alone;
    // the then arm is the first branch's.
    let ge = |n, v| cmp(Prim::Ge, n, v);
    let le = |n, v| cmp(Prim::Le, n, v);
    let none = all(vec![
        either(ge("a", 1), ge("b", 1)),
        either(ge("a", 1), le("b", 0)),
        either(le("a", 0), ge("b", 1)),
        either(le("a", 0), le("b", 0)),
    ]);
    let first = all(vec![ge("x", 3), ge("y", 0), ge("z", 0)]);
    let names: Vec<Arc<str>> = ["x", "y", "z", "a", "b"].map(Into::into).into();
    let a = arms(&if_(either(first, none), lit(1), lit(2)), &ints(&names));
    let get = |n: &str| a[0].scope.get(n).ints().to_string();
    assert_eq!([get("x"), get("y"), get("z")], ["[3..]", "[0..]", "[0..]"]);
}

#[test]
fn arms_of_a_chain_of_accounts_take_time_near_linear_in_its_depth() {
    // Each level names two new symbols, so a level that asked for every symbol below it would
    // cost the depth once for each level.
    on_a_deep_stack(|| {
        let cases: BTreeMap<usize, (Term, Scope)> = [60, 480]
            .map(|d| {
                (
                    d,
                    (if_(accounts(d), lit(1), lit(2)), ints(&account_names(d))),
                )
            })
            .into();
        scaling::check("arms of a chain of accounts d deep", 60, |d| {
            let (t, scope) = &cases[&d];
            std::hint::black_box(arms(t, scope));
        });
    });
}

#[test]
fn arms_of_a_capped_test_take_time_near_linear_in_its_depth() {
    // Two disjunctions and a hull with two finite bounds at each level, the case a level
    // tightens; a tightening over the whole nest below each level would cost its depth.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [30, 240]
            .map(|d| (d, if_(capped(d), lit(1), lit(2))))
            .into();
        let scope = ints(&["x".into(), "y".into(), "z".into()]);
        scaling::check("arms of a capped test nested d deep", 30, |d| {
            std::hint::black_box(arms(&tests[&d], &scope));
        });
    });
}
