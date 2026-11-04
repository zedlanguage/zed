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
use zedc::store::presburger;
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
    // `let t = <chain> in t && (t || x >= 5)` is `t` itself: the named test is translated
    // once, its formula held at both uses, and the arms are those of the chain written out.
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
    // The second branch asks `a` to be at most 0 and at least 1, and `b` at most `k - 1` and
    // at least `k`, in some combination, so it has no point, though no single choice in it is
    // ruled out alone; the then arm is the first branch's.
    let ge = |n, v| cmp(Prim::Ge, n, v);
    let le = |n, v| cmp(Prim::Le, n, v);
    let then_arm = |k: i64, z: i64| {
        let none = all(vec![
            either(ge("a", 1), ge("b", k)),
            either(ge("a", 1), le("b", k - 1)),
            either(le("a", 0), ge("b", k)),
            either(le("a", 0), le("b", k - 1)),
        ]);
        let first = all(vec![ge("x", 3), ge("y", 0), ge("z", z)]);
        let names: Vec<Arc<str>> = ["x", "y", "z", "a", "b"].map(Into::into).into();
        let a = arms(&if_(either(first, none), lit(1), lit(2)), &ints(&names));
        let get = |n: &str| a[0].scope.get(n).ints().to_string();
        [get("x"), get("y"), get("z")]
    };
    // With `k = 2` and `z >= 1` every atom has a color of its own, so the formula is renamed
    // and searched, and the search shows the second branch empty.
    assert_eq!(then_arm(2, 1), ["[3..]", "[0..]", "[1..]"]);
    // With `k = 1` and `z >= 0`, `a` and `b` occur alike, as do `y` and `z`: only a search
    // in an order chosen by name would show the second branch empty (NAME-ties, COMPLEXITY.md
    // NAME-ties-or), so it is kept, and the then arm is no narrower than the scope.
    assert_eq!(then_arm(1, 0), ["[..]", "[..]", "[..]"]);
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

/// Panics when `run` at `8n` does more than `8 ln(8n) / ln(n)` times its work at `n`, the
/// ratio work of order `n log n` has. The rule's limit of 24 times does not tell `n log n`
/// from a small `n²` term at these sizes.
fn within_n_log_n(what: &str, n: usize, run: impl Fn(usize) + Sync) {
    let limit = 8.0 * (8.0 * n as f64).ln() / (n as f64).ln();
    scaling::compare(
        &format!("{what}: sizes {n} and {}", 8 * n),
        &format!("work of order n log n does at most {limit:.2} times the work"),
        limit,
        || run(n),
        || run(8 * n),
    );
}

#[test]
fn arms_of_a_long_chain_of_accounts_take_time_within_n_log_n() {
    // A lookup of a conjunct in the relation's maps finds the very formula it holds; compared
    // in full, the nest below the level, each lookup cost the depth: 0.85 and 13.19 G
    // instructions at d = 240 and 1920, 15.5 times. Now 0.76 and 7.84 G, 10.2 times.
    on_a_deep_stack(|| {
        let cases: BTreeMap<usize, (Term, Scope)> = [240, 1920]
            .map(|d| {
                (
                    d,
                    (if_(accounts(d), lit(1), lit(2)), ints(&account_names(d))),
                )
            })
            .into();
        within_n_log_n("arms of a chain of accounts d deep", 240, |d| {
            let (t, scope) = &cases[&d];
            std::hint::black_box(arms(t, scope));
        });
    });
}

/// [`accounts_paired`] nested `d` deep, each level's choice on its own symbol `qi`, around
/// `x <= 0 && y >= 1 || x >= 10 && y <= -1`.
fn paired_chain(d: usize) -> Term {
    let ge = |n: &str, v| cmp(Prim::Ge, n, v);
    let le = |n: &str, v| cmp(Prim::Le, n, v);
    let base = either(
        all(vec![le("x", 0), ge("y", 1)]),
        all(vec![ge("x", 10), le("y", -1)]),
    );
    let level = |inner, q: &str| {
        let first = either(
            all(vec![ge(q, 0), inner]),
            all(vec![le(q, -1), ge("x", 3), le("x", 4)]),
        );
        let second = either(all(vec![ge("y", 1), ge("x", 5)]), le(q, -1));
        all(vec![ge("x", 0), le("x", 10), first, second])
    };
    let nest = (0..d).fold(base, |inner, i| level(inner, &format!("q{i}")));
    either(all(vec![ge("x", 100), le("x", 200)]), nest)
}

/// The names `x`, `y`, `q0, …, q(d-1)` of [`paired_chain`].
fn paired_names(d: usize) -> Vec<Arc<str>> {
    let qs = (0..d).map(|i| Arc::from(format!("q{i}")));
    ["x".into(), "y".into()].into_iter().chain(qs).collect()
}

#[test]
fn a_chain_of_paired_choices_keeps_only_the_small_choice() {
    // At each level `qi >= 0` needs `y >= 1` and `x >= 5`, which the level below allows only
    // at `3 <= x <= 4` or, at the bottom, at `x <= 0` or `y <= -1`; so every level takes
    // `qi <= -1` and `3 <= x <= 4`.
    for d in [1, 2, 20, 200] {
        let a = arms(
            &if_(paired_chain(d), lit(1), lit(2)),
            &ints(&paired_names(d)),
        );
        let get = |k: usize, n: &str| a[k].scope.get(n).ints().to_string();
        assert_eq!(get(0, "x"), "[3..=4, 100..=200]", "d = {d}");
        assert_eq!(get(1, "x"), "[..=99, 201..]", "d = {d}");
    }
}

#[test]
fn arms_of_a_chain_of_paired_choices_take_time_within_n_log_n() {
    // Most cases of a level fail. Each failed case emptied every name in scope, the depth
    // of them: 1.45 and 22.16 G instructions at d = 120 and 960, 15.2 times. A failed case
    // is dropped, so now only a scope that is shown is emptied: 1.31 and 11.56 G, 8.8 times.
    on_a_deep_stack(|| {
        let cases: BTreeMap<usize, (Term, Scope)> = [120, 960]
            .map(|d| {
                (
                    d,
                    (if_(paired_chain(d), lit(1), lit(2)), ints(&paired_names(d))),
                )
            })
            .into();
        within_n_log_n("arms of a chain of paired choices d deep", 120, |d| {
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

/// At each level `i` of `d`: `(100 <= x <= 200 && w >= i) || (0 <= x <= 10 && (x >= 5 ||
/// y >= 0) && (y <= -1 || x >= 7) && level i + 1)`, the last level `w >= d`. Inside each level
/// `x` is in `5..=10`, though each choice alone allows `0..=10`, so the hull of `x` moves
/// inward at every level.
fn moving(d: usize) -> Term {
    let ge = |n, v: usize| cmp(Prim::Ge, n, v as i64);
    let le = |n, v: i64| cmp(Prim::Le, n, v);
    (0..d).rev().fold(ge("w", d), |inner, i| {
        let body = all(vec![
            ge("x", 0),
            le("x", 10),
            either(ge("x", 5), ge("y", 0)),
            either(le("y", -1), ge("x", 7)),
            inner,
        ]);
        either(all(vec![ge("x", 100), le("x", 200), ge("w", i)]), body)
    })
}

/// At each level `i` of `d`: `(100 <= x <= 200 && v >= i) || ((y >= 0 || z >= 0) && ((20 <= x
/// <= 30 && w >= i) || (0 <= x <= 10 && level i + 1)))`, the last level `w >= d`. The small
/// choice `20..=30` misses the bound `10` that the deep choice holds, so a point at that bound
/// is found only below every level.
fn heavy(d: usize) -> Term {
    let ge = |n, v: usize| cmp(Prim::Ge, n, v as i64);
    let le = |n, v: i64| cmp(Prim::Le, n, v);
    (0..d).rev().fold(ge("w", d), |inner, i| {
        let deep = all(vec![ge("x", 0), le("x", 10), inner]);
        let small = all(vec![ge("x", 20), le("x", 30), ge("w", i)]);
        let body = all(vec![either(ge("y", 0), ge("z", 0)), either(small, deep)]);
        either(all(vec![ge("x", 100), le("x", 200), ge("v", i)]), body)
    })
}

/// The names `moving` and `heavy` use.
fn level_names() -> Vec<Arc<str>> {
    ["x", "y", "z", "w", "v"].map(Into::into).into()
}

/// The hull of `x` in the then and else arms of `if test then 1 else 2`.
fn x_hulls(test: Term) -> [String; 2] {
    let a = arms(&if_(test, lit(1), lit(2)), &ints(&level_names()));
    assert_eq!(a.len(), 2);
    [0, 1].map(|k| a[k].scope.get("x").ints().to_string())
}

#[test]
fn arms_of_a_test_whose_bound_moves_at_each_level_keep_the_inner_bound() {
    for d in [1, 2, 5, 40] {
        assert_eq!(
            x_hulls(moving(d)),
            ["[5..=10, 100..=200]", "[..]"].map(String::from),
            "d = {d}"
        );
    }
}

#[test]
fn arms_of_a_test_whose_small_choice_misses_the_bound_keep_every_range() {
    for d in [1, 2, 5, 40] {
        assert_eq!(
            x_hulls(heavy(d)),
            ["[0..=10, 20..=30, 100..=200]", "[..]"].map(String::from),
            "d = {d}"
        );
    }
}

#[test]
fn arms_of_a_test_whose_bound_moves_at_each_level_take_time_near_linear_in_its_depth() {
    // Each level tightens the hull of `x`; a tightening over the whole nest below each level,
    // or a search that reads again the nest below each level, would cost its depth.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [60, 480]
            .map(|d| (d, if_(moving(d), lit(1), lit(2))))
            .into();
        let scope = ints(&level_names());
        scaling::check("arms of a test whose bound moves at each level", 60, |d| {
            std::hint::black_box(arms(&tests[&d], &scope));
        });
    });
}

#[test]
fn arms_of_a_test_whose_small_choice_misses_the_bound_take_time_near_linear_in_its_depth() {
    // A point at the bound is found only below every level, so a search that read the nest
    // below each level again would cost its depth.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> =
            [60, 480].map(|d| (d, if_(heavy(d), lit(1), lit(2)))).into();
        let scope = ints(&level_names());
        scaling::check(
            "arms of a test whose small choice misses the bound",
            60,
            |d| {
                std::hint::black_box(arms(&tests[&d], &scope));
            },
        );
    });
}

/// `100 <= x <= 200 || (0 <= x <= 10 && (q >= 0 && inner || q <= -1 && 3 <= x <= 4) && (y >= 1
/// && x >= 5 || q <= -1))`: a branch whose first choice holds `inner`, a choice between `x`
/// and `y` of opposite signs, beside a second choice that needs `y >= 1` and `x >= 5`.
fn accounts_paired(inner: Term) -> Term {
    let ge = |n, v| cmp(Prim::Ge, n, v);
    let le = |n, v| cmp(Prim::Le, n, v);
    let first = either(
        all(vec![ge("q", 0), inner]),
        all(vec![le("q", -1), ge("x", 3), le("x", 4)]),
    );
    let second = either(all(vec![ge("y", 1), ge("x", 5)]), le("q", -1));
    let level = all(vec![ge("x", 0), le("x", 10), first, second]);
    either(all(vec![ge("x", 100), le("x", 200)]), level)
}

/// The hull of `x` in the then arm of `if test then 1 else 2` over `x`, `y` and `q`.
fn then_x(test: Term) -> String {
    let names: Vec<Arc<str>> = ["x", "y", "q"].map(Into::into).into();
    let a = arms(&if_(test, lit(1), lit(2)), &ints(&names));
    a[0].scope.get("x").ints().to_string()
}

#[test]
fn a_choice_one_level_inside_a_branch_is_read_with_the_rest_of_the_branch() {
    // Inner: `x <= 0 && y >= 1 || x >= 10 && y <= -1`. With `q >= 0` the second choice needs
    // `y >= 1` and `x >= 5`, which neither inner choice meets, so `q <= -1` and `3 <= x <= 4`.
    let ge = |n, v| cmp(Prim::Ge, n, v);
    let le = |n, v| cmp(Prim::Le, n, v);
    let inner = either(
        all(vec![le("x", 0), ge("y", 1)]),
        all(vec![ge("x", 10), le("y", -1)]),
    );
    assert_eq!(then_x(accounts_paired(inner)), "[3..=4, 100..=200]");
}

#[test]
fn a_choice_two_levels_inside_a_branch_is_read_by_its_projections_only() {
    // Inner as above with each sign of `y` one choice further in: `x <= 0 && (y >= 1 || y >=
    // 2) || x >= 10 && (y <= -1 || y <= -2)`. The level reads the inner choices by their own
    // constraints and the branch by its projections, `x` in `{0, 10}` and `y` not 0, which
    // allow `x = 10` with `y = 1`, so `10` is kept, though no point of the test has it
    // (tradeoff comment at `presburger::summarize`).
    let ge = |n, v| cmp(Prim::Ge, n, v);
    let le = |n, v| cmp(Prim::Le, n, v);
    let inner = either(
        all(vec![le("x", 0), either(ge("y", 1), ge("y", 2))]),
        all(vec![ge("x", 10), either(le("y", -1), le("y", -2))]),
    );
    assert_eq!(
        then_x(accounts_paired(inner)),
        "[3..=4, 10..=10, 100..=200]"
    );
}

#[test]
fn the_search_for_a_point_tests_each_part_of_a_deep_test_a_bounded_number_of_times() {
    // The search marks a part it finds not to hold and does not test it again while its values
    // are unchanged (`Parts::failed`). Without the marks a nest that fails deep is tested again
    // below each level: 516 parts per level at d = 60 and 3876 at d = 480 for `heavy`. With
    // them both nests measure 24 to 41 parts per level at both depths.
    on_a_deep_stack(|| {
        let scope = ints(&level_names());
        for (name, nest) in [("heavy", heavy as fn(usize) -> Term), ("moving", moving)] {
            for d in [60, 480] {
                let test = if_(nest(d), lit(1), lit(2));
                presburger::parts_tested();
                std::hint::black_box(arms(&test, &scope));
                let tested = presburger::parts_tested();
                assert!(
                    tested <= 48 * d as u64,
                    "{name}, d = {d}: {tested} parts tested, more than 48 per level"
                );
            }
        }
    });
}
