//! A tuple that holds a function is a cell whose parts are counted references, as a tuple of
//! data is (row FIX-functions-in-tuples): building, matching and reading one costs its number
//! of parts, whatever the parts hold, so `n` of them run in O(n). The small instances are in
//! `held_values.rs`.

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, Pattern, Prim, Shared, Term, Value, World};
use zed_tests::scaling;
use zedc::zir::memory;

use super::scaling::check_run;
use crate::function_binders::{bind, calls, match1};
use crate::planned;
use crate::scaling::strings;

/// `match (f, z) { (h, k) -> h(k) }` in each of `n` calls.
fn matched(n: usize) -> Term {
    let s = prim(Prim::Tuple, vec![var("f"), var("z")]);
    calls(
        n,
        match1(
            s,
            Pattern::Tuple(vec![bind("h"), bind("k")]),
            app(var("h"), vec![var("k")]),
        ),
    )
}

/// `x = read x; f = (y) -> y; g = (y) -> match (f, x, y) { (h, a, b) -> h(b) }; (g(0), …,
/// g(n-1))`: each call holds the tuple `x` in a held tuple, which the arm does not use.
fn holding(n: usize) -> Term {
    let p = Pattern::Tuple(vec![bind("h"), bind("a"), bind("b")]);
    let s = prim(Prim::Tuple, vec![var("f"), var("x"), var("y")]);
    let body = app(var("h"), vec![var("b")]);
    let g = lam(&["y"], Term::Match(Shared::new(s), vec![(p, body)]));
    let gs = (0..n).map(|i| app(var("g"), vec![lit(i as i64)])).collect();
    let_(
        "x",
        Term::Read("x".into()),
        let_(
            "f",
            lam(&["y"], var("y")),
            let_("g", g, prim(Prim::Tuple, gs)),
        ),
    )
}

/// `n` matches of a held tuple: O(1) each, so the run is O(n).
#[test]
fn matches_of_held_tuples_scale() {
    check_run(
        "n matches of a tuple holding a function",
        1_800,
        matched,
        |_| World::new(),
    );
}

/// `n` held tuples, each holding a tuple of `64n` strings: each holds it by one count, not a
/// copy, so the run is O(n) and not O(n^2). Copying the held part, as a held tuple kept as a
/// kernel value in a cell would, costs `64n` per call; a fresh tuple of `n` parts made in each
/// call, the same O(n^2) shape, fails this check (negative control run 2026-11-14,
/// FIX-functions-in-tuples).
#[test]
fn held_tuples_holding_a_large_tuple_scale() {
    check_run(
        "n tuples holding a function and a tuple of 64n strings",
        1_200,
        holding,
        |n| strings(64 * n),
    );
}

/// `(k in {0, …, n-1}) -> body`.
fn over(n: usize, body: Term) -> Term {
    Term::Fam {
        domain: Shared::new(lit(Value::Family(Family::set(
            (0..n as i64).map(Value::Int),
        )))),
        var: "k".into(),
        body: Shared::new(body),
    }
}

/// `g = (k in {0, …, n-1}) -> ((y) -> y + k); h = (k in g) -> g[k](1); h >< (+)`: the kernel
/// makes a family of n functions, which comes back as a held value of n closures the kernel
/// made (`alloc_made`, row FAIL-native-fam-result-holds-function), then reads and applies
/// each in a second kernel call, which makes the family again once (`Lets::held`). The sum is
/// n + n (n - 1) / 2. Small instances: `held_values::closures_a_kernel_call_made_read_their_
/// own_held_values_in_a_later_call`.
fn made_functions(n: usize) -> Term {
    let make = over(n, lam(&["y"], prim(Prim::Add, vec![var("y"), var("k")])));
    let apply = Term::Fam {
        domain: Shared::new(var("g")),
        var: "k".into(),
        body: Shared::new(app(app(var("g"), vec![var("k")]), vec![lit(1i64)])),
    };
    let sum = Term::Fold {
        family: Shared::new(apply),
        op: Shared::new(Term::PrimFn(Prim::Add)),
        identity: Some(Shared::new(lit(0i64))),
        depth: 1,
        ev: Default::default(),
    };
    let_("g", make, sum)
}

/// `f = (y) -> y; t = (f, 1); u = (k in {0, …, n-1}) -> t; count(u)`: a family the kernel makes
/// with one held tuple at each of n keys, one cell in native code and in the machine. Small
/// instance: `held_values::a_held_tuple_at_each_key_of_a_family_is_one_cell`.
fn one_held_at_each_key(n: usize) -> Term {
    let t = prim(Prim::Tuple, vec![var("f"), lit(1i64)]);
    let_(
        "f",
        lam(&["y"], var("y")),
        let_(
            "t",
            t,
            let_("u", over(n, var("t")), prim(Prim::Count, vec![var("u")])),
        ),
    )
}

/// `make(n)` and `make(8n)`, planned first, run by the counting machine and by native code,
/// each checked to give `want(n)`.
fn check_both(what: &str, n: usize, make: fn(usize) -> Term, want: fn(usize) -> Value) {
    scaling::on_a_thread(1 << 29, || {
        let (small, large) = (planned(&make(n)), planned(&make(scaling::FACTOR * n)));
        let at = |m: usize| if m == n { &small } else { &large };
        scaling::check(&format!("{what}, the counting machine"), n, |m| {
            let (g, p) = at(m);
            let (v, _) = memory::run(g.graph(), p, &mut Evaluator::new(World::new())).unwrap();
            assert_eq!(v, want(m));
        });
        scaling::check(&format!("{what}, native code"), n, |m| {
            let (g, p) = at(m);
            let o = zed_native::run(g, p, &mut Evaluator::new(World::new())).unwrap();
            assert_eq!(o.value, want(m));
        });
    })
}

/// A family of n functions the kernel makes, then reads and applies: O(n) in each back end.
#[test]
fn a_family_of_functions_the_kernel_makes_is_read_and_applied_in_linear_time() {
    check_both(
        "a family of n functions made in the kernel, read and applied",
        2_000,
        made_functions,
        |n| Value::Int((n + n * (n - 1) / 2) as i64),
    );
}

/// One held tuple at each of n keys of a family the kernel makes: O(n), where making the tuple
/// again at each key, as the machine did, made n cells.
#[test]
fn one_held_tuple_at_each_key_of_a_family_scales() {
    check_both(
        "one held tuple at each of n keys of a family made in the kernel",
        5_000,
        one_held_at_each_key,
        |n| Value::Int(n as i64),
    );
}
