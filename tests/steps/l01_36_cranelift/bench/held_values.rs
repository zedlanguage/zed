//! A tuple that holds a function is a cell whose parts are counted references, as a tuple of
//! data is (row FIX-functions-in-tuples): building, matching and reading one costs its number
//! of parts, whatever the parts hold, so `n` of them run in O(n). The small instances are in
//! `held_values.rs`.

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Pattern, Prim, Shared, Term, World};

use super::scaling::check_run;
use crate::function_binders::{bind, calls, match1};
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
