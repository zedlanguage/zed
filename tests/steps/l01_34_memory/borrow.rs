//! Borrow inference: a lambda's parameter is owned when some use consumes it and borrowed
//! otherwise, and a call passes each argument as the callee takes it when the plan sees the
//! callee, in its region or through captures, and owned otherwise.

use zed_kernel::Prim;
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zedc::zir::memory::Mode;

use super::{cat, machine};

#[test]
fn a_parameter_only_read_is_borrowed() {
    // `f = x -> len(x)`: `f(s)` lends `s`, which the pair then takes without a dup.
    let f = lam(&["x"], prim(Prim::Len, vec![var("x")]));
    let t = let_(
        "f",
        f,
        let_(
            "s",
            cat("a", "b"),
            prim(
                Prim::Tuple,
                vec![
                    app(var("f"), vec![var("s")]),
                    app(var("f"), vec![cat("c", "d")]),
                    var("s"),
                ],
            ),
        ),
    );
    let (v, s, p) = machine(&t);
    assert_eq!(v, r#"(2, 2, "ab")"#);
    assert_eq!(p.regions["r.0/0"].args, [Mode::Borrowed]);
    let call = &p.regions["r"].nodes[2];
    assert_eq!(call.callee.as_deref(), Some("r.0/0"));
    assert_eq!(call.modes, [Mode::Borrowed, Mode::Borrowed]);
    assert_eq!(s.increments, 0);
}

#[test]
fn a_parameter_consumed_is_owned() {
    // `g = x -> (x, 1)`: the pair consumes `x`, so `g(s)` gives `s` away; `s` is read again
    // after, so it gets a dup first, and its last reader drops it.
    let g = lam(&["x"], prim(Prim::Tuple, vec![var("x"), lit(1)]));
    let t = let_(
        "g",
        g,
        let_(
            "s",
            cat("a", "b"),
            prim(
                Prim::Tuple,
                vec![
                    app(var("g"), vec![var("s")]),
                    prim(Prim::Len, vec![var("s")]),
                ],
            ),
        ),
    );
    let (v, s, p) = machine(&t);
    assert_eq!(v, r#"(("ab", 1), 2)"#);
    assert_eq!(p.regions["r.0/0"].args, [Mode::Owned]);
    let call = &p.regions["r"].nodes[2];
    assert_eq!((call.modes[1], &call.dups[..]), (Mode::Owned, &[1][..]));
    assert_eq!(s.increments, 1);
}

#[test]
fn a_call_through_a_capture_sees_the_callee() {
    // The arm reaches `f` as a capture, and the plan follows it back to the lambda.
    let f = lam(&["x"], prim(Prim::Len, vec![var("x")]));
    let c = prim(Prim::Lt, vec![prim(Prim::Len, vec![var("s")]), lit(5)]);
    let t = let_(
        "f",
        f,
        let_(
            "s",
            cat("a", "b"),
            if_(c, app(var("f"), vec![var("s")]), lit(0)),
        ),
    );
    let (v, s, p) = machine(&t);
    assert_eq!(v, "2");
    let arm = &p.regions["r.4/0"];
    assert_eq!(arm.nodes[0].callee.as_deref(), Some("r.0/0"));
    assert_eq!(arm.nodes[0].modes, [Mode::Borrowed, Mode::Borrowed]);
    assert_eq!(s.increments, 0);
}

#[test]
fn an_unknown_callee_takes_its_arguments_owned() {
    // `ap = (h, y) -> h(y)` cannot see `h`, so it passes `y` owned and therefore owns `y`;
    // the lambda it is given only reads its parameter, and the call drops it after.
    let ap = lam(&["h", "y"], app(var("h"), vec![var("y")]));
    let len = lam(&["x"], prim(Prim::Len, vec![var("x")]));
    let t = let_("ap", ap, app(var("ap"), vec![len, cat("abc", "d")]));
    let (v, _, p) = machine(&t);
    assert_eq!(v, "4");
    let body = &p.regions["r.0/0"];
    assert_eq!(body.args, [Mode::Borrowed, Mode::Owned]);
    assert_eq!(body.nodes[0].callee, None);
    assert_eq!(body.nodes[0].modes, [Mode::Borrowed, Mode::Owned]);
}

#[test]
fn a_closure_holds_its_captures() {
    // `f = x -> x + len(s)` takes `s` into its cell at its last use, so `s` is never
    // counted; the closure's cell frees `s` when it goes.
    let f = lam(
        &["x"],
        prim(Prim::Add, vec![var("x"), prim(Prim::Len, vec![var("s")])]),
    );
    let t = let_(
        "s",
        cat("ab", "c"),
        let_(
            "f",
            f,
            prim(
                Prim::Tuple,
                vec![app(var("f"), vec![lit(1)]), app(var("f"), vec![lit(2)])],
            ),
        ),
    );
    let (v, s, p) = machine(&t);
    assert_eq!(v, "(4, 5)");
    assert_eq!(p.regions["r"].nodes[1].modes, [Mode::Owned]);
    assert_eq!(p.regions["r.1/0"].args, [Mode::Borrowed, Mode::Borrowed]);
    assert_eq!((s.increments, s.allocations, s.frees, s.peak), (0, 3, 3, 2));
}
