//! The planner asks of a region under a node whether it consumes an argument, how a lambda body
//! takes its parameters, and which lambda a captured argument is; it keeps each answer by the
//! region's occurrence, so a branch nested `d` deep or a function captured `d` regions down is
//! asked about once, and planning is linear (T12-Z4, COMPLEXITY.md Z4). The shapes are those of
//! design review Q10: nested `if`s reading `k` names, a chain of functions each calling the one
//! before twice, and a function called twice in each of `d` nested arms or lambdas.
//!
//! The plan finds a region from its parent's by index, not by its path from the root, so a nest
//! `d` deep plans in O(d) instructions and bytes (T14-paths).

use std::sync::Arc;

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, World};
use zedc::zir::lower::lower;
use zedc::zir::memory::{self, Mode};
use zedc::zir::{Op, Region};

use super::{cat, machine, planned, run};

/// `v0 = "a" ++ "v0"; …; v{k-1} = …;` then `if v0 == "av0" then … if v0 == "av0" then (v0, …,
/// v{k-1}) else "no" … else "no"`, the `if`s `d` deep: every then arm captures all `k` names,
/// and whether it consumes one asks the arm under it, down to the tuple.
pub(super) fn nest(k: usize, d: usize) -> Term {
    let names: Vec<String> = (0..k).map(|i| format!("v{i}")).collect();
    let mut t = prim(Prim::Tuple, names.iter().map(|n| var(n)).collect());
    for _ in 0..d {
        let c = prim(Prim::Eq, vec![var(&names[0]), lit("av0")]);
        t = if_(c, t, lit("no"));
    }
    for n in names.iter().rev() {
        t = let_(n, cat("a", n), t);
    }
    t
}

/// `f0 = (x) -> len(x)`, or `(x) -> len((x, 1).0)`, whose tuple consumes `x`, when
/// `consume_leaf`; `f{i} = (x) -> f{i-1}(x) + f{i-1}(x)` for `i` up to `d`; then
/// `f{d}("a" ++ "b")`: how each `f{i}` takes `x` is how `f0` does, asked twice per level.
pub(super) fn call_chain(d: usize, consume_leaf: bool) -> Term {
    let mut t = app(var(&format!("f{d}")), vec![cat("a", "b")]);
    for i in (1..=d).rev() {
        let prev = format!("f{}", i - 1);
        let twice = vec![
            app(var(&prev), vec![var("x")]),
            app(var(&prev), vec![var("x")]),
        ];
        t = let_(&format!("f{i}"), lam(&["x"], prim(Prim::Add, twice)), t);
    }
    let leaf = if consume_leaf {
        prim(
            Prim::TupleGet,
            vec![prim(Prim::Tuple, vec![var("x"), lit(1i64)]), lit(0i64)],
        )
    } else {
        var("x")
    };
    let_("f0", lam(&["x"], prim(Prim::Len, vec![leaf])), t)
}

/// `s = "a" ++ "b"; f = (x) -> len(x);` then `f` called twice at each of `d` levels, the levels
/// nested as the else arms of `if`s (`c{i} = f(s) + f(s); if s == "{i}" then … else c{i}`), or,
/// with `lambdas`, as the bodies of lambdas (`(p{i}) -> (f(s) + f(s), …)`): each call finds `f`
/// through the captures of every level above it.
pub(super) fn capture_chain(d: usize, lambdas: bool) -> Term {
    let mut t = app(var("f"), vec![var("s")]);
    for i in 0..d {
        let twice = vec![app(var("f"), vec![var("s")]), app(var("f"), vec![var("s")])];
        let call = prim(Prim::Add, twice);
        t = if lambdas {
            lam(
                &[format!("p{i}").as_str()],
                prim(Prim::Tuple, vec![call, t]),
            )
        } else {
            let x = format!("c{i}");
            let c = prim(Prim::Eq, vec![var("s"), lit(i.to_string().as_str())]);
            let_(&x, call, if_(c, t, var(&x)))
        };
    }
    let len = lam(&["x"], prim(Prim::Len, vec![var("x")]));
    let_("s", cat("a", "b"), let_("f", len, t))
}

/// `f`, `g` = a function that borrows its argument (`len(x)`) and one that consumes it
/// (`(x, 1)`), in the order `first_borrows` says; `w1 = (y) -> f(y); w2 = (y) -> g(y);
/// (w1("a" ++ "b"), w2("c" ++ "d"))`. The two wrappers have one body up to the hint naming
/// their capture, and take `y` as the function they call does.
fn wrappers(first_borrows: bool) -> Term {
    let borrow = lam(&["x"], prim(Prim::Len, vec![var("x")]));
    let consume = lam(&["x"], prim(Prim::Tuple, vec![var("x"), lit(1i64)]));
    let (f, g) = if first_borrows {
        (borrow, consume)
    } else {
        (consume, borrow)
    };
    let w = |f: &str| lam(&["y"], app(var(f), vec![var("y")]));
    let calls = vec![
        app(var("w1"), vec![cat("a", "b")]),
        app(var("w2"), vec![cat("c", "d")]),
    ];
    let_(
        "f",
        f,
        let_(
            "g",
            g,
            let_("w1", w("f"), let_("w2", w("g"), prim(Prim::Tuple, calls))),
        ),
    )
}

/// The kernel's value of `t`, printed.
fn kernel(t: &Term) -> String {
    Evaluator::new(World::new()).run(t).unwrap().to_string()
}

/// The path of the body of the `i`th lambda node of `g`'s root region.
pub(super) fn body_path(g: &Region, i: usize) -> String {
    let k = (0..g.nodes.len())
        .filter(|k| matches!(g.nodes[*k].op, Op::Lambda))
        .nth(i)
        .expect("the root region has that many lambdas");
    format!("r.{k}/0")
}

#[test]
fn a_call_chain_borrows_down_to_a_borrowing_leaf_and_owns_down_to_a_consuming_one() {
    for (consume_leaf, want) in [(false, Mode::Borrowed), (true, Mode::Owned)] {
        let t = call_chain(4, consume_leaf);
        let (g, p) = planned(&t, true);
        // `f0` to `f4` are the root's lambdas 0 to 4, and each takes `x`, its first argument, as
        // `f0` does; `f1` to `f4` also take the function they capture.
        assert_eq!(p[body_path(&g, 0).as_str()].args, [want]);
        for i in 1..=4 {
            assert_eq!(p[body_path(&g, i).as_str()].args[0], want, "f{i}");
        }
        let (v, _) = run(&g, &p).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(v, kernel(&t));
    }
    assert_eq!(kernel(&call_chain(4, false)), "32");
}

#[test]
fn capture_chains_borrow_the_captured_string_for_every_call() {
    // `f`'s body borrows `x`, so no call of `f` takes a count of `s`.
    let t = capture_chain(3, false);
    let (v, s, p) = machine(&t);
    assert_eq!(v, kernel(&t));
    assert_eq!(v, "4");
    let g = lower(&t).unwrap();
    assert_eq!(p[body_path(&g, 0).as_str()].args, [Mode::Borrowed]);
    assert_eq!(s.increments, 0);
    // The nested lambdas are planned, not run: the program's value is a function.
    let (g, p) = planned(&capture_chain(3, true), true);
    assert_eq!(p[body_path(&g, 0).as_str()].args, [Mode::Borrowed]);
    // The outer lambda's body takes its parameter and the captured `f` and `s`.
    assert_eq!(p[body_path(&g, 1).as_str()].args.len(), 3);
}

#[test]
fn nested_ifs_hand_each_name_owned_down_to_the_tuple() {
    let t = nest(4, 5);
    let (v, s, p) = machine(&t);
    assert_eq!(v, kernel(&t));
    assert_eq!(v, r#"("av0", "av1", "av2", "av3")"#);
    // Every then arm owns the four names it captures, since the tuple at the bottom takes them;
    // the names are never shared.
    let mut at = 0;
    for _ in 0..5 {
        let r = p.regions[at].nodes.iter().find_map(|n| n.regions.first());
        at = *r.expect("a then arm under the last");
        assert_eq!(p.regions[at].args, [Mode::Owned; 4], "{}", p.path(at));
    }
    assert_eq!(s.increments, 0);
}

/// Two wrappers with one body, calling a borrowing and a consuming function, once with a body
/// each and once sharing one body, as a pass that hash-conses regions would leave them, in both
/// orders: the plans are equal and each wrapper takes `y` as its callee does. A planner that kept
/// its answers by the body region rather than by its occurrence would give the second wrapper
/// the first one's modes (design review Q10).
#[test]
fn wrappers_sharing_one_body_take_their_argument_as_their_callee_does() {
    for first_borrows in [true, false] {
        let t = wrappers(first_borrows);
        let mut apart = lower(&t).unwrap();
        let (w1, w2) = (body_path(&apart, 2), body_path(&apart, 3));
        let ls: Vec<usize> = (0..apart.nodes.len())
            .filter(|k| matches!(apart.nodes[*k].op, Op::Lambda))
            .collect();
        let (first, second) = (ls[2], ls[3]);
        let body = &apart.nodes[first].regions[0];
        assert_eq!(body.nodes, apart.nodes[second].regions[0].nodes);
        apart.nodes[second].regions[0] = Arc::new(Region::clone(body));
        let mut shared = apart.clone();
        shared.nodes[second].regions[0] = Arc::clone(&shared.nodes[first].regions[0]);
        assert!(Arc::ptr_eq(
            &shared.nodes[first].regions[0],
            &shared.nodes[second].regions[0]
        ));
        let (borrows, consumes) = if first_borrows { (w1, w2) } else { (w2, w1) };
        for fuse in [true, false] {
            let (pa, ps) = (memory::plan(&apart, fuse), memory::plan(&shared, fuse));
            assert_eq!(ps, pa);
            assert_eq!(ps[borrows.as_str()].args[0], Mode::Borrowed);
            assert_eq!(ps[consumes.as_str()].args[0], Mode::Owned);
            let (va, sa) = run(&apart, &pa).unwrap_or_else(|e| panic!("{e}"));
            let (vs, ss) = run(&shared, &ps).unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(va, kernel(&t));
            assert_eq!((vs, ss), (va, sa));
        }
    }
}
