//! The transfer's time against the size of the term (the rule of low complexity, DESIGN.md
//! Part G): a name bound once is followed once however often it is read, and a test in guard
//! position is transferred once for each outcome.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::preimage::{Classes, Demand, exact_preimage, preimage};

use super::{doms, shown};

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

/// `x1 = i + i; x2 = x1 + x1; …; xk >= 0`: each name read twice.
fn doubling(k: usize) -> Term {
    let mut body = prim(Prim::Ge, var(&format!("x{k}")), int(0));
    for i in (1..=k).rev() {
        let prev = if i == 1 {
            "i".to_string()
        } else {
            format!("x{}", i - 1)
        };
        let e = prim(Prim::Add, var(&prev), var(&prev));
        body = Term::Let(format!("x{i}").into(), Arc::new(e), Arc::new(body));
    }
    body
}

/// `f0 = (v) -> v; f1 = (v) -> max(f0(v), f0(v + d)); …; fk(i) >= 0`: each function calls
/// the one before it twice, with arguments that differ when `d` is 1 and agree when it is 0.
fn calls(k: usize, d: i64) -> Term {
    let call = |j: usize, a: Term| Term::App(Arc::new(var(&format!("f{j}"))), vec![a]);
    let mut body = prim(Prim::Ge, call(k, var("i")), int(0));
    for j in (0..=k).rev() {
        let e = if j == 0 {
            var("v")
        } else {
            let second = if d == 0 {
                var("v")
            } else {
                prim(Prim::Add, var("v"), int(d))
            };
            prim(Prim::Max, call(j - 1, var("v")), call(j - 1, second))
        };
        let f = Term::Lam(vec!["v".into()], Arc::new(e));
        body = Term::Let(format!("f{j}").into(), Arc::new(f), Arc::new(body));
    }
    body
}

fn calls_apart(k: usize) -> Term {
    calls(k, 1)
}

fn calls_alike(k: usize) -> Term {
    calls(k, 0)
}

/// `if (if (… i >= 3 …) { i >= 1 } else { i <= -1 }) { i >= 0 } else { i <= 0 }`: each
/// branch's guard is the branch before it.
fn guards(k: usize) -> Term {
    let mut g = prim(Prim::Ge, var("i"), int(3));
    for j in 0..k as i64 {
        let (a, b) = (
            prim(Prim::Ge, var("i"), int(j)),
            prim(Prim::Le, var("i"), int(-j)),
        );
        g = Term::If(Arc::new(g), Arc::new(a), Arc::new(b));
    }
    g
}

/// `i >= 0 && i >= 1 && … && i >= k - 1`.
fn conjunction(k: usize) -> Term {
    (1..k as i64).fold(prim(Prim::Ge, var("i"), int(0)), |a, j| {
        prim(Prim::And, a, prim(Prim::Ge, var("i"), int(j)))
    })
}

#[test]
fn preimages_within_the_depth_are_exact() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let cases = [
        (doubling(6), "i [0..=50]; exact"),
        (guards(6), "i [5..=50]; exact"),
        (conjunction(6), "i [5..=50]; exact"),
    ];
    for (t, want) in cases {
        assert_eq!(shown(&preimage(&t, &ds, &Demand::Bool(true))), want, "{t}");
    }
}

#[test]
fn the_transfer_scales() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let ds = &ds;
    let run = |make: fn(usize) -> Term| {
        move |k: usize| {
            preimage(&make(k), ds, &Demand::Bool(true));
        }
    };
    scaling::check("a chain of `let`s, each name read twice", 6, run(doubling));
    scaling::check("branches nested in guard position", 6, run(guards));
    scaling::check("a conjunction of tests", 8, run(conjunction));
    scaling::check(
        "functions each calling the one before twice, alike",
        6,
        run(calls_alike),
    );
    scaling::check(
        "functions each calling the one before twice, apart",
        6,
        run(calls_apart),
    );
}

/// A function is summarized once for each abstraction of its arguments, so a chain of
/// functions each calling the one before twice is read in time linear in its length, not
/// exponential; and the preimage is still exact.
#[test]
fn nested_calls_are_summarized() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    for k in [1, 2, 5, 20, 48] {
        let p = preimage(&calls_alike(k), &ds, &Demand::Bool(true));
        assert_eq!(
            shown(&p),
            "i [0..=50]; exact",
            "{k} functions, arguments alike"
        );
        let p = preimage(&calls_apart(k), &ds, &Demand::Bool(true));
        let lo = -(k as i64).min(50);
        assert_eq!(
            shown(&p),
            format!("i [{lo}..=50]; exact"),
            "{k} functions, apart"
        );
    }
}

/// A chain of `let`s is followed to the end and memoized, never cut. An old count of nested
/// terms cut every chain of 22 or more and fell back on enumeration.
#[test]
fn a_long_chain_of_lets_is_not_cut() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    for k in 1..=64 {
        let p = preimage(&doubling(k), &ds, &Demand::Bool(true));
        assert_eq!(shown(&p), "i [0..=50]; exact", "a chain of {k} `let`s");
    }
}

/// `x * x mod 10 == 9` with `x` in `0..=n`, and `x * y mod 7 == 3` with each in `1..=n`.
fn squares(n: usize) -> (Term, zedc::store::preimage::Domains) {
    let sq = prim(Prim::Mul, var("x"), var("x"));
    let t = prim(Prim::Eq, prim(Prim::Mod, sq, int(10)), int(9));
    (t, doms(&[("x", Some(0), Some(n as i64))]))
}

fn products(n: usize) -> (Term, zedc::store::preimage::Domains) {
    let xy = prim(Prim::Mul, var("x"), var("y"));
    let t = prim(Prim::Eq, prim(Prim::Mod, xy, int(7)), int(3));
    let n = Some(n as i64);
    (t, doms(&[("x", Some(1), n), ("y", Some(1), n)]))
}

/// `x * y <= n` with each in `1..=n`: the plain preimage is exact on every sub-box under or
/// over the curve, so only the boxes the curve crosses are split.
fn hyperbola(n: usize) -> (Term, zedc::store::preimage::Domains) {
    let t = prim(Prim::Le, prim(Prim::Mul, var("x"), var("y")), int(n as i64));
    let n = Some(n as i64);
    (t, doms(&[("x", Some(1), n), ("y", Some(1), n)]))
}

/// Under `@exact` the search visits fewer than twice as many boxes as there are points in
/// the domain, each in time of the size of the term, so its time is of the order of the
/// number of points: `n` for one input in `0..=n`, `n^2` for two; and where the plain
/// preimage is exact on sub-boxes, of the boxes the boundary crosses: `n` for `x * y <= n`.
#[test]
fn the_exact_search_scales_with_the_number_of_points() {
    let run = |make: fn(usize) -> (Term, zedc::store::preimage::Domains)| {
        move |n: usize| {
            let (t, ds) = make(n);
            exact_preimage(&t, &ds, &Classes::new(), &Demand::Bool(true));
        }
    };
    scaling::check(
        "`x * x mod 10 == 9` over `0..=n` under `@exact`",
        256,
        run(squares),
    );
    scaling::check_order(
        "`x * y mod 7 == 3` over `1..=n` squared under `@exact`",
        16,
        2,
        run(products),
    );
    scaling::check(
        "`x * y <= n` over `1..=n` squared under `@exact`",
        64,
        run(hyperbola),
    );
}
