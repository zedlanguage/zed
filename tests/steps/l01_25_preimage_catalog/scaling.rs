//! The transfer's time against the size of the term (the rule of low complexity, DESIGN.md
//! Part G): a name bound once is followed once however often it is read, and a test in guard
//! position is transferred once for each outcome.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::preimage::{Demand, preimage};

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
}

/// The call depth counts calls, not the nesting of terms: a chain of `let`s of any length up
/// to 64 is followed to the end and memoized, never cut. The old count cut every chain of 22
/// or more, ran out of the transfer's budget and fell back on enumeration.
#[test]
fn a_long_chain_of_lets_is_not_cut() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    for k in 1..=64 {
        let p = preimage(&doubling(k), &ds, &Demand::Bool(true));
        assert_eq!(shown(&p), "i [0..=50]; exact", "a chain of {k} `let`s");
    }
}
