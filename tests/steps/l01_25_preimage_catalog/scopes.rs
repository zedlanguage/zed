//! What a persistent scope, one memo per transfer and results by the inputs they narrow must
//! keep: the innermost binding of a name wins, a closure reads the parameter of the call that
//! made it, and a union of boxes is exact just when it is a box.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc::store::interval::IntervalSet;
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

fn bind(x: &str, e: Term, body: Term) -> Term {
    Term::Let(x.into(), Arc::new(e), Arc::new(body))
}

fn lam(x: &str, b: Term) -> Term {
    Term::Lam(vec![x.into()], Arc::new(b))
}

fn call(f: &str, a: Term) -> Term {
    Term::App(Arc::new(var(f)), vec![a])
}

fn at_least(x: &str, n: i64) -> Term {
    prim(Prim::Ge, var(x), int(n))
}

fn holds(t: &Term, ds: &[(&str, Option<i64>, Option<i64>)]) -> String {
    shown(&preimage(t, &doms(ds), &Demand::Bool(true)))
}

#[test]
fn a_binding_hides_an_outer_binding_of_its_name() {
    // `x = i + 1; x = x + 1; x >= 5`
    let t = bind(
        "x",
        prim(Prim::Add, var("i"), int(1)),
        bind("x", prim(Prim::Add, var("x"), int(1)), at_least("x", 5)),
    );
    assert_eq!(holds(&t, &[("i", Some(0), Some(10))]), "i [3..=10]; exact");
}

#[test]
fn a_binding_of_an_inputs_name_reads_the_input() {
    // `i = i + 1; i >= 5`
    let t = bind("i", prim(Prim::Add, var("i"), int(1)), at_least("i", 5));
    assert_eq!(holds(&t, &[("i", Some(0), Some(10))]), "i [4..=10]; exact");
}

#[test]
fn a_parameter_hides_an_input_of_its_name() {
    // `f = (i) -> i >= 3; f(j)`, with an input `i` that the term does not read.
    let t = bind("f", lam("i", at_least("i", 3)), call("f", var("j")));
    let ds = [("i", Some(0), Some(10)), ("j", Some(0), Some(10))];
    assert_eq!(holds(&t, &ds), "i [0..=10]; j [3..=10]; exact");
}

/// One function, reached from two calls whose arguments have different intervals: what is
/// remembered of the first must not answer for the second.
#[test]
fn a_closure_reads_the_parameter_of_the_call_that_made_it() {
    // `f = (a) -> { g = (b) -> a + b; g(1) }; f(i) <= 8 && f(i + 100) >= 105`
    let inner = bind(
        "g",
        lam("b", prim(Prim::Add, var("a"), var("b"))),
        call("g", int(1)),
    );
    let low = prim(Prim::Le, call("f", var("i")), int(8));
    let high = prim(
        Prim::Ge,
        call("f", prim(Prim::Add, var("i"), int(100))),
        int(105),
    );
    let t = bind("f", lam("a", inner), prim(Prim::And, low, high));
    assert_eq!(holds(&t, &[("i", Some(0), Some(10))]), "i [4..=7]; exact");
}

#[test]
fn a_union_of_boxes_is_exact_when_it_is_a_box() {
    let ds = [("x", Some(0), Some(9)), ("y", Some(0), Some(9))];
    let or = |a, b| prim(Prim::Or, a, b);
    let and = |a, b| prim(Prim::And, a, b);
    // Each box leaves the other input whole: their union is no box.
    let t = or(at_least("x", 1), at_least("y", 1));
    assert_eq!(holds(&t, &ds), "x [0..=9]; y [0..=9]; necessary");
    // One box lies within the other.
    let t = or(
        and(at_least("x", 1), at_least("y", 1)),
        and(at_least("x", 2), at_least("y", 2)),
    );
    assert_eq!(holds(&t, &ds), "x [1..=9]; y [1..=9]; exact");
    // The boxes differ in one input.
    let t = or(
        and(at_least("x", 1), at_least("y", 2)),
        and(at_least("x", 3), at_least("y", 2)),
    );
    assert_eq!(holds(&t, &ds), "x [1..=9]; y [2..=9]; exact");
    // One box narrows a name the other leaves whole, and is not within it.
    let t = or(at_least("x", 1), and(at_least("x", 0), at_least("y", 2)));
    assert_eq!(holds(&t, &ds), "x [0..=9]; y [0..=9]; necessary");
}

#[test]
fn an_empty_input_leaves_no_point() {
    let mut ds = doms(&[("i", Some(0), Some(9)), ("j", Some(0), Some(9))]);
    ds.insert("j".into(), IntervalSet::empty());
    let p = preimage(&at_least("i", 5), &ds, &Demand::Bool(true));
    assert_eq!(p.domains["i"], IntervalSet::empty());
    // A term that reads no input keeps the box, as it did.
    let p = preimage(&Term::Lit(Value::Bool(true)), &ds, &Demand::Bool(true));
    assert!(!p.domains["i"].is_empty() && p.domains["j"].is_empty() && p.exact);
}
