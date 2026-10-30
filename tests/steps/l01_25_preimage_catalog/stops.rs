//! Each kind of stop is reported, with the term it stopped at, and the preimage at a stop
//! keeps the whole domain, so it stays necessary.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc::store::preimage::{Demand, StopKind, preimage};

use super::{check, doms, function, pre, shown};

/// The preimage of `true` under `src` over `ds`, printed, after checking it on the window
/// `-150..=150`.
fn holds(src: &str, ds: &[(&str, Option<i64>, Option<i64>)]) -> String {
    let p = pre(src, ds, &Demand::Bool(true));
    let (_, body) = function(src);
    check(&body, &doms(ds), &Demand::Bool(true), &p, (-150, 150));
    shown(&p)
}

#[test]
fn a_string_operation_stops_the_transfer() {
    assert_eq!(
        holds("ok(x) = String(x) == \"12\";\n", &[("x", None, None)]),
        "x [..]; necessary; stop: string operation Show stops the transfer at String(x)"
    );
    // Below `len` the string stops it; the finite domain is then enumerated, and the stop is
    // still reported.
    assert_eq!(
        holds(
            "ok(x) = len(String(x)) <= 2;\n",
            &[("x", Some(-200), Some(200))]
        ),
        "x [-9..=99]; exact; enumerated; stop: string operation Show stops the transfer at \
         String(x)"
    );
    assert_eq!(
        holds("ok(x) = len(trim(String(x))) <= 2;\n", &[("x", None, None)]),
        "x [..]; necessary; stop: string operation Trim stops the transfer at trim(String(x))"
    );
}

#[test]
fn a_string_operation_on_constants_only_is_run() {
    assert_eq!(
        holds("ok(x) = x < len(String(1000));\n", &[("x", None, None)]),
        "x [..=3]; exact"
    );
}

#[test]
fn a_foreign_call_stops_the_transfer() {
    // `hash` is a foreign function: a name the term does not bind.
    let call = Term::App(
        Arc::new(Term::Var("hash".into())),
        vec![Term::Var("x".into())],
    );
    let t = Term::Prim(Prim::Lt, vec![call, Term::Lit(Value::Int(10))]);
    let p = preimage(&t, &doms(&[("x", None, None)]), &Demand::Bool(true));
    assert_eq!(
        shown(&p),
        "x [..]; necessary; stop: foreign name `hash` stops the transfer at hash(x)"
    );
    assert_eq!(p.stops[0].kind, StopKind::Foreign("hash".into()));
}

#[test]
fn a_term_outside_the_scalar_catalog_is_reported() {
    // `sum` of a tuple belongs to the catalog's tuple entries, not its scalar ones.
    let x = Term::Var("x".into());
    let tuple = Term::Prim(Prim::Tuple, vec![x, Term::Lit(Value::Int(1))]);
    let t = Term::Prim(
        Prim::Lt,
        vec![Term::Prim(Prim::Sum, vec![tuple]), Term::Lit(Value::Int(5))],
    );
    let wide = preimage(&t, &doms(&[("x", None, None)]), &Demand::Bool(true));
    assert_eq!(
        shown(&wide),
        "x [..]; necessary; stop: no scalar catalog entry for sum((x, 1))"
    );
    assert_eq!(wide.stops[0].kind, StopKind::Outside);
    // On a finite domain the enumeration decides it, and the stop is still reported.
    let ds = doms(&[("x", Some(-10), Some(10))]);
    let p = preimage(&t, &ds, &Demand::Bool(true));
    check(&t, &ds, &Demand::Bool(true), &p, (-10, 10));
    assert_eq!(
        shown(&p),
        "x [-10..=3]; exact; enumerated; stop: no scalar catalog entry for sum((x, 1))"
    );
}

#[test]
fn a_length_under_arithmetic_is_read_through_to_its_stop() {
    assert_eq!(
        holds("ok(x) = len(String(x)) + 1 <= 3;\n", &[("x", None, None)]),
        "x [..]; necessary; stop: string operation Show stops the transfer at String(x)"
    );
}

#[test]
fn a_call_that_never_returns_stops_at_the_call_depth() {
    // `w(w) >= x` with `w = \g. g(g)`: each call makes another, so only the call depth ends
    // the transfer.
    let g = || Term::Var("g".into());
    let w = Term::Lam(
        vec!["g".into()],
        Arc::new(Term::App(Arc::new(g()), vec![g()])),
    );
    let t = Term::Prim(
        Prim::Ge,
        vec![
            Term::App(Arc::new(w.clone()), vec![w]),
            Term::Var("x".into()),
        ],
    );
    let p = preimage(&t, &doms(&[("x", None, None)]), &Demand::Bool(true));
    assert!(!p.exact, "{}", shown(&p));
    assert!(
        p.stops.iter().any(|s| s.kind == StopKind::Outside),
        "{}",
        shown(&p)
    );
}
