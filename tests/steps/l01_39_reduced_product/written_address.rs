//! Written constraints are kept by content address (DESIGN.md sec:domains; QUESTIONS W6; step
//! KEY-written-addr): two constraints that differ only in the names of their binders are one
//! constraint, two that differ in anything else stay two, and the key costs the distinct parts
//! of a term, not its printed text, which grows with each path through its shared parts.

use std::sync::Arc;

use zed_kernel::term::build::{app, lam, lit, prim, var};
use zed_kernel::{Prim, Shared, Term};
use zedc::store::product::Scope;

use super::ints;
use zed_tests::scaling;

/// `((x) -> x < k)(n)`, its binder named `x`.
fn below(x: &str, k: i64) -> Term {
    app(
        lam(&[x], prim(Prim::Lt, vec![var(x), lit(k)])),
        vec![var("n")],
    )
}

/// The scope of `n` with each of `cs` written, in order, and reduced.
fn written(cs: &[Term]) -> Scope {
    let mut s = ints(&["n".into()]);
    for c in cs {
        s.write(c.clone());
    }
    s.reduce();
    s
}

#[test]
fn one_text_written_twice_is_one_constraint() {
    let s = written(&[below("x", 5), below("x", 5)]);
    assert_eq!(s.written.len(), 1);
    assert_eq!(s, written(&[below("x", 5)]));
}

#[test]
fn one_address_with_other_binder_names_is_one_constraint() {
    let (a, b) = (below("x", 5), below("y", 5));
    assert_ne!(a.to_string(), b.to_string(), "the two print apart");
    let s = written(&[a.clone(), b.clone()]);
    assert_eq!(s.written.len(), 1);
    // The scope does not depend on which of the names was written, or on the order.
    assert_eq!(s, written(std::slice::from_ref(&a)));
    assert_eq!(s, written(std::slice::from_ref(&b)));
    assert_eq!(s, written(&[b, a]));
}

#[test]
fn other_addresses_stay_two_constraints() {
    // Another literal.
    assert_eq!(written(&[below("x", 5), below("x", 6)]).written.len(), 2);
    // Another free name: `((x) -> x < 5)(m)` is not `((x) -> x < 5)(n)`.
    let on_m = app(
        lam(&["x"], prim(Prim::Lt, vec![var("x"), lit(5)])),
        vec![var("m")],
    );
    let mut s = ints(&["n".into(), "m".into()]);
    s.write(below("x", 5));
    s.write(on_m);
    assert_eq!(s.written.len(), 2);
    // A binder read where a free name was: `((x) -> x < n)(n)` is not `((x) -> n < n)(n)`.
    let reads_x = app(
        lam(&["x"], prim(Prim::Lt, vec![var("x"), var("n")])),
        vec![var("n")],
    );
    let reads_n = app(
        lam(&["x"], prim(Prim::Lt, vec![var("n"), var("n")])),
        vec![var("n")],
    );
    assert_eq!(written(&[reads_x, reads_n]).written.len(), 2);
}

/// `k` constraints `((x{i}) -> x{i} < i)(n)`, each with a binder name of its own, and the
/// same `k` again with the binders renamed: `k` constraints in all.
fn renamed_pairs(k: usize) -> Vec<Term> {
    (0..k)
        .flat_map(|i| {
            [
                below(&format!("x{i}"), i as i64),
                below(&format!("y{i}"), i as i64),
            ]
        })
        .collect()
}

/// `((x) -> t_d < 5)(n)`, where `t_0` is `x` and `t_{i + 1}` is `t_i(t_i())`, each `t_i` held
/// in one node: `d` nodes and `2^d` paths, so its printed text has some `2^d` names.
fn doubled(x: &str, d: usize) -> Term {
    let mut t = var(x);
    for _ in 0..d {
        let s = Shared::new(t);
        t = Term::App(s.clone(), vec![Term::App(s, vec![])]);
    }
    app(lam(&[x], prim(Prim::Lt, vec![t, lit(5)])), vec![var("n")])
}

#[test]
fn writing_scales_with_the_constraints_and_the_parts() {
    // `2k` constraints that are `k` addresses: the writes cost about `k log k`. The scope and
    // the constraints are built before the timing.
    let base = ints(&["n".into()]);
    let built = scaling::inputs(256, renamed_pairs);
    scaling::check("2k written constraints, k addresses", 256, |k| {
        let mut s = base.clone();
        for c in &built[&k] {
            s.write(c.clone());
        }
        assert_eq!(s.written.len(), k);
    });
    // Two constraints of `d` shared parts each, alike up to their binder name: the key costs
    // `d`, where the printed text has `2^d` names.
    let built = scaling::inputs(16, |d| [doubled("x", d), doubled("y", d)]);
    scaling::check("a written constraint of d shared parts", 16, |d| {
        let mut s = base.clone();
        for c in &built[&d] {
            s.write(c.clone());
        }
        assert_eq!(s.written.len(), 1);
    });
}

#[test]
fn a_written_constraint_keeps_its_free_names() {
    let mut s = ints(&["n".into()]);
    s.write(below("x", 5));
    let names: Vec<&Vec<Arc<str>>> = s.written.values().collect();
    assert_eq!(names, [&vec![Arc::<str>::from("n")]]);
}
