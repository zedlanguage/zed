//! A pattern may reach below a constant that a counted cell holds, as when a config table of
//! literals is paired with a computed value. Constants are not counted, so the fused release
//! stops at the constant and writes no count, as the counting machine does; the kernel, the
//! machine and native code agree with fusion and without it.

use std::sync::Arc;
use zed_kernel::Shared;

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Evaluator, Pattern, Prim, Term, Value, World};
use zedc::zir::lower::lower;
use zedc::zir::memory::{plan, run};

use super::kernel;

fn bind(x: &str) -> Pattern {
    Pattern::Bind(x.into())
}

/// `(1, "x")`, a constant.
fn limits() -> Term {
    lit(Value::tuple(vec![Value::Int(1), Value::str("x")]))
}

/// A cell holding the constant `limits()` and a computed part.
fn row() -> Term {
    prim(
        Prim::Tuple,
        vec![limits(), prim(Prim::Add, vec![lit(1), lit(1)])],
    )
}

/// `let q = row in match (q, q) { (((_, b), _), _) => b }`: the outer pair is unique, the
/// row shared, and `b` lies below the constant.
fn below_a_constant_in_a_shared_cell() -> Term {
    let p = Pattern::Tuple(vec![
        Pattern::Tuple(vec![
            Pattern::Tuple(vec![Pattern::Wild, bind("b")]),
            Pattern::Wild,
        ]),
        Pattern::Wild,
    ]);
    let_(
        "q",
        row(),
        Term::Match(
            Shared::new(prim(Prim::Tuple, vec![var("q"), var("q")])),
            vec![(p, var("b"))],
        ),
    )
}

/// `t` gives `want` in the kernel, and in the machine and native code with fusion and
/// without, the two with the same counts.
fn agrees(t: &Term, want: Value) {
    assert_eq!(kernel(t).unwrap(), want);
    for fuse in [true, false] {
        let g = Arc::new(lower(t).unwrap());
        let p = plan(&g, fuse);
        let (v, s) = run(&g, &p, &mut Evaluator::new(World::new())).unwrap();
        let o = zed_native::run(&g, &p, &mut Evaluator::new(World::new())).unwrap();
        assert_eq!((&v, &o.value), (&want, &want), "fuse {fuse}");
        assert_eq!(
            (o.stats.increments, o.stats.decrements, o.stats.frees),
            (s.increments, s.decrements, s.frees),
            "fuse {fuse}"
        );
    }
}

#[test]
fn a_binder_below_a_constant_in_a_shared_cell() {
    agrees(&below_a_constant_in_a_shared_cell(), Value::str("x"));
}

#[test]
fn a_binder_beside_a_constant_in_a_shared_cell() {
    // The other binder keeps its reference to the shared row's computed part.
    let p = Pattern::Tuple(vec![
        Pattern::Tuple(vec![
            Pattern::Tuple(vec![bind("a"), Pattern::Wild]),
            bind("n"),
        ]),
        Pattern::Wild,
    ]);
    let body = prim(Prim::Tuple, vec![var("a"), var("n")]);
    let t = let_(
        "q",
        row(),
        Term::Match(
            Shared::new(prim(Prim::Tuple, vec![var("q"), var("q")])),
            vec![(p, body)],
        ),
    );
    agrees(&t, Value::tuple(vec![Value::Int(1), Value::Int(2)]));
}

#[test]
fn a_binder_below_a_constant_in_a_unique_cell() {
    let p = Pattern::Tuple(vec![
        Pattern::Tuple(vec![Pattern::Wild, bind("b")]),
        Pattern::Wild,
    ]);
    let t = Term::Match(Shared::new(row()), vec![(p, var("b"))]);
    agrees(&t, Value::str("x"));
}

#[test]
fn a_binder_below_a_constant_atom_in_a_shared_cell() {
    // An atom's payload is reached the same way as a tuple's parts.
    let some = lit(Value::atom_with("some", vec![Value::str("x")]));
    let q = prim(
        Prim::Tuple,
        vec![some, prim(Prim::Add, vec![lit(1), lit(1)])],
    );
    let p = Pattern::Tuple(vec![
        Pattern::Tuple(vec![
            Pattern::Atom("some".into(), vec![bind("b")]),
            Pattern::Wild,
        ]),
        Pattern::Wild,
    ]);
    let t = let_(
        "q",
        q,
        Term::Match(
            Shared::new(prim(Prim::Tuple, vec![var("q"), var("q")])),
            vec![(p, var("b"))],
        ),
    );
    agrees(&t, Value::str("x"));
}
