//! `&&`, `||` and `if` with a failing operand under the machine (SPEC-and-or-failing-operand).
//! The surface `a && b` elaborates to `if a { b } else { false }` and `a || b` to
//! `if a { true } else { b }` (DESIGN.md sec:grammar, *Kernel desugaring*), so a failing left
//! operand fails the term, and a failing right one fails it only where the left one is `true`
//! for `&&` and `false` for `||` (DESIGN.md sec:failure). The kernel's own `and` and `or`
//! primitives, which no source text writes, read both operands and give the atom of either
//! (DESIGN.md step L1.25). The machine gives the kernel's value on each and frees every cell.

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zedc::zir::memory;

use super::planned;

/// `(5 div y) > 0`: `#divByZero` where `y` is 0, `true` where `y` is 1.
fn d() -> Term {
    prim(
        Prim::Gt,
        vec![prim(Prim::IntDiv, vec![lit(5), var("y")]), lit(0)],
    )
}

/// The surface `a && b`, as the elaborator writes it.
fn and(a: Term, b: Term) -> Term {
    if_(a, b, lit(false))
}

/// The surface `a || b`, as the elaborator writes it.
fn or(a: Term, b: Term) -> Term {
    if_(a, lit(true), b)
}

/// `t` with `y` bound to `y`, run by the kernel and by the machine with and without fusion:
/// the value shown, the same in all three.
fn value(t: &Term, y: i64) -> String {
    let t = let_("y", lit(y), t.clone());
    let kernel = Evaluator::new(World::new()).run(&t).unwrap().to_string();
    for fuse in [true, false] {
        let (g, p) = planned(&t, fuse);
        let (v, s) = memory::run(&g, &p, &mut Evaluator::new(World::new())).unwrap();
        assert_eq!(s.allocations, s.frees, "{t}, fused {fuse}: a cell left");
        assert_eq!(
            v.to_string(),
            kernel,
            "{t}, fused {fuse}: the kernel's value"
        );
    }
    kernel
}

#[test]
fn a_failing_operand_fails_and_or_only_where_it_is_taken() {
    let (f, t) = (|| lit(false), || lit(true));
    let fail = "#divByZero";
    let cases: Vec<(&str, Term, &str, &str)> = vec![
        ("false && d", and(f(), d()), "false", "false"),
        ("true && d", and(t(), d()), fail, "true"),
        ("d && false", and(d(), f()), fail, "false"),
        ("d && true", and(d(), t()), fail, "true"),
        ("true || d", or(t(), d()), "true", "true"),
        ("false || d", or(f(), d()), fail, "true"),
        ("d || true", or(d(), t()), fail, "true"),
        ("d || false", or(d(), f()), fail, "true"),
        (
            "if true { 1 } else { 5 div y }",
            if_(t(), lit(1), prim(Prim::IntDiv, vec![lit(5), var("y")])),
            "1",
            "1",
        ),
        (
            "if false { 5 div y } else { 1 }",
            if_(f(), prim(Prim::IntDiv, vec![lit(5), var("y")]), lit(1)),
            "1",
            "1",
        ),
        ("if d { 1 } else { 2 }", if_(d(), lit(1), lit(2)), fail, "1"),
        // `y != 0 && d`: the guard keeps `d` from being taken where it fails.
        (
            "y != 0 && d",
            and(prim(Prim::Ne, vec![var("y"), lit(0)]), d()),
            "false",
            "true",
        ),
        // The kernel primitives read both operands.
        (
            "and(false, d)",
            prim(Prim::And, vec![f(), d()]),
            fail,
            "false",
        ),
        (
            "and(d, false)",
            prim(Prim::And, vec![d(), f()]),
            fail,
            "false",
        ),
        ("or(true, d)", prim(Prim::Or, vec![t(), d()]), fail, "true"),
        ("or(d, true)", prim(Prim::Or, vec![d(), t()]), fail, "true"),
    ];
    for (case, term, at_zero, at_one) in cases {
        assert_eq!(value(&term, 0), at_zero, "{case} at y == 0");
        assert_eq!(value(&term, 1), at_one, "{case} at y == 1");
    }
    // Control: a failure value itself, not one made by an operation, behaves the same.
    let nope = || lit(Value::atom("nope"));
    assert_eq!(value(&and(lit(false), nope()), 0), "false");
    assert_eq!(value(&and(nope(), lit(false)), 0), "#nope");
}
