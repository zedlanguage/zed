//! Building a syntax tree is of order n log n in the length of the text, and its depth is
//! bounded by memory alone (DESIGN.md Part G). Each text is lexed and parsed before timing, so
//! the checks time the building alone.

use zed_tests::scaling::{check, inputs};
use zed_tests::trees::parsed;
use zedc::ast::{ExprKind, UnaryOp, build};

#[test]
fn a_long_chain_scales() {
    let built = inputs(200, |n| {
        parsed(format!("x{}", ".f(a, b: c)[i]?.g".repeat(n)), "Expr")
    });
    check("building a chain of 4n links", 200, |n| {
        let (text, tokens, tree) = &built[&n];
        let e = build(text, tokens, tree).unwrap();
        assert!(matches!(e.kind, ExprKind::Member { .. }));
    });
}

#[test]
fn deep_nesting_scales() {
    let built = inputs(500, |n| {
        parsed(format!("{}1{}", "f((-".repeat(n), "))".repeat(n)), "Expr")
    });
    check("building calls and negations nested n deep", 500, |n| {
        let (text, tokens, tree) = &built[&n];
        let e = build(text, tokens, tree).unwrap();
        let (mut e, mut depth) = (&e, 0);
        while let ExprKind::Call { positional, .. } = &e.kind
            && let [arg] = positional.as_slice()
            && let ExprKind::Unary(UnaryOp::Neg, inner) = &arg.kind
        {
            (e, depth) = (inner, depth + 1);
        }
        assert_eq!(depth, n);
        assert!(matches!(&e.kind, ExprKind::Int { digits, .. } if digits.as_str() == "1"));
    });
}

#[test]
fn nested_string_holes_scale() {
    let built = inputs(100, |n| {
        parsed(format!("{}1{}", "\"${".repeat(n), "}\"".repeat(n)), "Expr")
    });
    check("building string holes nested n deep", 100, |n| {
        let (text, tokens, tree) = &built[&n];
        let e = build(text, tokens, tree).unwrap();
        assert!(matches!(e.kind, ExprKind::Str(_)));
    });
}
