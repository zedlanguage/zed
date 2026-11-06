//! Building blocks is of order n log n in the length of the text, and the depth of their
//! nesting is bounded by memory alone (DESIGN.md Part G). Each text is lexed and parsed before
//! timing, so the checks time the building alone.

use zed_tests::scaling::{check, inputs};
use zed_tests::trees::parsed;
use zedc::ast::{ExprKind, StmtKind, build};

#[test]
fn a_long_block_scales() {
    let built = inputs(200, |n| {
        parsed(format!("x -> {{ {}x }}", "a, _ = x; ".repeat(n)), "Expr")
    });
    check("building a block of n statements", 200, |n| {
        let (text, tokens, tree) = &built[&n];
        let e = build(text, tokens, tree).unwrap();
        let ExprKind::Lambda { body, .. } = &e.kind else {
            panic!("a lambda")
        };
        let ExprKind::Block(stmts) = &body.kind else {
            panic!("a block")
        };
        let binds = stmts
            .iter()
            .filter(|s| matches!(s.kind, StmtKind::Bind { .. }))
            .count();
        assert_eq!(
            (binds, stmts.last().unwrap().to_string()),
            (n, "(return x)".into())
        );
    });
}

#[test]
fn nested_blocks_scale() {
    let built = inputs(200, |n| {
        parsed(
            format!("{}x{}", "x -> { y = 1; ".repeat(n), " }".repeat(n)),
            "Expr",
        )
    });
    check("building blocks nested n deep", 200, |n| {
        let (text, tokens, tree) = &built[&n];
        let e = build(text, tokens, tree).unwrap();
        let (mut e, mut depth) = (&e, 0);
        while let ExprKind::Lambda { body, .. } = &e.kind
            && let ExprKind::Block(stmts) = &body.kind
            && let [bind, ret] = stmts.as_slice()
            && let StmtKind::Bind { .. } = bind.kind
            && let StmtKind::Return(values) = &ret.kind
            && let [v] = values.as_slice()
        {
            (e, depth) = (v, depth + 1);
        }
        assert_eq!((depth, e.to_string()), (n, "x".into()));
    });
}
