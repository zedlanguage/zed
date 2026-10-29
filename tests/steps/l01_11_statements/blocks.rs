//! A block binds names and ends in its export.

use zedc::ast::{ExprKind, StmtKind, Target};

use super::check;

#[test]
fn bindings_and_the_trailing_expression() {
    check(&[
        (
            "xs -> { n = xs.len; total = xs.sum; total / n }",
            "(fn (xs) (block (= (n) (. xs len)) (= (total) (. xs sum)) (return (/ total n))))",
        ),
        (
            "p -> { lo, hi = p.bounds; hi - lo }",
            "(fn (p) (block (= (lo hi) (. p bounds)) (return (- hi lo))))",
        ),
        (
            "p -> { _, hi = p.bounds; hi }",
            "(fn (p) (block (= (_ hi) (. p bounds)) (return hi)))",
        ),
        (
            "parse(s) else { 0 }",
            "(else (call parse s) (block (return 0)))",
        ),
        (
            "f(x -> { y = x * 2; y + 1 })",
            "(call f (fn (x) (block (= (y) (* x 2)) (return (+ y 1)))))",
        ),
        // Statement order has no meaning, so a binding may follow the export.
        ("x -> { y + 1; y = x }", "syntax"),
        (
            "x -> { return y + 1; y = x * 2; }",
            "(fn (x) (block (return (+ y 1)) (= (y) (* x 2))))",
        ),
    ]);
}

#[test]
fn the_semicolon_rule() {
    check(&[
        // A statement without its `;` does not parse.
        ("x -> { y = x y }", "syntax"),
        // The trailing expression takes none; an expression statement is layer L6.
        (
            "x -> { y = x; y; }",
            "error: this form (Decl) is built from layer L6",
        ),
        // A brace holding only an expression is a display (`{ x }` is a set), not a block.
        (
            "({ x })",
            "error: this form (Primary) is built from layer L2",
        ),
    ]);
}

#[test]
fn a_block_exports_exactly_once() {
    check(&[
        (
            "x -> { return x; x + 1 }",
            "error: a block exports once; its export is already at byte 7",
        ),
        (
            "x -> { return x; return x + 1; }",
            "error: a block exports once; its export is already at byte 7",
        ),
        (
            "x -> { y = x * 2; return y; y + 1 }",
            "error: a block exports once; its export is already at byte 18",
        ),
        (
            "x -> { y = x; }",
            "error: this block exports nothing: end it with an expression or `return e;`",
        ),
    ]);
}

#[test]
fn a_statement_of_a_later_step_names_that_step() {
    check(&[
        (
            "x -> { sq(v) = v * v; sq(x) }",
            "error: this form (Function) is built from step L1.12",
        ),
        (
            "x -> { out <- x; x }",
            "error: this form (Push) is built from step L1.12",
        ),
        (
            "x -> { n: int = x; n }",
            "error: this form (Binding) is built from layer L10",
        ),
        (
            "x -> { y = x with z = 1; y }",
            "error: this form (Boundary) is built from layer L6",
        ),
        (
            "x -> { local y = x; y }",
            "error: this form (Decl) is built from layer L2",
        ),
    ]);
}

#[test]
fn a_wildcard_target_binds_nothing() {
    let text = "p -> { _, hi = p.bounds; hi }";
    let tokens = zedc::lex::lex(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Expr", zedc::parse::TOP).unwrap();
    let ExprKind::Lambda { body, .. } = zedc::ast::build(text, &tokens, &tree).unwrap().kind else {
        panic!("a lambda");
    };
    let ExprKind::Block(stmts) = body.kind else {
        panic!("a block");
    };
    let StmtKind::Bind { targets, .. } = &stmts[0].kind else {
        panic!("a binding");
    };
    assert_eq!(targets, &[Target::Wild, Target::Name("hi".into())]);
    assert_eq!(
        &text[stmts[0].span.start..stmts[0].span.end],
        "_, hi = p.bounds;"
    );
}
