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
        // A binding may follow the export, which is stored last, where the formatter writes it
        // (step L1.13). A name is still used only below its definition (DESIGN.md
        // sec:lexical), which name resolution checks.
        ("x -> { y + 1; y = x }", "syntax"),
        (
            "x -> { y = x * 2; return y + 1; z = y; }",
            "(fn (x) (block (= (y) (* x 2)) (= (z) y) (return (+ y 1))))",
        ),
    ]);
}

#[test]
fn the_semicolon_rule() {
    check(&[
        // A statement without its `;` does not parse.
        ("x -> { y = x y }", "syntax"),
        // The trailing expression takes none: with one, it is an expression statement, and
        // the block exports nothing.
        (
            "x -> { y = x; y; }",
            "error: this block exports nothing, and a block gives a value, so it must export one. \
             End it with an expression, or with `return e;` to give the value `e`.",
        ),
        // A brace holding only an expression is a display (`{ x }` is a set), not a block.
        ("({ x })", "(set x)"),
    ]);
}

#[test]
fn a_block_exports_exactly_once() {
    check(&[
        (
            "x -> { return x; x + 1 }",
            "error: this block exports a second time, and a block exports one value, once. Remove one \
             of the two exports.; the block's first export at byte 7",
        ),
        (
            "x -> { return x; return x + 1; }",
            "error: this block exports a second time, and a block exports one value, once. Remove one \
             of the two exports.; the block's first export at byte 7",
        ),
        (
            "x -> { y = x * 2; return y; y + 1 }",
            "error: this block exports a second time, and a block exports one value, once. Remove one \
             of the two exports.; the block's first export at byte 18",
        ),
        (
            "x -> { y = x; }",
            "error: this block exports nothing, and a block gives a value, so it must export one. \
             End it with an expression, or with `return e;` to give the value `e`.",
        ),
    ]);
}

#[test]
fn a_statement_of_a_later_layer_is_refused_as_not_compiled_yet() {
    check(&[
        (
            "x -> { n: int = x; n }",
            concat!(
                "error: ",
                zed_tests::not_yet!("the binding with a declared type `n: int = x;`")
            ),
        ),
        (
            "x -> { y[x + 1] <- 1; y }",
            concat!(
                "error: ",
                zed_tests::not_yet!("the push at a key `y[x + 1] <- 1;`")
            ),
        ),
        // `local` builds from step L2.3; name resolution refuses it in a block.
        (
            "x -> { local y = x; y }",
            "(fn (x) (block (local (= (y) x)) (return y)))",
        ),
    ]);
}

#[test]
fn a_wildcard_target_binds_nothing() {
    let text = "p -> { _, hi = p.bounds; hi }";
    let tokens = zedc::lex::lex(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Expr", zedc::parse::TOP).unwrap();
    let e = zedc::ast::build(text, &tokens, &tree).unwrap();
    let ExprKind::Lambda { body, .. } = &e.kind else {
        panic!("a lambda");
    };
    let ExprKind::Block(stmts) = &body.kind else {
        panic!("a block");
    };
    let StmtKind::Bind { targets, .. } = &stmts[0].kind else {
        panic!("a binding");
    };
    let hi = zedc::lex::Span { start: 10, end: 12 };
    assert_eq!(&text[hi.start..hi.end], "hi");
    assert_eq!(targets, &[Target::Wild, Target::Name("hi".into(), hi)]);
    assert_eq!(
        &text[stmts[0].span.start..stmts[0].span.end],
        "_, hi = p.bounds;"
    );
}

/// The two forms of `if` (author, P348; DESIGN.md sec:tour_methods, "Statement position must
/// write something, and drop nothing"). The `if` statement stands among the statements of a
/// block, may leave out its `else`, and each arm ends with a statement, after any bindings; a
/// missing `else` builds as the empty block. The `if` that gives a value has both arms, each
/// one expression. Red before green: the parser refused `if done { break; };`, "expected
/// 'else'".
#[test]
fn an_if_statement_may_leave_out_its_else_and_its_arms_end_with_a_statement() {
    check(&[
        // Accepted.
        (
            "loop { if done { break; }; }",
            "(loop (block (do (if done (block (break)) (block)))))",
        ),
        (
            "x -> { if c { y = f(x); out <- y; }; 0 }",
            "(fn (x) (block (do (if c (block (= (y) (call f x)) (<- out y)) (block))) (return 0)))",
        ),
        (
            "c -> { x = if c { 1 } else { 2 }; x }",
            "(fn (c) (block (= (x) (if c (block (return 1)) (block (return 2)))) (return x)))",
        ),
        (
            "loop { if a { break; } else if b { y = 1; break; }; }",
            "(loop (block (do (if a (block (break)) (if b (block (= (y) 1) (break)) (block))))))",
        ),
        // Rejected: an empty `else { }`, a value at the end of an arm, an `if` that gives a
        // value with no `else` (its message, a clause of the parse error, is tested at step
        // L1.19), an empty `if`, and an empty `then` arm.
        (
            "loop { if c { break; } else { }; }",
            "error: Empty `else { }` in an `if` statement. Leave out the `else`: `if c { break; \
             };`.; an arm of an `if` statement holds a statement; with no `else`, nothing happens \
             when the condition is false at byte 28",
        ),
        (
            "c -> { if c { 1 }; 0 }",
            "error: Value at the end of an arm of an `if` statement: `1`.; an arm of an `if` \
             statement ends with a statement; an `if` that gives a value has an `else` and \
             stands where the value is used, as `x = if c { 1 } else { 2 };` at byte 14",
        ),
        (
            "c -> { if c { f(c) }; 0 }",
            "error: Value at the end of an arm of an `if` statement: `f(c)`. End the arm with a \
             statement, `f(c);`.; an arm of an `if` statement ends with a statement; an `if` \
             that gives a value has an `else` and stands where the value is used, as `x = if c \
             { 1 } else { 2 };` at byte 14",
        ),
        ("c -> { x = if c { 1 }; x }", "syntax"),
        (
            "c -> { if c { }; 0 }",
            "error: Empty `if` statement: `if c { };` does nothing. Delete it.; an arm of an `if` \
             statement holds a statement at byte 12",
        ),
        (
            "loop { if c { } else { break; }; }",
            "error: Empty block after `if c` in an `if` statement. Write a statement in it, or \
             negate the condition: `if !c { break; };`.; an arm of an `if` statement holds a \
             statement at byte 12",
        ),
        // A condition that is already negated as a whole loses its `!`, and the parentheses
        // that only grouped it; a `!` on part of the condition is not dropped (the controls).
        (
            "loop { if !c { } else { break; }; }",
            "error: Empty block after `if !c` in an `if` statement. Write a statement in it, or \
             negate the condition: `if c { break; };`.; an arm of an `if` statement holds a \
             statement at byte 13",
        ),
        (
            "loop { if !(a && b) { } else { break; }; }",
            "error: Empty block after `if !(a && b)` in an `if` statement. Write a statement in \
             it, or negate the condition: `if a && b { break; };`.; an arm of an `if` statement \
             holds a statement at byte 20",
        ),
        (
            "loop { if !a && b { } else { break; }; }",
            "error: Empty block after `if !a && b` in an `if` statement. Write a statement in it, \
             or negate the condition: `if !(!a && b) { break; };`.; an arm of an `if` statement \
             holds a statement at byte 18",
        ),
        (
            "loop { if a && b { } else { break; }; }",
            "error: Empty block after `if a && b` in an `if` statement. Write a statement in it, \
             or negate the condition: `if !(a && b) { break; };`.; an arm of an `if` statement \
             holds a statement at byte 17",
        ),
    ]);
}
