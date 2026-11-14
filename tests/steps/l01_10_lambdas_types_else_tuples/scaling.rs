//! The nested atom patterns and lambdas whose text the benchmark of `bench/scaling.rs` writes,
//! and what that text must be, checked here at small sizes (TEST-bench-move-rest, P170).

use zedc::ast::Expr;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// The expression `text`, built.
fn build(text: &str) -> Expr {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Expr", TOP).unwrap();
    zedc::ast::build(text, &tokens, &tree).unwrap()
}

/// `e else #a(#a(… #a …)) -> 0`, the pattern nested `n` deep, and
/// `((x = ((x = … 0 …) -> x)) -> x)`, the lambda nested `n` deep.
pub(super) fn nested(n: usize) -> (Expr, Expr) {
    (
        build(&format!(
            "e else {}#a{} -> 0",
            "#a(".repeat(n),
            ")".repeat(n)
        )),
        build(&format!("{}0{}", "((x = ".repeat(n), ") -> x)".repeat(n))),
    )
}

/// Writes the text of `pattern` and `lambda`, nested `n` deep, and checks its length and start.
pub(super) fn texts_hold(pattern: &Expr, lambda: &Expr, n: usize) {
    let (p, l) = (pattern.to_string(), lambda.to_string());
    assert_eq!(p.len(), "(else e  0)".len() + 4 * n + 2);
    assert!(
        l.starts_with(&"(fn ((x = ".repeat(n)),
        "{}",
        &l[..l.len().min(40)]
    );
}

/// The text of nested patterns and lambdas has its length and start at small depths, and its
/// whole text at depth 1; `bench/scaling.rs` holds the timing.
#[test]
fn the_text_of_nested_patterns_and_lambdas_is_written_at_small_depths() {
    for n in [1, 2, 9] {
        let (pattern, lambda) = nested(n);
        texts_hold(&pattern, &lambda, n);
    }
    assert_eq!(nested(1).0.to_string(), "(else e #a(#a) 0)");
    assert_eq!(nested(1).1.to_string(), "(fn ((x = 0)) x)");
}
