//! Writing the text of nested atom patterns, and of lambdas nested in their parameters'
//! defaults, is of order n in its length (DESIGN.md Part G).

use std::cell::RefCell;
use std::collections::HashMap;

use zed_tests::scaling;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// The expression `text`, built.
fn build(text: &str) -> zedc::ast::Expr {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Expr", TOP).unwrap();
    zedc::ast::build(text, &tokens, &tree).unwrap()
}

/// `e else #a(#a(… #a …)) -> 0`, the pattern nested `n` deep, and
/// `((x = ((x = … 0 …) -> x)) -> x)`, the lambda nested `n` deep.
fn nested(n: usize) -> (zedc::ast::Expr, zedc::ast::Expr) {
    (
        build(&format!(
            "e else {}#a{} -> 0",
            "#a(".repeat(n),
            ")".repeat(n)
        )),
        build(&format!("{}0{}", "((x = ".repeat(n), ") -> x)".repeat(n))),
    )
}

#[test]
fn the_text_of_nested_patterns_and_lambdas_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            let built = RefCell::new(HashMap::new());
            scaling::check(
                "the text of nested patterns and lambdas, by depth",
                125,
                |n| {
                    let mut built = built.borrow_mut();
                    let (pattern, lambda) = built.entry(n).or_insert_with(|| nested(n));
                    let (p, l) = (pattern.to_string(), lambda.to_string());
                    assert_eq!(p.len(), "(else e  0)".len() + 4 * n + 2);
                    assert!(l.starts_with(&"(fn ((x = ".repeat(n)), "{}", &l[..40]);
                },
            );
            assert_eq!(nested(1).0.to_string(), "(else e #a(#a) 0)");
            assert_eq!(nested(1).1.to_string(), "(fn ((x = 0)) x)");
        })
        .unwrap()
        .join()
        .unwrap();
}
