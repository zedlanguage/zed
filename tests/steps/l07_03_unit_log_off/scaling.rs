//! Building, formatting and resolving unit items is linear in their number (DESIGN.md Part G,
//! the rule of low complexity): `n` copies of `@log(#off);`, each after the first refused with
//! a note naming the first, and `n` functions each with the item misplaced in its body. Each
//! input is lexed and parsed before timing.

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::ast::unit;
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};
use zedc::resolve::resolve;

struct Parsed {
    text: String,
    tokens: Vec<Token>,
    tree: Tree,
}

/// Checks that building, formatting and resolving `make(n)` is linear in `n`, from `base`;
/// every unit made is refused, with `n - 1` or `n` errors.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = [base, 8 * base]
        .into_iter()
        .map(|n| {
            let text = make(n);
            let tokens = lex(&text).unwrap();
            let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
            (n, Parsed { text, tokens, tree })
        })
        .collect();
    scaling::check(what, base, |n| {
        let p = &units[&n];
        let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
        std::hint::black_box(format(&p.text, &p.tokens, &stmts));
        let errors = resolve(&stmts).unwrap_err();
        assert!(errors.len() >= n - 1);
    });
}

#[test]
fn many_unit_items_scale() {
    linear("n copies of the unit item", 4000, |n| {
        (0..n).map(|i| format!("@log(#off);\nf{i}(x) = x;\n")).collect()
    });
}

#[test]
fn many_misplaced_unit_items_scale() {
    linear("n blocks holding the unit item", 4000, |n| {
        (0..n)
            .map(|i| format!("f{i}(x) {{\n  @log(#off);\n  x\n}}\n"))
            .collect()
    });
}
