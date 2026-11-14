//! Building, formatting and resolving unit items is linear in their number (DESIGN.md Part G,
//! the rule of low complexity): `n` copies of `@log(#off);`, each after the first refused with
//! a note naming the first, and `n` functions each with the item misplaced in its body. The
//! benchmarks in `bench/scaling.rs` hold the times; here each unit passes at small sizes.

use zedc::ast::unit;
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};
use zedc::resolve::resolve;

pub(super) struct Parsed {
    text: String,
    tokens: Vec<Token>,
    tree: Tree,
}

/// The unit `text`, lexed and parsed.
pub(super) fn parsed(text: String) -> Parsed {
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
    Parsed { text, tokens, tree }
}

/// Builds, formats and resolves the unit `p` of size `n`, which is refused with `n - 1` or `n`
/// errors.
pub(super) fn pass(p: &Parsed, n: usize) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    std::hint::black_box(format(&p.text, &p.tokens, &stmts));
    let errors = resolve(&stmts).unwrap_err();
    assert!(errors.len() >= n - 1);
}

/// `n` copies of the unit item, each before a function.
pub(super) fn copies(n: usize) -> String {
    (0..n)
        .map(|i| format!("@log(#off);\nf{i}(x) = x;\n"))
        .collect()
}

/// `n` functions, each with the unit item in its body.
pub(super) fn misplaced(n: usize) -> String {
    (0..n)
        .map(|i| format!("f{i}(x) {{\n  @log(#off);\n  x\n}}\n"))
        .collect()
}

#[test]
fn each_unit_is_built_formatted_and_refused_at_small_sizes() {
    for n in [2, 3, 9] {
        pass(&parsed(copies(n)), n);
        pass(&parsed(misplaced(n)), n);
    }
}
