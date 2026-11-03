//! The L2 forms at the rule of low complexity (DESIGN.md Part G): building, formatting and
//! dropping a unit is linear in its size, for a struct of `n` fields, `n` methods, a display
//! nested `n` deep, and a chain of `n` updates. Each input is lexed and parsed before timing,
//! so the work measured is this step's, which the parser's own cost would otherwise hide.

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::ast::unit;
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};

/// A unit's text, tokens and parse tree.
struct Parsed {
    text: String,
    tokens: Vec<Token>,
    tree: Tree,
}

fn parsed(text: String) -> Parsed {
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
    Parsed { text, tokens, tree }
}

/// Builds and formats the unit `p`, and drops what it built.
fn pass(p: &Parsed) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    std::hint::black_box(format(&p.text, &p.tokens, &stmts));
}

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect();
    scaling::check(what, base, |n| pass(&units[&n]));
}

/// `struct Wide { f0: int = 0, f1: int = 1, … }` and a display giving every field.
fn wide(n: usize) -> String {
    let fields: Vec<String> = (0..n).map(|i| format!("f{i}: int = {i}")).collect();
    let given: Vec<String> = (0..n).map(|i| format!("f{i}: {i}")).collect();
    format!(
        "struct Wide {{ {} }}\nw = {{ {} }};\n",
        fields.join(", "),
        given.join(", ")
    )
}

#[test]
fn a_struct_of_many_fields_scales() {
    linear("a struct and a display of n fields", 1000, wide);
}

/// `n` methods on one struct, each with a parameter.
fn methods(n: usize) -> String {
    (0..n)
        .map(|i| format!("Acct.m{i}(k) = bal + k * {i};\n"))
        .collect()
}

#[test]
fn many_methods_scale() {
    linear("n methods", 500, methods);
}

/// `d = { a: { a: { … { a: 0 } … } } };`, nested `n` deep.
fn deep(n: usize) -> String {
    format!("d = {}0{};\n", "{ a: ".repeat(n), " }".repeat(n))
}

#[test]
fn a_deep_display_scales() {
    linear("a display nested n deep", 1000, deep);
}

/// `p with { x0 = 0 } with { x1 = 1 } …`, `n` updates long, and one `with` of `n` paths.
fn chain(n: usize) -> String {
    let chained: String = (0..n).map(|i| format!(" with {{ x{i} = {i} }}")).collect();
    let paths: Vec<String> = (0..n).map(|i| format!("c.x{i} = {i}")).collect();
    format!("q = p{chained};\nr = p with {{ {} }};\n", paths.join(", "))
}

#[test]
fn a_chain_of_updates_scales() {
    linear("a chain of n updates and an update of n paths", 1000, chain);
}
