//! The L2 forms at the rule of low complexity (DESIGN.md Part G): building, formatting and
//! dropping a unit is linear in its size, for a struct of `n` fields, `n` methods, a display
//! nested `n` deep, and a chain of `n` updates. Each input is lexed and parsed before timing,
//! so the work measured is this step's, which the parser's own cost would otherwise hide. The
//! benchmarks in `bench.rs` hold each linear; here each is built and formatted at small sizes.

use zedc::ast::unit;
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};

/// A unit's text, tokens and parse tree.
pub(super) struct Parsed {
    text: String,
    tokens: Vec<Token>,
    tree: Tree,
}

pub(super) fn parsed(text: String) -> Parsed {
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
    Parsed { text, tokens, tree }
}

/// Builds and formats the unit `p`, and drops what it built.
pub(super) fn pass(p: &Parsed) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    std::hint::black_box(format(&p.text, &p.tokens, &stmts));
}

/// `struct Wide { f0: int = 0, f1: int = 1, … }` and a display giving every field.
pub(super) fn wide(n: usize) -> String {
    let fields: Vec<String> = (0..n).map(|i| format!("f{i}: int = {i}")).collect();
    let given: Vec<String> = (0..n).map(|i| format!("f{i}: {i}")).collect();
    format!(
        "struct Wide {{ {} }}\nw = {{ {} }};\n",
        fields.join(", "),
        given.join(", ")
    )
}

/// `struct Many { import m.T0, import m .T1, … }`, `n` imports of distinct paths, some written
/// with spaces around their `.`.
pub(super) fn imports(n: usize) -> String {
    let paths: Vec<String> = (0..n)
        .map(|i| format!("import m{}T{i}", [".", " .", ". ", " . "][i % 4]))
        .collect();
    format!("struct Many {{ {} }}\n", paths.join(", "))
}

/// `struct Many { import m.T0, …, import m . T0, … }`: the `n` imports of `imports(n)`, then
/// each path again, spaced another way, so the last `n` imports are repeats.
pub(super) fn repeated(n: usize) -> String {
    let again: Vec<String> = (0..n)
        .map(|i| format!("import m{}T{i}", [" . ", ". ", " .", "."][i % 4]))
        .collect();
    imports(n).replacen(" }", &format!(", {} }}", again.join(", ")), 1)
}

/// `n` methods on one struct, each with a parameter.
pub(super) fn methods(n: usize) -> String {
    (0..n)
        .map(|i| format!("Acct.m{i}(k) = bal + k * {i};\n"))
        .collect()
}

/// `d = { a: { a: { … { a: 0 } … } } };`, nested `n` deep.
pub(super) fn deep(n: usize) -> String {
    format!("d = {}0{};\n", "{ a: ".repeat(n), " }".repeat(n))
}

/// `p with { x0 = 0 } with { x1 = 1 } …`, `n` updates long, and one `with` of `n` paths.
pub(super) fn chain(n: usize) -> String {
    let chained: String = (0..n).map(|i| format!(" with {{ x{i} = {i} }}")).collect();
    let paths: Vec<String> = (0..n).map(|i| format!("c.x{i} = {i}")).collect();
    format!("q = p{chained};\nr = p with {{ {} }};\n", paths.join(", "))
}

/// `w = { f0: v0, f1: v1, … };`, `n` fields whose values are bare names, and a display whose one
/// value is a chain of `n` operands joined by `&&` and one of `n` operands joined by `else`.
pub(super) fn named(n: usize) -> String {
    let given: Vec<String> = (0..n).map(|i| format!("f{i}: v{i}")).collect();
    let and: Vec<String> = (0..n).map(|i| format!("b{i}")).collect();
    let or_else: Vec<String> = (0..n).map(|i| format!("e{i}")).collect();
    format!(
        "w = {{ {} }};\nj = {{ a: {} }};\nk = {{ a: {} }};\n",
        given.join(", "),
        and.join(" && "),
        or_else.join(" else ")
    )
}

/// Every input of the benchmarks in `bench.rs` is built and formatted at small sizes.
#[test]
fn each_form_is_built_and_formatted_at_small_sizes() {
    for make in [wide, imports, repeated, methods, deep, chain, named] {
        for n in [1, 2, 9] {
            pass(&parsed(make(n)));
        }
    }
}

/// Each repeat is found by one lookup and dropped, so the struct keeps `n` imports.
#[test]
fn a_struct_that_imports_every_path_twice_keeps_each_once() {
    for n in [1, 2, 9, 1000] {
        let p = parsed(repeated(n));
        let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
        let shown = stmts[0].to_string();
        assert_eq!(shown.matches("(import ").count(), n, "{shown}");
    }
}
