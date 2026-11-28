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

/// `type T = Part… with { type Part0 = int, type Part1 = (Part0, Part0), … };`, a list of `n`
/// local parts each naming a pair of the one before, and `type U = Q0 with type Q0 = Q1 with
/// type Q1 = Q2 … with type Q… = int;`, `n` nested `with` clauses (SPEC-with-local-part).
pub(super) fn parts(n: usize) -> String {
    let listed: Vec<String> = (0..n)
        .map(|i| match i {
            0 => "type Part0 = int".to_string(),
            _ => format!("type Part{i} = (Part{}, Part{})", i - 1, i - 1),
        })
        .collect();
    let nested: String = (0..n)
        .map(|i| match i + 1 < n {
            true => format!(" with type Nest{i} = Nest{}", i + 1),
            false => format!(" with type Nest{i} = int"),
        })
        .collect();
    format!(
        "type Top = Part{} with {{ {} }};\ntype Nested = Nest0{nested};\n",
        n - 1,
        listed.join(", ")
    )
}

/// `parts(n)`, then `type Fun = A -> Link0 with type Link0 = (A, Link1) with type Link1 = (A,
/// Link2) … with type Link… = A for A in int | rat;`: a chain of `n` clauses around a function
/// type, each part using the variable of the `for` and the part of the clause outside it, which
/// the resolver reads in one pass over the chain (`Resolver::part_home`, COMPLEXITY.md
/// IMPL-with-list).
pub(super) fn part_chain(n: usize) -> String {
    let clauses: String = (0..n)
        .map(|i| match i + 1 < n {
            true => format!(" with type Link{i} = (A, Link{})", i + 1),
            false => format!(" with type Link{i} = A"),
        })
        .collect();
    format!(
        "{}type Fun = A -> Link0{clauses} for A in int | rat;\n",
        parts(n)
    )
}

/// The statements of `p`, built.
pub(super) fn built(p: &Parsed) -> (String, Vec<zedc::ast::Stmt>) {
    (p.text.clone(), unit(&p.text, &p.tokens, &p.tree).unwrap())
}

/// The input of the resolution benchmark in `bench.rs` resolves at small sizes with no error
/// but this zedc's refusal of each type declaration and each local part: every name is
/// defined, no part is used above a part it may not see, and the `for` variable stands in the
/// function type under each chain.
#[test]
fn local_parts_in_a_chain_resolve_at_small_sizes() {
    let refusals = [
        zed_tests::not_yet!("a type declaration"),
        zed_tests::not_yet!("a local part declaration"),
    ];
    for n in [1, 2, 9] {
        let (text, stmts) = built(&parsed(part_chain(n)));
        let errors = zedc::resolve::resolve_text(&stmts, Some(&text))
            .err()
            .unwrap_or_default();
        let parts = errors.iter().filter(|e| e.message == refusals[1]).count();
        let others: Vec<&str> = errors
            .iter()
            .map(|e| e.message.as_str())
            .filter(|m| !refusals.contains(m))
            .collect();
        assert!(others.is_empty(), "n = {n}: {others:?}");
        // One refusal for each `with` clause: the braced list is one, and each chain has n.
        assert_eq!(parts, 2 * n + 1, "n = {n}");
    }
}

/// `v with { f0(0), f1(1), … }`, a list of `n` facets (SPEC-with-list), which this zedc parses
/// and refuses as of layer L7.
pub(super) fn facets(n: usize) -> String {
    let fs: Vec<String> = (0..n).map(|i| format!("f{i}({i})")).collect();
    format!("w = v with {{ {} }};\n", fs.join(", "))
}

/// Every input of the benchmarks in `bench.rs` is built and formatted at small sizes, and the
/// list of facets, which does not build, is parsed.
#[test]
fn each_form_is_built_and_formatted_at_small_sizes() {
    for n in [1, 2, 9] {
        parsed(facets(n));
    }
    for make in [wide, imports, repeated, methods, deep, chain, named, parts] {
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
