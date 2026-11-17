//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting and resolving a unit, refusing a pattern written bare, and refusing alternatives
//! that bind different names are linear in the unit's size, for an or-pattern of `n`
//! alternatives, one nested `n` deep, a match of `n` arms of the new forms, an or-pattern
//! written bare with `n` alternatives, and `n` alternatives each binding its own name. Each
//! input is lexed and parsed before timing where the parse succeeds, so the work measured is
//! this step's. The benchmarks in `bench.rs` hold each linear; here each runs at small sizes.

use zedc::ast::{Error, unit};
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};
use zedc::rejection::Row;
use zedc::resolve::resolve_text;

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

/// Builds, formats and resolves the unit `p`, and drops what it built; gives the number of
/// errors of row "Or-pattern alternatives bind different names".
pub(super) fn pass(p: &Parsed) -> usize {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    std::hint::black_box(format(&p.text, &p.tokens, &stmts));
    let errors = resolve_text(&stmts, Some(&p.text)).expect_err("a match is a later form");
    (errors.iter())
        .filter(|e| e.row == Some(Row::OrPatternNamesDiffer))
        .count()
}

/// Lexes and parses `text`, which the parser refuses, and gives the error.
pub(super) fn refuse(text: &str) -> Error {
    let tokens = lex(text).unwrap();
    Error::of_parse(text, parse(text, &tokens, "Unit", TOP).unwrap_err())
}

/// `f(v) = match v { (#a0 | #a1 | …) -> 0, _ -> 1 };`, one or-pattern of `n` alternatives.
pub(super) fn alts(n: usize) -> String {
    let alts: Vec<String> = (0..n).map(|i| format!("#a{i}")).collect();
    format!(
        "f(v) = match v {{ ({}) -> 0, _ -> 1 }};\n",
        alts.join(" | ")
    )
}

/// `f(v) = match v { ((((#a0 | #a1) | #a2) | …)) -> 0, _ -> 1 };`, an or-pattern nested `n` deep.
pub(super) fn nested(n: usize) -> String {
    let mut p = "#a0".to_string();
    for i in 1..=n {
        p = format!("({p} | #a{i})");
    }
    format!("f(v) = match v {{ {p} -> 0, _ -> 1 }};\n")
}

/// A match of `n` arms, in turn a range, an `is`-pattern, an or-pattern and atoms whose payload
/// is one of them.
pub(super) fn arms(n: usize) -> String {
    let arms: Vec<String> = (0..n)
        .map(|i| match i % 6 {
            0 => format!("({i}..<{}) -> {i}", i + 1),
            1 => format!("(k{i} is int) where k{i} > {i} -> k{i}"),
            2 => format!("(#a{i} | #b{i} | {i}) -> {i}"),
            3 => format!("#p{i}(0..={i}) -> {i}"),
            4 => format!("#q{i}(x is String | bool) -> {i}"),
            _ => format!("#r{i}(#ok(x) | #err(x)) -> x"),
        })
        .collect();
    format!("f(v) = match v {{ {}, _ -> 0 }};\n", arms.join(", "))
}

/// `f(v) = match v { #a0 | #a1 | … -> 0, _ -> 1 };`, an or-pattern of `n` alternatives written
/// bare, which the parser refuses.
pub(super) fn bare(n: usize) -> String {
    let alts: Vec<String> = (0..n).map(|i| format!("#a{i}")).collect();
    format!("f(v) = match v {{ {} -> 0, _ -> 1 }};\n", alts.join(" | "))
}

/// `f(v) = match v { (#a0(x0) | #a1(x1) | …) -> 0, _ -> 1 };`, `n` alternatives, each binding a
/// name of its own: one error naming `n` names, with both repairs.
pub(super) fn differ(n: usize) -> String {
    let alts: Vec<String> = (0..n).map(|i| format!("#a{i}(x{i})")).collect();
    format!(
        "f(v) = match v {{ ({}) -> 0, _ -> 1 }};\n",
        alts.join(" | ")
    )
}

/// Every input of the benchmarks in `bench.rs` is built, formatted and resolved, or refused, at
/// small sizes, with the errors expected.
#[test]
fn each_form_is_built_formatted_and_resolved_at_small_sizes() {
    // From two alternatives: the grammar has no pattern `(#a0)`.
    for n in [2, 3, 9] {
        for make in [alts, nested, arms] {
            assert_eq!(pass(&parsed(make(n))), 0, "{}", make(n));
        }
        let e = refuse(&bare(n + 1));
        assert_eq!(e.row, Some(Row::BareOperatorPattern), "{e}");
        let d = differ(n + 1);
        assert_eq!(pass(&parsed(d)), 1);
    }
}
