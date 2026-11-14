//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, refusing in name resolution and dropping a unit is linear in its size, for a
//! display of `n` entries, a match of `n` range-pattern arms, a section nested `n` deep, and an
//! array display of `n` elements or nested `n` deep.
//! Each input is lexed and parsed before timing, so the work measured is this step's. The
//! benchmarks in `bench.rs` hold each linear; here each is built, formatted and refused at small
//! sizes.

use zedc::ast::unit;
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};
use zedc::resolve::resolve;

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

/// Builds, formats and resolves the unit `p`, and drops what it built. Resolution refuses
/// every form of this step; the refusals are part of the work.
pub(super) fn pass(p: &Parsed) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    std::hint::black_box(format(&p.text, &p.tokens, &stmts));
    assert!(resolve(&stmts).is_err());
}

/// `f(x) = { 0 -> [0..<1, x::len], 1 -> [1..<2, x::len], … };`, a map display of `n` entries.
pub(super) fn display(n: usize) -> String {
    let entries: Vec<String> = (0..n)
        .map(|i| format!("{i} -> [{i}..<{}, x::len]", i + 1))
        .collect();
    format!("f(x) = {{ {} }};\n", entries.join(", "))
}

/// `f(x) = match x { 0..<1 -> 0, -2..=-1 -> 1, … , _ -> n };`, `n` range-pattern arms.
pub(super) fn arms(n: usize) -> String {
    let arms: Vec<String> = (0..n)
        .map(|i| match i % 2 {
            0 => format!("{i}..<{} -> {i}", i + 1),
            _ => format!("-{}..=-{i} -> {i}", i + 1),
        })
        .collect();
    format!("f(x) = match x {{ {}, _ -> {n} }};\n", arms.join(", "))
}

/// `f(x) = x >< (x >< (… (x >< (+)) …));`, a section nested `n` deep in reductions, with
/// `n` parentheses around the innermost section.
pub(super) fn deep(n: usize) -> String {
    format!(
        "f(x) = {}{}(+){}{};\n",
        "x >< (".repeat(n),
        "(".repeat(n),
        ")".repeat(n),
        ")".repeat(n)
    )
}

/// `f(x) = [[0, x], [1, x], …];`, an array display of `n` arrays of two elements (SEQ-desugar).
pub(super) fn array(n: usize) -> String {
    let rows: Vec<String> = (0..n).map(|i| format!("[{i}, x]")).collect();
    format!("f(x) = [{}];\n", rows.join(", "))
}

/// `f(x) = [[… [x] …]];`, an array display nested `n` deep (SEQ-desugar).
pub(super) fn nested(n: usize) -> String {
    format!("f(x) = {}x{};\n", "[".repeat(n), "]".repeat(n))
}

/// Every input of the benchmarks in `bench.rs` is built, formatted and refused in name
/// resolution at small sizes.
#[test]
fn each_form_is_built_formatted_and_refused_at_small_sizes() {
    for make in [display, arms, deep, array, nested] {
        for n in [1, 2, 9] {
            pass(&parsed(make(n)));
        }
    }
}
