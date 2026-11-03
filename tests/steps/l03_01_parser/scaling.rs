//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, refusing in name resolution and dropping a unit is linear in its size, for a
//! display of `n` entries, a match of `n` range-pattern arms, a section nested `n` deep, and an
//! array display of `n` elements or nested `n` deep.
//! Each input is lexed and parsed before timing, so the work measured is this step's.

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::ast::unit;
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};
use zedc::resolve::resolve;

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

/// Builds, formats and resolves the unit `p`, and drops what it built. Resolution refuses
/// every form of this step; the refusals are part of the work.
fn pass(p: &Parsed) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    std::hint::black_box(format(&p.text, &p.tokens, &stmts));
    assert!(resolve(&stmts).is_err());
}

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect();
    scaling::check(what, base, |n| pass(&units[&n]));
}

/// `f(x) = { 0 -> [0..<1, x::len], 1 -> [1..<2, x::len], … };`, a map display of `n` entries.
fn display(n: usize) -> String {
    let entries: Vec<String> = (0..n)
        .map(|i| format!("{i} -> [{i}..<{}, x::len]", i + 1))
        .collect();
    format!("f(x) = {{ {} }};\n", entries.join(", "))
}

#[test]
fn a_display_of_many_entries_scales() {
    linear("a display of n entries", 2000, display);
}

/// `f(x) = match x { 0..<1 -> 0, -2..=-1 -> 1, … , _ -> n };`, `n` range-pattern arms.
fn arms(n: usize) -> String {
    let arms: Vec<String> = (0..n)
        .map(|i| match i % 2 {
            0 => format!("{i}..<{} -> {i}", i + 1),
            _ => format!("-{}..=-{i} -> {i}", i + 1),
        })
        .collect();
    format!("f(x) = match x {{ {}, _ -> {n} }};\n", arms.join(", "))
}

#[test]
fn a_match_of_many_range_arms_scales() {
    linear("a match of n range-pattern arms", 2000, arms);
}

/// `f(x) = x >< (x >< (… (x >< (+)) …));`, a section nested `n` deep in reductions, with
/// `n` parentheses around the innermost section.
fn deep(n: usize) -> String {
    format!(
        "f(x) = {}{}(+){}{};\n",
        "x >< (".repeat(n),
        "(".repeat(n),
        ")".repeat(n),
        ")".repeat(n)
    )
}

#[test]
fn a_section_nested_deep_scales() {
    linear("a section nested n deep", 1000, deep);
}

/// `f(x) = [[0, x], [1, x], …];`, an array display of `n` arrays of two elements (SEQ-desugar).
fn array(n: usize) -> String {
    let rows: Vec<String> = (0..n).map(|i| format!("[{i}, x]")).collect();
    format!("f(x) = [{}];\n", rows.join(", "))
}

#[test]
fn an_array_display_of_many_elements_scales() {
    linear("an array display of n elements", 2000, array);
}

/// `f(x) = [[… [x] …]];`, an array display nested `n` deep (SEQ-desugar).
fn nested(n: usize) -> String {
    format!("f(x) = {}x{};\n", "[".repeat(n), "]".repeat(n))
}

#[test]
fn an_array_display_nested_deep_scales() {
    linear("an array display nested n deep", 1000, nested);
}
