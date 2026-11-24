//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, resolving and dropping a unit are linear in its size, for a list pattern of `n`
//! entries with a rest, a record pattern of `n` fields, list and record patterns nested `n`
//! deep, and a match of `n` arms of them. Each input is lexed and parsed before timing, so the
//! work measured is this step's. The benchmarks in `bench.rs` hold each linear; here each runs
//! at small sizes.

use zed_tests::not_yet;
use zedc::ast::unit;
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};
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
/// resolution errors that are not a later form (a list or record pattern is not compiled yet).
pub(super) fn pass(p: &Parsed) -> usize {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    std::hint::black_box(format(&p.text, &p.tokens, &stmts));
    let errors = resolve_text(&stmts, Some(&p.text)).expect_err("a match is a later form");
    let later = not_yet("");
    let later = later.trim_start();
    errors
        .iter()
        .filter(|e| !e.message.ends_with(later))
        .count()
}

/// `f(v) = match v { [x0, x1, …, ..rest] -> 0, _ -> 1 };`, one list pattern of `n` entries.
pub(super) fn entries(n: usize) -> String {
    let xs: String = (0..n).map(|i| format!("x{i}, ")).collect();
    format!("f(v) = match v {{ [{xs}..rest] -> 0, _ -> 1 }};\n")
}

/// `f(p) = match p { {f0:, f1: 1, …} -> 0, _ -> 1 };`, one record pattern of `n` fields.
pub(super) fn fields(n: usize) -> String {
    let fs: Vec<String> = (0..n)
        .map(|i| match i % 2 {
            0 => format!("f{i}:"),
            _ => format!("f{i}: {i}"),
        })
        .collect();
    format!("f(p) = match p {{ {{{}}} -> 0, _ -> 1 }};\n", fs.join(", "))
}

/// `f(v) = match v { [{a: [{a: … [x] …}]}] -> 0, _ -> 1 };`, list and record patterns in
/// turn, nested `n` deep.
pub(super) fn nested(n: usize) -> String {
    let mut p = "x".to_string();
    for i in 0..n {
        p = match i % 2 {
            0 => format!("[{p}, ..r{i}]"),
            _ => format!("{{a: {p}}}"),
        };
    }
    format!("f(v) = match v {{ {p} -> 0, _ -> 1 }};\n")
}

/// A match of `n` arms, in turn a list, a list with a rest, a rest alone and a record.
pub(super) fn arms(n: usize) -> String {
    let arms: Vec<String> = (0..n)
        .map(|i| match i % 4 {
            0 => format!("[a{i}, {i}] -> a{i}"),
            1 => format!("[a{i}, ..r{i}] -> a{i}"),
            2 => format!("[..r{i}] -> {i}"),
            _ => format!("{{x:, y: [h{i}]}} -> h{i}"),
        })
        .collect();
    format!("f(v) = match v {{ {}, _ -> 0 }};\n", arms.join(", "))
}

/// Every input of the benchmarks in `bench.rs` is built, formatted and resolved at small sizes,
/// with no error but the later forms: every name an arm reads is bound by its pattern.
#[test]
fn each_form_is_built_formatted_and_resolved_at_small_sizes() {
    for n in [1, 2, 3, 9] {
        for make in [entries, fields, nested, arms] {
            assert_eq!(pass(&parsed(make(n))), 0, "{}", make(n));
        }
    }
}
