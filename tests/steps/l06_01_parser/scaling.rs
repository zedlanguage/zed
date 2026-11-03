//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, refusing in name resolution and dropping a unit is linear in its size, for a
//! loop body of `n` statements, `n` nested loops and a piecewise definition of `n` pieces.
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

/// `f(n) = loop t { x0' = x0 + t with x0 = 0; until x1' > n; … };`, a loop body of `n`
/// statements: bindings with a boundary, guards of both kinds and expression statements, which
/// the formatter reorders.
fn body(n: usize) -> String {
    let stmts: Vec<String> = (0..n)
        .map(|i| match i % 4 {
            0 => format!("x{i}' = x{i} + t with x{i} = 0;"),
            1 => format!("until x{i}' > n;"),
            2 => format!("while t < {i};"),
            _ => format!("g(x{i})*.h({i});"),
        })
        .collect();
    format!("f(n) = loop t {{ {} }};\n", stmts.join(" "))
}

#[test]
fn a_loop_body_of_many_statements_scales() {
    linear("a loop body of n statements", 2000, body);
}

/// `f(n) = loop t0 { loop t1 { … loop { break n; }; … }; };`, `n` loops nested.
fn nested(n: usize) -> String {
    let opens: String = (0..n).map(|i| format!("loop t{i} {{ ")).collect();
    format!("f(n) = {opens}break n;{};\n", " };".repeat(n - 1) + " }")
}

#[test]
fn nested_loops_scale() {
    linear("n nested loops", 1000, nested);
}

/// `x[i in 0..<1] = cold(i); x[i in 1..<2] = x[i - 1] + 1; …`, a piecewise definition of `n`
/// pieces, each with a sentinel.
fn pieces(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "x[i in {i}..<{}][j] = x[i - 1][j] + {i} with x[{i}][-1] = 0;\n",
                i + 1
            )
        })
        .collect()
}

#[test]
fn a_piecewise_definition_of_many_pieces_scales() {
    linear("a piecewise definition of n pieces", 2000, pieces);
}
