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

/// Builds, formats if `formatted`, and resolves the unit `p`, and drops what it built.
/// Resolution refuses every form of this step; the refusals are part of the work.
fn pass(p: &Parsed, formatted: bool) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    if formatted {
        std::hint::black_box(format(&p.text, &p.tokens, &stmts));
    }
    assert!(resolve(&stmts).is_err());
}

/// The units `make(base)` and `make(8 * base)`, parsed.
fn units(base: usize, make: impl Fn(usize) -> String) -> HashMap<usize, Parsed> {
    [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect()
}

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units = units(base, make);
    scaling::check(what, base, |n| pass(&units[&n], true));
}

/// `f(n) = loop t { x0' = x0 + t with initial x0 = 0; until x1' > n; … };`, a loop body of `n`
/// statements: bindings with a boundary, guards of both kinds and expression statements, which
/// the formatter reorders.
fn body(n: usize) -> String {
    let stmts: Vec<String> = (0..n)
        .map(|i| match i % 4 {
            0 => format!("x{i}' = x{i} + t with initial x{i} = 0;"),
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

/// Building, resolving and dropping are linear in the depth. The formatter writes each loop on
/// its own lines, indented by its depth, so its text is of order n^2 and so is writing it, as
/// for any nest of blocks (step L1.13).
#[test]
fn nested_loops_scale() {
    let units = units(1000, nested);
    scaling::check("n nested loops, built and resolved", 1000, |n| {
        pass(&units[&n], false)
    });
    scaling::check_order("n nested loops, formatted", 1000, 2, |n| {
        let p = &units[&n];
        let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
        assert!(format(&p.text, &p.tokens, &stmts).len() > n * n);
    });
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
