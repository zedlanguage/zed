//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, refusing in name resolution and dropping a unit is linear in its size, for a
//! loop body of `n` statements, `n` nested loops and a piecewise definition of `n` pieces.
//! The benchmarks in `bench/scaling.rs` hold the times; here each form passes at small sizes.

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

/// Builds, formats if `formatted`, and resolves the unit `p`, and drops what it built.
/// Resolution refuses every form of this step; the refusals are part of the work.
pub(super) fn pass(p: &Parsed, formatted: bool) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    if formatted {
        std::hint::black_box(format(&p.text, &p.tokens, &stmts));
    }
    assert!(resolve(&stmts).is_err());
}

/// Builds and formats the unit `p` of `n` nested loops: each loop is written on its own lines,
/// indented by its depth, so the text is longer than `n^2`.
pub(super) fn formats_on_lines(p: &Parsed, n: usize) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    assert!(format(&p.text, &p.tokens, &stmts).len() > n * n);
}

/// `f(n) = loop t { initial x0 = 0; x0' = x0 + t; until x1' > n; … };`, a loop body of `n`
/// statements: `initial` statements with their bindings, guards of both kinds and expression
/// statements, which the formatter reorders.
pub(super) fn body(n: usize) -> String {
    let stmts: Vec<String> = (0..n)
        .map(|i| match i % 4 {
            0 => format!("initial x{i} = 0; x{i}' = x{i} + t;"),
            1 => format!("until x{i}' > n;"),
            2 => format!("while t < {i};"),
            _ => format!("g(x{i})*.h({i});"),
        })
        .collect();
    format!("f(n) = loop t {{ {} }};\n", stmts.join(" "))
}

/// `f(n) = loop t0 { loop t1 { … loop { break n; }; … }; };`, `n` loops nested, `n >= 1`.
pub(super) fn nested(n: usize) -> String {
    let opens: String = (0..n).map(|i| format!("loop t{i} {{ ")).collect();
    format!("f(n) = {opens}break n;{};\n", " };".repeat(n - 1) + " }")
}

/// `x[i in 0..<1] = cold(i); x[i in 1..<2] = x[i - 1] + 1; …`, a piecewise definition of `n`
/// pieces, each with a sentinel.
pub(super) fn pieces(n: usize) -> String {
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
fn each_form_is_built_formatted_and_refused_at_small_sizes() {
    for n in [1, 2, 9] {
        pass(&parsed(body(n)), true);
        pass(&parsed(pieces(n)), true);
        let p = parsed(nested(n));
        pass(&p, false);
        formats_on_lines(&p, n);
    }
}
