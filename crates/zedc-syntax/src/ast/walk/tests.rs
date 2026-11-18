//! No two expressions of a syntax tree share a span (TEST-read-fit-span-unique). The checker
//! keys what it learns of an expression by its span (`Info::fits` and `Ck::read_by` in
//! zedc-check, PROOF-read-fit-single-writer): two expressions at one span would read as one,
//! and the fit one of them needs would be refused as a second fit, or replaced, at the other.
//!
//! Every expression the builder makes has its own text, so the claim holds by construction;
//! these tests check it over every desugaring the builder makes and over the programs of the
//! repository, so that a desugaring that copies a span fails here. The desugarings, each in
//! [`DESUGARINGS`]: an infix call `a ~f~ b` (the call, its callee at the name and its operands
//! at theirs, ast/infix.rs); a section `(+)` (the section and the lambda it stands for are one
//! expression, the checker walks the lambda in its place, so the lambda shares its span and is
//! not counted apart; the lambda's body is at the text between the parentheses and its two
//! names at the parentheses, `section_lambda` in ast/mod.rs); `main`'s inputs and outputs
//! (`m.stdin`, `m.stdout` passed whole, a name at the member's text or at the whole argument,
//! ast/builder.rs); a sort key (`desc`, at its own argument); `is`, `in`, ranges, `else`,
//! reductions `><`, remaps `as … into …` (a remap that changes nothing is its operand, not a
//! second expression), records and named arguments written `x:` (one name at the label), and a
//! negative literal in a pattern (a pattern, not walked: the walk lists the expressions that
//! are run, the ones an operator or a call reads).

use super::{expr_kids_mut, stmts_exprs_mut};
use crate::ast::{Expr, ExprKind, Stmt, unit};
use crate::lex::{Span, lex};
use crate::parse::{TOP, parse_unit};
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Programs that make each desugaring of the builder (see the module's comment).
const DESUGARINGS: &[&str] = &[
    "f(a: int, b: int) = a + b;\nx = 1 ~f~ 2;\ny = 3 ~f~ 4 ~f~ 5;",
    "s = [1, 2, 3] >< (+);\nt = [1, 2] >< (*) else 1;\nu = [(+), (-)];",
    "main(m: MainArgs) {\n  w = m.stdin.concat(\" \");\n  m.stdout <- [w];\n}",
    "xs = [3, 1, 2];\nys = xs.sort(desc);\nzs = xs.sort();",
    "v = 2;\na = v is int;\nb = v is not f64;\nc = v in {1, 2};\nd = v not in {3};",
    "r = 1..=5;\nq = 0..<4;\ne = [1][0] else 0;",
    "t = [1, 2];\nu = t as (k -> v) into (v -> k);\nw = t as (k -> v) into (k -> v);",
    "x = 1;\ny = 2;\nr = {x:, y: y + 1};\nf(x: int) = x;\nz = f(x:);",
    "g(n: int) = match n { -1 -> 0, 0 -> 1, k -> k };\nh = g(-1) + -2;",
    "l = for n in 1..=3 where n != 2 { n * 2 };\nk = (n -> n + 1)(1);\nj = ((a, b) -> a + b)(1, 2);",
    "p = \"a ${1 + 2} b ${[1] >< (+)}\";\nq = !(1 == 2);\nr = -(-1);",
];

/// The span of each expression of `stmts`, the expressions of a section's lambda counted as
/// the section's own (the section is the lambda's span, and the checker walks the lambda in
/// its place). Walked on a work list, as [`expr_kids_mut`] is.
fn spans(stmts: &mut [Stmt]) -> Vec<Span> {
    let mut work: Vec<&mut Expr> = Vec::new();
    stmts_exprs_mut(stmts, &mut work);
    let mut out = Vec::new();
    while let Some(e) = work.pop() {
        out.push(e.span);
        let Expr { kind, .. } = e;
        if let ExprKind::Section(_, lambda) = kind {
            expr_kids_mut(&mut lambda.kind, &mut work);
        } else {
            expr_kids_mut(kind, &mut work);
        }
    }
    out
}

/// The first span two expressions of `text` share, or `None`; an error if `text` does not
/// build.
fn shared_span(text: &str) -> Result<Option<String>, String> {
    let tokens = lex(text).map_err(|e| format!("lexing: {e:?}"))?;
    let (tree, errors) = parse_unit(text, &tokens, TOP);
    if !errors.is_empty() {
        return Err(format!("parsing: {errors:?}"));
    }
    let mut stmts = unit(text, &tokens, &tree).map_err(|e| format!("building: {e:?}"))?;
    let mut seen = HashSet::new();
    Ok(spans(&mut stmts)
        .into_iter()
        .find(|s| !seen.insert(*s))
        .map(|s| {
            let shown = &text[s.start..s.end];
            format!("`{shown}` at {s:?} is the span of two expressions")
        }))
}

#[test]
fn each_desugaring_gives_each_expression_its_own_span() {
    for text in DESUGARINGS {
        match shared_span(text) {
            Ok(None) => {}
            Ok(Some(why)) => panic!("{why}, in\n{text}"),
            Err(e) => panic!("{e}, in\n{text}"),
        }
    }
}

/// The `.zed` files under `dir`, sorted.
fn zed_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()))
        .map(|d| d.expect("a directory entry").path())
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            zed_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "zed") {
            out.push(p);
        }
    }
}

#[test]
fn no_program_of_the_repository_has_two_expressions_at_one_span() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    zed_files(&root.join("zed"), &mut files);
    zed_files(&root.join("tests/steps"), &mut files);
    let mut built = 0;
    let mut not_built = Vec::new();
    for f in &files {
        let text = std::fs::read_to_string(f).expect("a .zed file reads");
        match shared_span(&text) {
            Ok(None) => built += 1,
            Ok(Some(why)) => panic!("{why}, in {}", f.display()),
            Err(e) => not_built.push(format!("{}: {e}", f.display())),
        }
    }
    eprintln!("{built} of {} files built and checked", files.len());
    for n in &not_built {
        eprintln!("not built: {n}");
    }
    assert!(built > 0, "no .zed file built");
}
