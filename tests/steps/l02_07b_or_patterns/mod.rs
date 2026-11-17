//! Step L2.7b, its syntax and names: the or-pattern `(p | q)`, the parenthesized range pattern
//! `(a..=b)` and `is`-pattern `(n is T)`, and an atom's payload that is one of them sharing the
//! atom's parentheses, `#p(0..=9)`. Each builds and formats to itself; each written bare is
//! refused with the arm written with it in parentheses (row "Pattern built with an operator,
//! written bare"); alternatives that bind different names are refused with the arm written out
//! once for each alternative and, where each binds one name, with one name in each (row
//! "Or-pattern alternatives bind different names"). The checking half of the step (types,
//! exhaustiveness by the residue method, guarded overlap) is plan row OR-PAT-check.

mod bare;
mod bench;
mod forms;
mod names;
mod scaling;

use zedc::ast::{Error, Stmt, unit};
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve_text;

/// The statements of the unit `text`, one s-expression per line.
fn sx(text: &str) -> String {
    build(text)
        .1
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>()
        .join("\n")
}

/// The tokens and statements of the unit `text`.
#[track_caller]
fn build(text: &str) -> (Vec<Token>, Vec<Stmt>) {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    let stmts = unit(text, &tokens, &tree).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    (tokens, stmts)
}

/// `text` formatted, after checking that the result builds to the same statements and formats
/// to itself.
#[track_caller]
fn fmt(text: &str) -> String {
    let (tokens, stmts) = build(text);
    let out = format(text, &tokens, &stmts);
    let (tokens2, stmts2) = build(&out);
    let show = |ss: &[Stmt]| ss.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    assert_eq!(
        show(&stmts),
        show(&stmts2),
        "the statements changed in\n{out}"
    );
    assert_eq!(format(&out, &tokens2, &stmts2), out, "not a fixed point");
    out
}

/// The error the parser refuses the unit `text` with.
#[track_caller]
fn refusal(text: &str) -> Error {
    let tokens = lex(text).unwrap();
    Error::of_parse(text, parse(text, &tokens, "Unit", TOP).expect_err(text))
}

/// The errors name resolution gives the unit `text`, with its text for the repairs.
fn resolution_errors(text: &str) -> Vec<Error> {
    let (_, stmts) = build(text);
    resolve_text(&stmts, Some(text)).err().unwrap_or_default()
}
