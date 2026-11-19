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

use zed_tests::step_helpers::l02_01_parser_structs::{build, fmt, sx};
use zedc::ast::Error;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve_text;

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
