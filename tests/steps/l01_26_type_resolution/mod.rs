//! Step L1.26: resolution rules 1, 3 and 4. Each declared function gets a signature from its
//! body; a bare numeric literal adopts the carrier an operator or a parameter expects,
//! exactly or not at all; an `is` test narrows the name it tests; a function argument fits
//! the function type its slot expects.

mod adoption;
mod calls;
mod fits;
mod narrowing;
mod random;
mod scaling;
mod signatures;

use zedc::ast::unit;
use zedc::check::{Info, check};
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;

/// The checker's findings on the unit `text`, with the resolution's binder names.
pub(crate) fn info(text: &str) -> (Info, Vec<String>) {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    let names = res.binders.iter().map(|b| b.name.clone()).collect();
    (check(&stmts, &res), names)
}

/// The signature of the declared function `name` in `text`, printed.
pub(crate) fn sig(text: &str, name: &str) -> String {
    let (info, names) = info(text);
    let (_, s) = info
        .sigs
        .iter()
        .find(|(id, _)| names[**id] == name)
        .unwrap_or_else(|| panic!("no function `{name}`"));
    s.to_string()
}

/// The type errors of `text`, each `message [text]`.
pub(crate) fn type_errors(text: &str) -> Vec<String> {
    let (info, _) = info(text);
    info.errors
        .iter()
        .map(|e| format!("{} [{}]", e.message, &text[e.span.start..e.span.end]))
        .collect()
}
