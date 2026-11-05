//! Step L1.26: resolution rules 1, 3 and 4. Each declared function gets a signature from its
//! body; a bare numeric literal adopts the carrier an operator or a parameter expects,
//! exactly or not at all; an `is` test narrows the name it tests; a function argument fits
//! the function type its slot expects.

mod adoption;
mod bounds;
mod calls;
mod curried_classes;
mod docs;
mod fits;
mod handled;
mod held_functions;
mod literals;
mod named_calls;
mod narrowing;
mod random;
mod scaling;
mod signatures;
mod soundness;

use std::sync::Arc;

use zedc::ast::Stmt;
use zedc::check::ty::Sig;
use zedc::check::{Info, check};
use zedc::resolve::Resolution;

/// The unit `text`, read and resolved: what the checker takes, built before a scaling test
/// times the checker alone (COMPLEXITY.md F85).
pub(crate) struct Resolved {
    text: String,
    stmts: Vec<Stmt>,
    res: Resolution,
}

impl Resolved {
    /// Reads and resolves `text`.
    pub(crate) fn new(text: &str) -> Self {
        let (stmts, res) = zed_tests::deep::resolved(text);
        Resolved {
            text: text.to_string(),
            stmts,
            res,
        }
    }

    /// The checker's findings.
    pub(crate) fn check(&self) -> Info {
        check(&self.stmts, &self.res)
    }

    /// The type errors, each `message [text]`.
    pub(crate) fn type_errors(&self) -> Vec<String> {
        self.check()
            .errors
            .iter()
            .map(|e| format!("{} [{}]", e.message, &self.text[e.span.start..e.span.end]))
            .collect()
    }
}

/// The checker's findings on the unit `text`, with the resolution's binder names.
pub(crate) fn info(text: &str) -> (Info, Vec<String>) {
    let r = Resolved::new(text);
    let names = r.res.binders.iter().map(|b| b.name.clone()).collect();
    (r.check(), names)
}

/// The signature of the declared function `name` in `text`.
pub(crate) fn sig_of(text: &str, name: &str) -> Arc<Sig> {
    let (info, names) = info(text);
    let (_, s) = info
        .sigs
        .iter()
        .find(|(id, _)| names[**id] == name)
        .unwrap_or_else(|| panic!("no function `{name}`"));
    s.clone()
}

/// The signature of the declared function `name` in `text`, printed.
pub(crate) fn sig(text: &str, name: &str) -> String {
    sig_of(text, name).to_string()
}

/// The type errors of `text`, each `message [text]`.
pub(crate) fn type_errors(text: &str) -> Vec<String> {
    Resolved::new(text).type_errors()
}
