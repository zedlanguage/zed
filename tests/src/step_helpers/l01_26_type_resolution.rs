//! Checker helpers of step L1.26 (tests/steps/l01_26_type_resolution).

use std::sync::Arc;

use zedc::ast::Stmt;
use zedc::check::Info;
use zedc::check::ty::Sig;
use zedc::check::walk::check;
use zedc::resolve::Resolution;

/// The unit `text`, read and resolved: what the checker takes, built before a scaling test
/// times the checker alone (COMPLEXITY.md F85).
pub struct Resolved {
    text: String,
    stmts: Vec<Stmt>,
    res: Resolution,
}

impl Resolved {
    /// Reads and resolves `text`.
    pub fn new(text: &str) -> Self {
        let (stmts, res) = crate::deep::resolved(text);
        Resolved {
            text: text.to_string(),
            stmts,
            res,
        }
    }

    /// The checker's findings.
    pub fn check(&self) -> Info {
        check(&self.stmts, &self.res)
    }

    /// The type errors, each `message [text]`.
    pub fn type_errors(&self) -> Vec<String> {
        self.check()
            .errors
            .iter()
            .map(|e| format!("{} [{}]", e.message, &self.text[e.span.start..e.span.end]))
            .collect()
    }
}

/// The checker's findings on the unit `text`, with the resolution's binder names.
pub fn info(text: &str) -> (Info, Vec<String>) {
    let r = Resolved::new(text);
    let names = r.res.binders.iter().map(|b| b.name.clone()).collect();
    (r.check(), names)
}

/// The signature of the declared function `name` in `text`.
pub fn sig_of(text: &str, name: &str) -> Arc<Sig> {
    let (info, names) = info(text);
    let (_, s) = info
        .sigs
        .iter()
        .find(|(id, _)| names[**id] == name)
        .unwrap_or_else(|| panic!("no function `{name}`"));
    s.clone()
}

/// The signature of the declared function `name` in `text`, printed.
pub fn sig(text: &str, name: &str) -> String {
    sig_of(text, name).to_string()
}

/// The type errors of `text`, each `message [text]`.
pub fn type_errors(text: &str) -> Vec<String> {
    Resolved::new(text).type_errors()
}
