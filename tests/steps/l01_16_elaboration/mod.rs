//! Step L1.16: elaboration of the L1 surface to kernel terms. Each program is elaborated and
//! its definitions evaluated by the kernel evaluator; where a term's shape is the point, it is
//! printed; and each error elaboration reports has a case.

mod calls;
mod errors;
mod handled;
mod order;
mod programs;
mod scaling;

use zed_kernel::{Evaluator, Term, World};
use zedc::ast::{Stmt, unit};
use zedc::check::{Info, check};
use zedc::elab::{Unit, elaborate, elaborate_checked};
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::{Resolution, resolve};

/// The elaboration of the unit `text`, or its errors as `message [text]`.
pub(crate) fn elab(text: &str) -> Result<Unit, Vec<String>> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    elaborate(&stmts, &res).map_err(|es| {
        es.iter()
            .map(|e| format!("{} [{}]", e.message, &text[e.span.start..e.span.end]))
            .collect()
    })
}

/// A unit parsed, resolved and checked without error, so that a scaling test can time its
/// elaboration alone: parsing and checking cost far more per term than elaboration and hide a
/// quadratic in it (COMPLEXITY.md F85).
pub(crate) struct Checked {
    stmts: Vec<Stmt>,
    res: Resolution,
    pub(crate) info: Info,
}

/// The unit `text`, parsed, resolved and checked.
pub(crate) fn checked(text: &str) -> Checked {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    Checked::new(unit(text, &tokens, &tree).unwrap())
}

impl Checked {
    /// The unit of the statements `stmts`, resolved and checked.
    pub(crate) fn new(stmts: Vec<Stmt>) -> Checked {
        let res = resolve(&stmts).unwrap_or_else(|e| panic!("{e:?}"));
        let info = check(&stmts, &res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        Checked { stmts, res, info }
    }

    /// The elaboration of the unit from the checker's findings: what [`elab`] gives, without
    /// the checker's warnings.
    pub(crate) fn elab(&self) -> Unit {
        elaborate_checked(&self.stmts, &self.res, &self.info).unwrap_or_else(|es| panic!("{es:?}"))
    }

    /// The checker's findings on the unit, made again.
    pub(crate) fn check(&self) -> Info {
        check(&self.stmts, &self.res)
    }
}

/// `t` under the interpreter's prelude words (step L1.18).
pub(crate) fn with_prelude(t: Term) -> Term {
    zedc::interp::prelude(t)
}

/// The value of the definition `name` of `text`, printed.
pub(crate) fn value(text: &str, name: &str) -> String {
    let u = elab(text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    let t = u
        .get(name)
        .unwrap_or_else(|| panic!("no definition `{name}`"));
    match Evaluator::new(World::new()).run(&with_prelude(t)) {
        Ok(v) => v.to_string(),
        Err(e) => format!("error: {e}"),
    }
}

/// The term of the definition `name` of `text`, not closed over the others.
pub(crate) fn term(text: &str, name: &str) -> String {
    let u = elab(text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    let d = u.defs.iter().find(|d| d.name == name);
    d.unwrap_or_else(|| panic!("no definition `{name}`"))
        .term
        .to_string()
}

/// The errors of `text`.
pub(crate) fn errors(text: &str) -> Vec<String> {
    match elab(text) {
        Ok(_) => panic!("{text}: elaborated without error"),
        Err(e) => e,
    }
}
