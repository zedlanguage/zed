//! A unit the checker accepts elaborates to a unit holding each of its top-level definitions
//! (plan row FAIL-elab-none-without-error): elaboration never drops a definition without an
//! error. When it fails with no error of its own or of the checker's, it reports a bug in zedc
//! at the first definition that failed, so the failure shows at its cause rather than as a
//! later "no definition `x`".

use std::collections::HashSet;

use zed_tests::oracle::{corpus, step_units};
use zedc::ast::{Stmt, StmtKind, Target, unit};
use zedc::check::walk::check;
use zedc::elab::elaborate_text;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;

use super::elab;

/// The names the top-level statements of `stmts` define.
fn defined(stmts: &[Stmt]) -> Vec<&str> {
    let mut out = Vec::new();
    for s in stmts {
        match &s.bare().kind {
            StmtKind::Function(f) => out.push(f.name.as_str()),
            StmtKind::Bind { targets, .. } => out.extend(targets.iter().filter_map(|t| match t {
                Target::Name(n, _) => Some(n.as_str()),
                Target::Wild => None,
            })),
            _ => {}
        }
    }
    out
}

/// What elaboration made of a unit the checker accepts.
enum Outcome {
    /// A unit holding each top-level definition.
    Kept,
    /// Elaboration's own errors, none of them a bug in zedc: a form the checker accepts and
    /// this zedc does not support, as a prelude word.
    Refused,
    /// A unit that lost a definition, or a bug in zedc reported: the fault, described.
    Fault(String),
}

/// What elaboration makes of `text`, when it checks without error.
fn kept(text: &str) -> Option<Outcome> {
    let tokens = lex_fence(text).ok()?;
    let tree = parse(text, &tokens, "Unit", TOP).ok()?;
    let stmts = unit(text, &tokens, &tree).ok()?;
    let res = resolve(&stmts).ok()?;
    if !check(&stmts, &res).errors.is_empty() {
        return None;
    }
    Some(match elaborate_text(&stmts, &res, Some(text), None) {
        Err(es) => match es.iter().find(|e| e.message.contains("a bug in zedc")) {
            Some(e) => Outcome::Fault(e.message.clone()),
            None => Outcome::Refused,
        },
        Ok(u) => {
            let have: HashSet<&str> = u.defs.iter().map(|d| d.name.as_str()).collect();
            let lost: Vec<&str> = (defined(&stmts).into_iter())
                .filter(|n| !have.contains(n))
                .collect();
            match lost.is_empty() {
                true => Outcome::Kept,
                false => Outcome::Fault(format!("the unit lost {lost:?}")),
            }
        }
    })
}

#[test]
fn a_unit_that_checks_keeps_every_definition() {
    // The case that reached the fault on branch wt/remap-family before its fix: an uncalled
    // generic function's remap had no plan, and the whole unit was dropped.
    let src = "f(g) = g as (k -> v) into (k + 1 -> v);\nx = 1;\n";
    let u = elab(src).unwrap_or_else(|e| panic!("{e:?}"));
    assert!(u.get("x").is_some(), "the unit lost `x`");
    assert!(u.get("f").is_some(), "the unit lost `f`");
}

#[test]
fn every_program_that_checks_elaborates_every_top_level_definition() {
    // Every corpus program and step unit the checker accepts alone; the others (an import, a
    // form of a later layer, a program rejected on purpose) say nothing about the property.
    let mut paths: Vec<_> = corpus().into_iter().map(|(p, _)| p).collect();
    paths.extend(step_units());
    let (mut kept_all, mut refused, mut faults) = (0, 0, Vec::new());
    for path in &paths {
        let text = std::fs::read_to_string(path).unwrap();
        match kept(&text) {
            None => {}
            Some(Outcome::Kept) => kept_all += 1,
            Some(Outcome::Refused) => refused += 1,
            Some(Outcome::Fault(e)) => faults.push(format!("{}: {e}", path.display())),
        }
    }
    assert!(faults.is_empty(), "{}", faults.join("\n"));
    // A test that elaborated no program would pass the assertion above.
    assert!(
        kept_all > 0,
        "no program of {} elaborated ({refused} refused by elaboration)",
        paths.len()
    );
}
