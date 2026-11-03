//! Step L7.3, the unit item `@log(#off);` (DESIGN.md sec:ports, Logging): an annotation of
//! the unit, an item of its own, which drops the log lines of every body in its unit. It
//! parses from layer L7, builds, formats, resolves and checks; the resolution records it for
//! the log port of step L7.3 to read. Each other way to write a unit item is refused with its
//! reason.

mod items;
mod resolution;
mod run;
mod scaling;

use zedc::ast::{Stmt, unit};
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::resolve::{Resolution, resolve};

/// The statements of the unit `text`, parsed at every layer.
fn build(text: &str) -> Vec<Stmt> {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    unit(text, &tokens, &tree).unwrap_or_else(|e| panic!("{e} in\n{text}"))
}

/// The resolution of the unit `text`, or its errors, each as `line:column: message` with its
/// notes as `; note line:column: text`.
fn resolved(text: &str) -> Result<Resolution, Vec<String>> {
    let at = |byte: usize| {
        let before = &text[..byte];
        let line = before.matches('\n').count() + 1;
        let column = byte - before.rfind('\n').map_or(0, |i| i + 1) + 1;
        format!("{line}:{column}")
    };
    resolve(&build(text)).map_err(|errors| {
        errors
            .iter()
            .map(|e| {
                let mut out = format!("{}: {}", at(e.span.start), e.message);
                for n in &e.notes {
                    out += &format!("; note {}: {}", at(n.span.start), n.text);
                }
                out
            })
            .collect()
    })
}
