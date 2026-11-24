//! Step L2.7c, its syntax and names (QUESTIONS A131 and A133): the list pattern `[a, b]`,
//! `[first, ..rest]` and `[..rest]`, whose rest, written last and alone named, binds the entries
//! after those written, and the record pattern `{x: p, y:}`, whose fields are matched by name
//! as a struct's are. Each builds, formats to itself, and binds its names in resolution, which
//! reports each as a form this version does not compile yet. The checking half of the step
//! (types, and the exhaustiveness of list patterns at the rule of low complexity) needs the
//! compiled struct and tuple patterns of step L2.7 and the lists of step L3.1: plan row
//! PAT-list-record-check.

mod bench;
mod forms;
mod scaling;

use zed_tests::step_helpers::l02_01_parser_structs::{build, fmt, sx};
use zedc::ast::Error;
use zedc::resolve::resolve_text;

/// The errors name resolution gives the unit `text`.
fn resolution_errors(text: &str) -> Vec<Error> {
    let (_, stmts) = build(text);
    resolve_text(&stmts, Some(text)).err().unwrap_or_default()
}
