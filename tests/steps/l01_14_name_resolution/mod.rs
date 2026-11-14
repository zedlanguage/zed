//! Step L1.14: name resolution. A bare name resolves in its block scopes, innermost outward,
//! then in the unit's top level, then in the prelude; one test per rule of that order, and
//! one per error a resolution reports.

mod above;
mod bench;
mod complete;
mod fences;
mod order;
pub(crate) mod scaling;
mod scopes;

use zedc::ast::{Stmt, unit};
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::{Kind, Ref, Resolution, resolve};

/// The resolution of the unit `text`, or its errors as `message [text]`, each note after it
/// as `; note [text]`.
fn run(text: &str) -> Result<Resolution, Vec<String>> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    run_stmts(text, &unit(text, &tokens, &tree).unwrap())
}

/// [`run`] on `stmts`, statements built from `text`.
fn run_stmts(text: &str, stmts: &[Stmt]) -> Result<Resolution, Vec<String>> {
    resolve(stmts).map_err(|es| {
        es.iter()
            .map(|e| {
                let mut out = format!("{} [{}]", e.message, &text[e.span.start..e.span.end]);
                for n in &e.notes {
                    out += &format!("; {} [{}]", n.text, &text[n.span.start..n.span.end]);
                }
                out
            })
            .collect()
    })
}

/// What the `n`-th (from 0) occurrence of the name `name` in `text` resolves to: the text and
/// kind of each binder, or the prelude word.
fn at(text: &str, name: &str, n: usize) -> Vec<String> {
    let r = run(text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    let start = text
        .match_indices(name)
        .filter(|(i, _)| {
            let ok = |c: Option<char>| !c.is_some_and(|c| c.is_alphanumeric() || c == '_');
            ok(text[..*i].chars().next_back()) && ok(text[i + name.len()..].chars().next())
        })
        .nth(n)
        .unwrap_or_else(|| panic!("no occurrence {n} of `{name}`"))
        .0;
    let (_, used) = r
        .uses
        .iter()
        // A type the builder writes for `main`'s header (QUESTIONS Q51) has an empty span at the
        // first use of its field, and is skipped.
        .find(|(s, _)| s.start == start && s.end > s.start)
        .unwrap_or_else(|| panic!("occurrence {n} of `{name}` is not a recorded use"));
    match used {
        Ref::Prelude(w) => vec![format!("prelude {w}")],
        Ref::Unit { unit, name } => vec![format!("unit {unit} {name}")],
        Ref::Main(p) => vec![format!("input {p}")],
        Ref::Bound(ids) => ids
            .iter()
            .map(|&i| {
                let b = &r.binders[i];
                let kind = match b.kind {
                    Kind::Binding => "binding",
                    Kind::Function => "function",
                    Kind::Param => "param",
                    Kind::Port => "port",
                    Kind::Pattern => "pattern",
                    Kind::Struct => "struct",
                    Kind::Type => "type",
                    Kind::TypeParam => "type-param",
                    Kind::Field => "field",
                    Kind::Method => "method",
                    Kind::Receiver => "receiver",
                    Kind::Unit => "qualifier",
                };
                format!("{kind} {}", &text[b.span.start..b.span.end])
            })
            .collect(),
    }
}

/// The errors of the unit `text`.
fn errors(text: &str) -> Vec<String> {
    run(text).err().unwrap_or_else(|| panic!("{text} resolves"))
}
