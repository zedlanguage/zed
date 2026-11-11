//! Step L2.3: name resolution completed. Imports bring in the names of other units, by name or
//! through a qualifier; two imports that bring in one name make its uses ambiguous; the imports
//! of a package form no cycle; a `local` declaration is visible in its unit only; the manifest
//! marks the package root and names the prelude unit; and resolution binds the names of L2's
//! declarations: structs and their fields, types and their parameters, methods and their
//! receiver `this`, and the binders of `match` arms and of every pattern.

mod binders;
mod command;
mod corpus_words;
mod cycles;
mod imports;
mod later_forms;
mod later_words;
mod manifest;
mod queries;
pub(crate) mod scaling;
mod source;
mod units;

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use zedc::ast::unit;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::query::Db;
use zedc::resolve::{Alone, Kind, Ref, Resolved, resolve_in};
use zedc::unit::{Memory, Package, load};

/// The files `files`, each a name under the root and its text.
pub(crate) fn files(files: &[(&str, &str)]) -> Memory {
    Memory(
        files
            .iter()
            .map(|&(name, text)| (name.to_string(), Arc::from(text)))
            .collect::<HashMap<_, _>>(),
    )
}

/// The package of `files` that the unit `main` reaches.
fn package(fs: &[(&str, &str)]) -> Package {
    load(&mut Db::new(), &files(fs), &["main"])
}

/// The error zedc gives for the corpus's string type, pending plan item STR-types. DESIGN.md
/// (sec:order, "Defined words by layer") names the string types `U8String`, `Utf8String`,
/// `Utf16String` and `Utf32String` and has no `String`; the corpus writes `Utf8String`, which
/// zedc does not define until STR-types lands. Then each test that expects this error fails,
/// and the expectation goes.
const STR_TYPES_PENDING: &str = "the type `Utf8String` is not defined";

/// Whether `message` is a form a later step compiles or links, which this step only reaches. A
/// prelude word or type of a later layer is this step's own error, so it is kept.
fn later(message: &str) -> bool {
    zed_tests::is_not_yet(message)
        && !message.starts_with("the prelude word ")
        && !message.starts_with("the prelude type ")
}

/// The problems of the package `p` as `zedc` prints them, but for the forms of later steps.
fn mistakes(p: &Package) -> Vec<String> {
    p.report(Path::new(""))
        .into_iter()
        .filter(|m| !later(m))
        .collect()
}

/// What the `n`-th (from 0) occurrence of the word `word` in the unit `path` of `p` resolves to:
/// each binder's kind and text, and the unit an import brought it from; or the other unit's
/// definition it names.
fn use_of(p: &Package, path: &str, word: &str, n: usize) -> Vec<String> {
    let u = p.unit(path).unwrap_or_else(|| panic!("no unit `{path}`"));
    let text = u.text.as_ref().unwrap().as_ref().unwrap();
    let r = u
        .resolved
        .as_ref()
        .unwrap_or_else(|| panic!("`{path}` is not resolved"));
    describe(text, r, word, n)
}

/// What the `n`-th occurrence of `word` in `text`, resolved as `r`, resolves to: the use whose
/// text is `word`, else the shortest use that starts there.
fn describe(text: &str, r: &Resolved, word: &str, n: usize) -> Vec<String> {
    let start = text
        .match_indices(word)
        .filter(|(i, _)| {
            let ok = |c: Option<char>| !c.is_some_and(|c| c.is_alphanumeric() || c == '_');
            ok(text[..*i].chars().next_back()) && ok(text[i + word.len()..].chars().next())
        })
        .nth(n)
        .unwrap_or_else(|| panic!("no occurrence {n} of `{word}`"))
        .0;
    let (_, used) = r
        .res
        .uses
        .iter()
        .find(|(s, _)| s.start == start && s.end == start + word.len())
        .or_else(|| r.res.uses.iter().find(|(s, _)| s.start == start))
        .unwrap_or_else(|| panic!("occurrence {n} of `{word}` is not a recorded use"));
    match used {
        Ref::Prelude(w) => vec![format!("prelude {w}")],
        Ref::Unit { unit, name } => vec![format!("{unit}.{name}")],
        Ref::Bound(ids) => ids
            .iter()
            .map(|&i| {
                let b = &r.res.binders[i];
                let kind = format!("{:?}", b.kind).to_lowercase();
                let from = r.res.imports.get(&i).map_or(String::new(), |u| {
                    if b.kind == Kind::Unit {
                        format!(" for {u}")
                    } else {
                        format!(" from {u}")
                    }
                });
                format!("{kind} {}{from}", &text[b.span.start..b.span.end])
            })
            .collect(),
    }
}

/// The resolution of the unit `text`, read alone.
fn alone(text: &str) -> Resolved {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    let stmts = unit(text, &tokens, &tree).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    resolve_in(&stmts, &Alone)
}

/// The errors of the unit `text`, read alone, as `message [text]` with each note after it as
/// `; note [text]`, but for the forms of later steps.
fn errors(text: &str) -> Vec<String> {
    let r = alone(text);
    r.errors
        .iter()
        .chain(&r.later)
        .filter(|e| !later(&e.message))
        .map(|e| {
            let mut out = format!("{} [{}]", e.message, &text[e.span.start..e.span.end]);
            for n in &e.notes {
                out += &format!("; {} [{}]", n.text, &text[n.span.start..n.span.end]);
            }
            out
        })
        .collect()
}
