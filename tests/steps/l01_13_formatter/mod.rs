//! Step L1.13: the source formatter. What it writes parses to the same statements and formats
//! to itself, and keeps every comment.

mod fences;
mod layout;

use zedc::ast::{Stmt, unit};
use zedc::format::format;
use zedc::lex::{Token, comments, lex_fence};
use zedc::parse::{TOP, parse};

/// The statements of the unit `text` and its tokens, or why it does not build.
fn build(text: &str) -> Result<(Vec<Token>, Vec<Stmt>), String> {
    let tokens = lex_fence(text).map_err(|e| e.to_string())?;
    let tree = parse(text, &tokens, "Unit", TOP).map_err(|e| e.to_string())?;
    let stmts = unit(text, &tokens, &tree).map_err(|e| e.message)?;
    Ok((tokens, stmts))
}

/// `stmts` without their spans, which formatting moves.
fn shape(stmts: &[Stmt]) -> String {
    let debug = format!("{stmts:?}");
    let mut out = String::new();
    let mut rest = &debug[..];
    while let Some(i) = rest.find("Span {") {
        out += &rest[..i];
        rest = &rest[i + rest[i..].find('}').unwrap() + 1..];
    }
    out + rest
}

/// The comments of `text`, sorted.
fn comment_texts(text: &str, tokens: &[Token]) -> Vec<String> {
    let mut cs: Vec<String> = comments(text, tokens)
        .iter()
        .map(|c| text[c.start..c.end].to_string())
        .collect();
    cs.sort();
    cs
}

/// `text` formatted, after checking that the result builds to the same statements, keeps the
/// same comments, and formats to itself.
#[track_caller]
fn fmt(text: &str) -> String {
    let (tokens, stmts) = build(text).unwrap();
    let out = format(text, &tokens, &stmts);
    let (tokens2, stmts2) = build(&out).unwrap_or_else(|e| panic!("{e} in\n{out}"));
    assert_eq!(
        shape(&stmts),
        shape(&stmts2),
        "the statements changed in\n{out}"
    );
    assert_eq!(comment_texts(text, &tokens), comment_texts(&out, &tokens2));
    assert_eq!(format(&out, &tokens2, &stmts2), out, "not a fixed point");
    out
}
