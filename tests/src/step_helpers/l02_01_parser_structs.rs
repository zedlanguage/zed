//! Parser helpers of step L2.1 (tests/steps/l02_01_parser_structs), which steps L1.11, L1.12,
//! L2.2, L2.7b, L3.1 and L6.1 use too: before DRY-test-helpers each of them had its own copy.

pub use super::l01_13_formatter::fmt;
use zedc::ast::{Error, Stmt, unit};
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;

/// The error `e` as a test table writes it: `error: …`, then each note as `; … at byte …`.
pub fn error_sx(e: &Error) -> String {
    let mut out = format!("error: {e}");
    for n in &e.notes {
        out += &format!("; {} at byte {}", n.text, n.span.start);
    }
    out
}

/// The statements of the unit `text`, one s-expression per line, or its error as
/// [`error_sx`] writes it, or `syntax` when it does not parse.
pub fn sx(text: &str) -> String {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Unit", TOP) {
        Err(_) => "syntax".into(),
        Ok(tree) => match unit(text, &tokens, &tree) {
            Err(e) => error_sx(&e),
            Ok(stmts) => stmts
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        },
    }
}

/// Checks each `(unit, its statements)` of `cases` with [`sx`].
#[track_caller]
pub fn check(cases: &[(&str, &str)]) {
    crate::tables::check(cases, sx);
}

/// The s-expression of the expression `text`, or its error as [`error_sx`] writes it, or
/// `syntax` when it does not parse. Step L1.10's `sx` is this without the notes.
pub fn expr_sx(text: &str) -> String {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Expr", TOP) {
        Err(_) => "syntax".into(),
        Ok(tree) => {
            zedc::ast::build(text, &tokens, &tree).map_or_else(|e| error_sx(&e), |e| e.to_string())
        }
    }
}

/// Checks each `(expression, its s-expression)` of `cases` with [`expr_sx`].
#[track_caller]
pub fn check_exprs(cases: &[(&str, &str)]) {
    crate::tables::check(cases, expr_sx);
}

/// The statements of the unit `text` and its tokens; panics when it does not build.
#[track_caller]
pub fn build(text: &str) -> (Vec<Token>, Vec<Stmt>) {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    let stmts = unit(text, &tokens, &tree).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    (tokens, stmts)
}

/// The errors name resolution gives the unit `text`, each as `message [text]`.
pub fn refused(text: &str) -> Vec<String> {
    let (_, stmts) = build(text);
    match resolve(&stmts) {
        Ok(_) => Vec::new(),
        Err(es) => es
            .iter()
            .map(|e| format!("{} [{}]", e.message, &text[e.span.start..e.span.end]))
            .collect(),
    }
}

/// Checks each `(unit, the errors name resolution gives it)` of `cases` with [`refused`].
#[track_caller]
pub fn check_refused(cases: &[(&str, &[&str])]) {
    crate::tables::check_lists(cases, refused);
}
