//! Step L1.12: declarations, namely functions in equation and block form with their `test`
//! tables, `main`'s port header, the whole-value push `p <- e`, and `if`/`else`.

mod fences;
mod functions;
mod ifs;
mod pushes;

use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// The statements of the unit `text`, one s-expression per line, or its error: `error: …`,
/// or `syntax` when it does not parse.
fn sx(text: &str) -> String {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Unit", TOP) {
        Err(_) => "syntax".into(),
        Ok(tree) => match zedc::ast::unit(text, &tokens, &tree) {
            Err(e) => format!("error: {e}"),
            Ok(stmts) => stmts
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        },
    }
}

#[track_caller]
fn check(cases: &[(&str, &str)]) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = sx(text);
            (got != want).then(|| format!("{text}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
