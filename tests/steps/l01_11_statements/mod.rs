//! Step L1.11: statements in a block, namely bindings with their tuple-destructuring targets
//! and `return` with a value or a comma list, and the `;` rule: every statement ends in `;`
//! but the trailing expression, which is the block's `return`.

mod blocks;
mod fences;
mod returns;

use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// The s-expression of the expression `text`, or its error: `error: …`, or `syntax` when it
/// does not parse.
fn sx(text: &str) -> String {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Expr", TOP) {
        Err(_) => "syntax".into(),
        Ok(tree) => zedc::ast::build(text, &tokens, &tree)
            .map_or_else(|e| format!("error: {e}"), |e| e.to_string()),
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
