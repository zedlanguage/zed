//! Step L1.10: lambdas with a declaration's parameter list, `is` and `is not` with the type
//! expressions they test against, `else` with its atom-pattern form, and tuples.

mod elses;
mod fences;
mod lambdas;
mod tests_of_types;
mod tuples;

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
