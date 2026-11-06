//! Parser helpers of step L1.10 (tests/steps/l01_10_lambdas_types_else_tuples).

use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// The s-expression of the expression `text`, or its error: `error: …`, or `syntax` when it
/// does not parse.
pub fn sx(text: &str) -> String {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Expr", TOP) {
        Err(_) => "syntax".into(),
        Ok(tree) => zedc::ast::build(text, &tokens, &tree)
            .map_or_else(|e| format!("error: {e}"), |e| e.to_string()),
    }
}
