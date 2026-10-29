//! Step L1.9: postfix chains become syntax trees (`zedc::ast`): calls with positional, named
//! and curried arguments, `.`, `?.`, indexing, and the `5.double` rule of the lexer.

mod calls;
mod chains;
mod fences;

use zedc::ast::{Error, Expr, build};
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// The syntax tree of the expression `text`, parsed at the top ring.
fn ast(text: &str) -> Result<Expr, Error> {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Expr", TOP)
        .unwrap_or_else(|e| panic!("{text:?} does not parse: {e}"));
    build(text, &tokens, &tree)
}
