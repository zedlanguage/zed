//! The syntax of the compiler `zedc`: the lexer, the parser, the syntax tree and the formatter.
//! `zedc` re-exports each module at its old path (`zedc::lex`, ...).

pub mod ast;
pub mod fixed_width;
pub mod format;
pub mod lex;
pub mod parse;

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
use zed_testkit::seed;
