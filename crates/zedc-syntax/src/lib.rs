//! The syntax of the compiler `zedc`: the lexer, the parser, the syntax tree and the formatter.
//! `zedc` re-exports each module at its old path (`zedc::lex`, ...).

pub mod ast;
pub mod format;
pub mod lex;
pub mod parse;

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;
