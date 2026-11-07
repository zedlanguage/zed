//! The syntax of the compiler `zedc`: the lexer, the parser, the syntax tree and the formatter.
//! `zedc` re-exports each module at its old path (`zedc::lex`, ...).

pub mod ast;
pub mod format;
pub mod lex;
pub mod parse;
