//! The grammar tools on a program deep and long enough that a parser nesting on the call stack
//! would overflow a test thread's 2 MiB stack (author P178: an unusual size is a benchmark).
//! The tools parse on the machine's heap stack, and the lexical grammar goes through the same
//! machine one character at a time. The same checks at small sizes are
//! `the_tools_take_a_nested_program_and_lex_a_sum` in `mod.rs`.

use crate::{lexes_a_sum, tools_take_a_nest};

#[test]
fn the_tools_take_a_deep_program_on_a_small_stack() {
    tools_take_a_nest(4000);
}

#[test]
fn the_tools_lex_a_long_program_on_a_small_stack() {
    lexes_a_sum(200_000);
}
