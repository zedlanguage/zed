//! How long the grammar of sec:grammar takes on the forms its left-recursive rules read: each
//! chain is linear in its length, and each lookahead over them is matched once at its token.
//! The benchmarks of `grammar_scaling.rs`, whose test parses each form at small lengths.

use std::collections::HashMap;

use zed_tests::scaling::check;
use zedc::ast::build;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, parse};

use crate::grammar_scaling::*;

/// `form` lexed at `n` and `8n`, so that timing covers the parse alone.
fn lexed(n: usize, form: &Form) -> HashMap<usize, (String, Vec<Token>)> {
    [n, 8 * n]
        .into_iter()
        .map(|m| {
            let text = (form.input)(m);
            let tokens = lex(&text).unwrap();
            (m, (text, tokens))
        })
        .collect()
}

fn scales(n: usize, form: &Form) {
    let inputs = lexed(n, form);
    check(form.what, n, |m| {
        let (text, tokens) = &inputs[&m];
        parse(text, tokens, form.start, TOP).unwrap();
    });
}

#[test]
fn a_long_sum_is_linear() {
    scales(4_000, &SUM);
}

#[test]
fn a_long_sum_builds_in_linear_time() {
    let inputs = lexed(4_000, &SUM);
    let trees: HashMap<usize, _> = inputs
        .iter()
        .map(|(n, (text, tokens))| (*n, parse(text, tokens, "Expr", TOP).unwrap()))
        .collect();
    check("the syntax tree of a sum of n terms", 4_000, |m| {
        let (text, tokens) = &inputs[&m];
        build(text, tokens, &trees[&m]).unwrap();
    });
}

#[test]
fn a_long_member_chain_is_linear() {
    scales(4_000, &MEMBER_CHAIN);
}

#[test]
fn a_long_type_union_is_linear() {
    scales(4_000, &TYPE_UNION);
}

#[test]
fn a_long_dotted_path_is_linear() {
    scales(4_000, &DOTTED_PATH);
}

#[test]
fn a_long_keypath_is_linear() {
    scales(4_000, &KEYPATH);
}

#[test]
fn a_call_with_many_arguments_is_linear() {
    scales(4_000, &MANY_ARGUMENTS);
}

#[test]
fn nested_blocks_are_linear() {
    scales(2_000, &NESTED_BLOCKS);
}

#[test]
fn a_block_of_many_statements_is_linear() {
    scales(2_000, &MANY_STATEMENTS);
}

#[test]
fn a_program_of_many_functions_is_linear() {
    scales(1_000, &MANY_FUNCTIONS);
}

#[test]
fn functions_nested_many_deep_are_linear() {
    scales(1_000, &NESTED_FUNCTIONS);
}

#[test]
fn a_sum_of_many_calls_with_literals_is_linear() {
    scales(1_000, &CALLS_WITH_LITERALS);
}
