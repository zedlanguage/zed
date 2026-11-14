//! Parsing each long form of a rule written as a list or a left recursion is linear in its
//! length, and so are building and formatting a long else chain: the benchmarks of
//! `lr4_assoc.rs`, whose tests parse each form, and build and write back an else chain, at small
//! lengths.

use std::collections::HashMap;

use zed_tests::scaling::check;
use zedc::ast::build;
use zedc::format::format_source;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, parse};

use crate::lr4_assoc::*;

/// The form at `n` and `8n`, lexed before the clock starts, then parsed.
fn scales(form: &Long) {
    const N: usize = 2_000;
    let inputs: HashMap<usize, (String, Vec<Token>)> = [N, 8 * N]
        .into_iter()
        .map(|m| {
            let text = (form.input)(m);
            let tokens = lex(&text).unwrap();
            (m, (text, tokens))
        })
        .collect();
    check(form.what, N, |m| {
        let (text, tokens) = &inputs[&m];
        parse(text, tokens, form.start, TOP).unwrap();
    });
}

macro_rules! scaling {
    ($($name:ident $form:ident;)*) => {
        $(
            #[test]
            fn $name() {
                scales(&$form);
            }
        )*
    };
}

scaling! {
    a_long_else_chain_is_linear ELSE_CHAIN;
    a_long_and_join_chain_is_linear AND_JOIN_CHAIN;
    a_long_full_join_is_linear FULL_JOIN;
    a_long_equality_chain_is_linear EQUALITY_CHAIN;
    a_long_ascending_chain_is_linear ASCENDING_CHAIN;
    a_long_out_pattern_is_linear OUT_PATTERN;
    a_long_in_pattern_is_linear IN_PATTERN;
    a_long_sort_key_list_is_linear SORT_KEY_LIST;
    a_long_suffix_chain_after_with_is_linear SUFFIX_CHAIN_AFTER_WITH;
    a_long_update_path_is_linear UPDATE_PATH;
    a_long_generator_list_is_linear GENERATOR_LIST;
    a_long_facet_list_is_linear FACET_LIST;
    a_long_grammar_alternation_is_linear GRAMMAR_ALTERNATION;
    a_long_grammar_sequence_is_linear GRAMMAR_SEQUENCE;
    a_long_indexed_definition_is_linear INDEXED_DEFINITION;
    a_long_keyed_push_is_linear KEYED_PUSH;
    a_long_boundary_is_linear BOUNDARY;
    a_long_annotation_list_is_linear ANNOTATION_LIST;
}

/// The built tree of a long else chain, and its formatting, are linear too.
#[test]
fn a_long_else_chain_builds_and_formats_in_linear_time() {
    const N: usize = 2_000;
    let texts: HashMap<usize, String> = [N, 8 * N]
        .into_iter()
        .map(|m| (m, (ELSE_CHAIN.input)(m)))
        .collect();
    check("building an else chain of n tails", N, |m| {
        let text = &texts[&m];
        let tokens = lex(text).unwrap();
        let tree = parse(text, &tokens, "Expr", TOP).unwrap();
        build(text, &tokens, &tree).unwrap();
    });
    let units: HashMap<usize, String> = texts
        .iter()
        .map(|(&m, t)| (m, format!("f(c) = {t};\n")))
        .collect();
    check("formatting an else chain of n tails", N, |m| {
        format_source(units[&m].as_bytes()).unwrap();
    });
}
