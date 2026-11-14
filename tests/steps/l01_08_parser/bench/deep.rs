//! Each stage of each deep form of `deep.rs`, from text to text, is linear in the depth, and a
//! nest of blocks of lines is written at the order of its text: the benchmarks of `deep.rs`.
//! Its tests run each form through every stage at a few levels, and write a small nest of
//! blocks of lines; `bench/stack.rs` runs each form far deeper.

use std::collections::HashMap;
use std::sync::{Mutex, PoisonError};

use zed_tests::scaling::{check, check_order};
use zedc::ast::{Expr, build};
use zedc::format::format_source;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};

use crate::deep::*;

/// `form` at depths `n` and `8n`, lexed and parsed.
fn parsed(n: usize, form: fn(usize) -> String) -> HashMap<usize, (String, Vec<Token>, Tree)> {
    [n, 8 * n]
        .into_iter()
        .map(|m| {
            let text = form(m);
            let tokens = lex(&text).unwrap();
            let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
            (m, (text, tokens, tree))
        })
        .collect()
}

/// One form is measured at a time: forms measured together compete for memory, which slows
/// the larger size more than the smaller.
static MEASURING: Mutex<()> = Mutex::new(());

/// Each stage of `form` at depths n and 8n, the inputs made before the clock starts.
fn every_stage_scales(what: &str, form: fn(usize) -> String) {
    const N: usize = 200;
    let inputs = parsed(N, form);
    let units: HashMap<usize, String> = inputs
        .iter()
        .map(|(&m, (text, ..))| (m, format!("f(c) = {text};\n")))
        .collect();
    let exprs: HashMap<usize, Expr> = inputs
        .iter()
        .map(|(&m, (text, tokens, tree))| (m, build(text, tokens, tree).unwrap()))
        .collect();
    let _alone = MEASURING.lock().unwrap_or_else(PoisonError::into_inner);
    check(&format!("lexing {what}"), N, |m| {
        lex(&inputs[&m].0).unwrap();
    });
    check(&format!("parsing {what}"), N, |m| {
        let (text, tokens, _) = &inputs[&m];
        parse(text, tokens, "Expr", TOP).unwrap();
    });
    check(&format!("formatting {what}"), N, |m| {
        format_source(units[&m].as_bytes()).unwrap();
    });
    check(&format!("building and dropping {what}"), N, |m| {
        let (text, tokens, tree) = &inputs[&m];
        build(text, tokens, tree).unwrap();
    });
    check(&format!("printing {what}"), N, |m| {
        exprs[&m].to_string();
    });
}

macro_rules! every_stage_scales {
    ($($scales:ident $form:ident;)*) => {
        $(
            #[test]
            fn $scales() {
                every_stage_scales(stringify!($form), $form);
            }
        )*
    };
}

every_stage_scales! {
    parentheses_scale parens;
    a_long_sum_scales sum;
    prefix_operators_scale negations;
    powers_scale powers;
    lambdas_scale lambdas;
    calls_scale calls;
    named_arguments_scale named_calls;
    indexes_scale indexes;
    tuples_scale tuples;
    blocks_scale blocks;
    else_if_chains_scale else_ifs;
    ifs_in_branches_scale ifs_in_branches;
    else_defaults_scale defaults;
    string_holes_scale holes;
    parameter_defaults_scale lambda_defaults;
    patterns_scale patterns;
    field_patterns_scale field_patterns;
    grouped_types_scale grouped_types;
    function_types_scale arrow_types;
    tuple_types_scale tuple_types;
    deep_unions_scale unions_in_groups;
    differences_scale differences;
    long_unions_scale long_union;
}

/// The output itself has n² characters.
#[test]
fn deep_blocks_of_lines_are_written_at_the_order_of_their_text() {
    let units: HashMap<usize, String> = [250, 2_000]
        .into_iter()
        .map(|m| (m, nested_blocks(m)))
        .collect();
    check_order("nested blocks of two lines, by depth", 250, 2, |m| {
        writes_indented_lines(&units[&m], m)
    });
}
