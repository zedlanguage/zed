//! How long the grammar of sec:grammar takes on the forms its left-recursive rules read: each
//! chain is linear in its length, and each lookahead over them is matched once at its token.

use std::collections::HashMap;

use zed_tests::scaling::check;
use zedc::ast::build;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, parse};

/// `input(n)` lexed at `n` and `8n`, so that timing covers the parse alone.
fn inputs(n: usize, input: impl Fn(usize) -> String) -> HashMap<usize, (String, Vec<Token>)> {
    [n, 8 * n]
        .into_iter()
        .map(|m| {
            let text = input(m);
            let tokens = lex(&text).unwrap();
            (m, (text, tokens))
        })
        .collect()
}

fn scales(what: &str, n: usize, start: &str, input: impl Fn(usize) -> String) {
    let inputs = inputs(n, input);
    check(what, n, |m| {
        let (text, tokens) = &inputs[&m];
        parse(text, tokens, start, TOP).unwrap();
    });
}

#[test]
fn a_long_sum_is_linear() {
    scales("a sum of n terms", 4_000, "Expr", |n| {
        "a + ".repeat(n) + "b"
    });
}

#[test]
fn a_long_sum_builds_in_linear_time() {
    let inputs = inputs(4_000, |n| "a + ".repeat(n) + "b");
    let trees: HashMap<usize, _> = inputs
        .iter()
        .map(|(n, (text, tokens))| (*n, parse(text, tokens, "Expr", TOP).unwrap()))
        .collect();
    check("the syntax tree of a sum of n terms", 4_000, |m| {
        let (text, tokens) = &inputs[&m];
        std::mem::forget(build(text, tokens, &trees[&m]).unwrap());
    });
}

#[test]
fn a_long_member_chain_is_linear() {
    scales("a chain of n members", 4_000, "Expr", |n| {
        "a".to_string() + &".b(1)".repeat(n)
    });
}

#[test]
fn a_long_type_union_is_linear() {
    scales("a union of n types", 4_000, "Type", |n| {
        "A | ".repeat(n) + "B"
    });
}

#[test]
fn a_long_dotted_path_is_linear() {
    scales("a path of n names", 4_000, "Path", |n| {
        "a".to_string() + &".b".repeat(n)
    });
}

#[test]
fn a_long_keypath_is_linear() {
    scales("a keypath of n keys", 4_000, "KeyPath", |n| {
        "a".to_string() + &".b[1]".repeat(n)
    });
}

/// `PlainArg` reads `!(Name ':') Expr` at each argument.
#[test]
fn a_call_with_many_arguments_is_linear() {
    scales("a call of n arguments", 4_000, "Expr", |n| {
        format!("f({}1)", "a + b, ".repeat(n))
    });
}

/// `Primary` reads `&('{' Item)` before a block, so the statements of a block in a block are
/// read by the lookahead and by the block, once each. The parser recurses on nesting, so this
/// runs on a thread of its own with a large stack.
#[test]
fn nested_blocks_are_linear() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            scales("n nested blocks", 500, "Expr", |n| {
                format!("x -> {}1{}", "{ y = ".repeat(n), "; y }".repeat(n))
            })
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_block_of_many_statements_is_linear() {
    scales("a block of n statements", 2_000, "Expr", |n| {
        format!("x -> {{ {}x }}", "y = x + 1 * 2; ".repeat(n))
    });
}

#[test]
fn a_program_of_many_functions_is_linear() {
    scales("a program of n functions", 1_000, "Unit", |n| {
        "double(x) = x * 2 + 1;\nhalf(y) = y.value / 2 - 1;\n".repeat(n)
    });
}
