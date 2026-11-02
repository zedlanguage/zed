//! How long left-recursive parsing takes (COMPLEXITY.md F35): growth costs a constant at
//! each token, and memo entries at other tokens stay good, so a chain is linear in its length.

use std::collections::HashMap;

use zed_tests::scaling::{check, check_order};
use zedc::lex::{Token, lex};
use zedc::parse::{Grammar, TOP, parse_with};

const SUM: &str = "
Lines = (Sum ';')* L1
Sum = Sum '+' Term L1
  | Term L1
Term = Term '*' Amount L1
  | Amount L1
Amount = '(' Sum ')' L1
  | INT L1
";

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

#[test]
fn a_long_chain_of_operators_is_linear() {
    let g = Grammar::read(&[SUM]).unwrap();
    let inputs = inputs(4_000, |n| "1 + 2 * ".repeat(n) + "3");
    check("a chain of n operators", 4_000, |n| {
        let (text, tokens) = &inputs[&n];
        parse_with(&g, text, tokens, "Sum", TOP).unwrap();
    });
}

#[test]
fn many_short_chains_are_linear() {
    let g = Grammar::read(&[SUM]).unwrap();
    let inputs = inputs(2_000, |n| "1 + 2 * 3 + (4 + 5);\n".repeat(n));
    check("n lines of short chains", 2_000, |n| {
        let (text, tokens) = &inputs[&n];
        parse_with(&g, text, tokens, "Lines", TOP).unwrap();
    });
}

/// A ladder of `k` left-recursive rungs over an amount.
fn ladder(k: usize) -> Grammar {
    let mut text = String::from("R0 = INT L1\n");
    for i in 1..=k {
        let below = i - 1;
        text += &format!("R{i} = R{i} '+' R{below} L1\n  | R{below} L1\n");
    }
    Grammar::read(&[&text]).unwrap()
}

/// Each rung ending its growth at a token matches every rung below it again, once, because
/// each growth moves the token's version: quadratic in the rungs, a constant of the grammar.
#[test]
fn each_operand_costs_at_most_the_square_of_the_rungs() {
    let grammars: HashMap<usize, Grammar> = [8, 64].map(|k| (k, ladder(k))).into();
    let text = "1 + ".repeat(100) + "2";
    let tokens = lex(&text).unwrap();
    check_order("a ladder of n rungs", 8, 2, |k| {
        parse_with(&grammars[&k], &text, &tokens, &format!("R{k}"), TOP).unwrap();
    });
}

/// The paper's worst case: lookahead over a left-recursive rule at every token grows a match
/// from each token to the end, which no memo entry can share. Quadratic, and no worse.
#[test]
fn lookahead_over_a_left_recursive_rule_at_every_token_is_quadratic() {
    let g = Grammar::read(&["S = (&E 'x')* L1\nE = E 'x' L1\n  | 'x' L1\n"]).unwrap();
    let inputs = inputs(250, |n| "x ".repeat(n));
    check_order("lookahead at n tokens", 250, 2, |n| {
        let (text, tokens) = &inputs[&n];
        parse_with(&g, text, tokens, "S", TOP).unwrap();
    });
}
