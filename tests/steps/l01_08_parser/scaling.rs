//! How long left-recursive parsing takes (COMPLEXITY.md F35): a growth matches again only the
//! rules at its token that read a seed still growing, so a chain is linear in its length.

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

/// A ladder of `k` left-recursive rungs over an amount, rung `i` with the operator `o{i}`.
fn ladder(k: usize) -> Grammar {
    let mut text = String::from("R0 = INT L1\n");
    for i in 1..=k {
        let below = i - 1;
        text += &format!("R{i} = R{i} 'o{i}' R{below} L1\n  | R{below} L1\n");
    }
    Grammar::read(&[&text]).unwrap()
}

/// With its operators on the top rung, each operand passes through every rung. A rung's match,
/// once ended, reads no seed of the rung above, so each is matched once at each token: the
/// work is linear in the rungs, not quadratic.
#[test]
fn each_operand_costs_a_constant_per_rung() {
    let grammars: HashMap<usize, Grammar> = [8, 64].map(|k| (k, ladder(k))).into();
    let texts: HashMap<usize, String> = [8, 64]
        .map(|k| (k, format!("1 o{k} ").repeat(100) + "2"))
        .into();
    let tokens: HashMap<usize, Vec<Token>> =
        texts.iter().map(|(k, t)| (*k, lex(t).unwrap())).collect();
    check("a ladder of n rungs", 8, |k| {
        parse_with(
            &grammars[&k],
            &texts[&k],
            &tokens[&k],
            &format!("R{k}"),
            TOP,
        )
        .unwrap();
    });
}

/// A function's parameters at the head of a sum: `Lambda` fails after the whole list, and no
/// growth of the sum reads its seed, so the list is walked once however long the sum is.
#[test]
fn a_long_alternative_that_failed_is_not_walked_again_at_each_growth() {
    let g = Grammar::read(&["
Sum = Lambda L1
  | Sum '+' Term L1
  | Term L1
Lambda = Tuple '->' Term L1
Tuple = '(' IDENT (',' IDENT)* ')' L1
Term = Tuple L1
  | INT L1
"])
    .unwrap();
    let inputs = inputs(1_000, |n| {
        format!("(x{}) {}", ", x".repeat(n), "+ 1 ".repeat(n))
    });
    check("a list of n names and n operators", 1_000, |n| {
        let (text, tokens) = &inputs[&n];
        parse_with(&g, text, tokens, "Sum", TOP).unwrap();
    });
}

/// A check for a mistake before the left recursion: `Pending` reads no seed, so its long walk
/// over the tokens is done once.
#[test]
fn a_lookahead_before_the_left_recursion_is_matched_once() {
    let g = Grammar::read(&["
Paid = !Pending Paid 'x' L1
  | 'x' L1
Pending = Items 'q' L1
Items = 'x'* L1
"])
    .unwrap();
    let inputs = inputs(1_000, |n| "x ".repeat(n));
    check("a check over n tokens", 1_000, |n| {
        let (text, tokens) = &inputs[&n];
        parse_with(&g, text, tokens, "Paid", TOP).unwrap();
    });
}

/// `Sum` tries an arrow over `Product` before each `+`, so each growth of `Sum` reads `Product`
/// at the head, a left-recursive rung that writes a list in its own body. The growth of
/// `Product` is over and read no seed of `Sum`, so its list is not walked again.
#[test]
fn a_finished_rung_is_not_matched_again_by_the_rung_above() {
    let g = Grammar::read(&["
Sum = Product '->' Sum L1
  | Sum '+' Product L1
  | Product L1
Product = Product '*' INT L1
  | '[' INT (',' INT)* ']' L1
  | INT L1
"])
    .unwrap();
    let inputs = inputs(1_000, |n| {
        format!("[1{}]{}", ", 2".repeat(n), " + 3".repeat(n))
    });
    check("a list of n numbers and n operators", 1_000, |n| {
        let (text, tokens) = &inputs[&n];
        parse_with(&g, text, tokens, "Sum", TOP).unwrap();
    });
}

/// `Inner` reads the seed of `Outer` and walks a list after `(`. Each growth of `Sum` makes
/// `Attempt` stale at the first token, where `Attempt` reads `Inner` at the second token. The
/// growth moves only the first token's version, so `Inner` stays good and its list is walked
/// once. One version for all tokens would walk it at each growth.
#[test]
fn a_growth_leaves_a_stale_rule_at_a_later_token_good() {
    let g = Grammar::read(&["
Sum = Attempt L1
  | Sum '+' INT L1
  | '(' Inner ')' L1
  | INT L1
Attempt = Sum 'q' L1
  | '(' Outer 'z' L1
  | '(' Inner 'z' L1
Outer = Inner L1
Inner = Outer 'w' L1
  | INT (',' INT)* L1
"])
    .unwrap();
    let inputs = inputs(1_000, |n| {
        format!("(1{}){}", ", 2".repeat(n), " + 3".repeat(n))
    });
    check("a list of n numbers and n operators", 1_000, |n| {
        let (text, tokens) = &inputs[&n];
        parse_with(&g, text, tokens, "Sum", TOP).unwrap();
    });
}

/// A `*` is no rule and has no memo entry, so one written in the left-recursive rule itself,
/// before a token that fails, is walked again at each growth. Quadratic, and no worse; moved
/// to a rule of its own it is linear (`a_long_alternative_that_failed_...`). COMPLEXITY.md F35.
#[test]
fn a_loop_written_inside_the_left_recursive_rule_is_quadratic() {
    let g = Grammar::read(&["A = 'x'* 'q' L1\n  | A 'x' L1\n  | 'x' L1\n"]).unwrap();
    let inputs = inputs(250, |n| "x ".repeat(n));
    check_order("a loop over n tokens", 250, 2, |n| {
        let (text, tokens) = &inputs[&n];
        parse_with(&g, text, tokens, "A", TOP).unwrap();
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

/// `Inner` and `Outer` are a cycle of two rules, so they stay marked, and so does each rule that
/// reads them, at any token: `Items` here reads them after its first number. So `Items` is
/// matched again at each growth of `Sum` at its own token, and walks its list. Quadratic, and no
/// worse; a list over items that read no cycle is linear
/// (`a_long_alternative_that_failed_...`). COMPLEXITY.md F35.
#[test]
fn a_cycle_of_two_rules_under_a_list_at_the_growing_token_is_quadratic() {
    let g = Grammar::read(&["
Sum = Attempt L1
  | Sum '+' INT L1
  | Items L1
Attempt = Items 'q' L1
Items = INT (',' Outer)* L1
Outer = Inner L1
Inner = Outer 'w' L1
  | INT L1
"])
    .unwrap();
    let inputs = inputs(250, |n| format!("1{}{}", ", 2".repeat(n), " + 3".repeat(n)));
    check_order("a list of n numbers and n operators", 250, 2, |n| {
        let (text, tokens) = &inputs[&n];
        parse_with(&g, text, tokens, "Sum", TOP).unwrap();
    });
}
