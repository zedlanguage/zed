//! The grammars and inputs of the left-recursion benchmarks in `bench.rs` (COMPLEXITY.md F35),
//! each parsed here at small sizes (TEST-bench-move-rest, P170): every input a benchmark times
//! parses by its grammar from its start rule.

use std::collections::HashMap;

use zedc::lex::{Token, lex};
use zedc::parse::{Grammar, TOP, parse_with};

/// A benchmark: a grammar, its start rule, and the input of size `n`.
pub(super) struct Case {
    pub(super) grammar: &'static str,
    pub(super) start: &'static str,
    pub(super) input: fn(usize) -> String,
}

const SUM: &str = "
Lines = (Sum ';')* L1
Sum = Sum '+' Term L1
  | Term L1
Term = Term '*' Amount L1
  | Amount L1
Amount = '(' Sum ')' L1
  | INT L1
";

pub(super) const LONG_CHAIN: Case = Case {
    grammar: SUM,
    start: "Sum",
    input: |n| "1 + 2 * ".repeat(n) + "3",
};

pub(super) const SHORT_CHAINS: Case = Case {
    grammar: SUM,
    start: "Lines",
    input: |n| "1 + 2 * 3 + (4 + 5);\n".repeat(n),
};

/// A function's parameters at the head of a sum: `Lambda` fails after the whole list, and no
/// growth of the sum reads its seed, so the list is walked once however long the sum is.
pub(super) const FAILED_ALTERNATIVE: Case = Case {
    grammar: "
Sum = Lambda L1
  | Sum '+' Term L1
  | Term L1
Lambda = Tuple '->' Term L1
Tuple = '(' IDENT (',' IDENT)* ')' L1
Term = Tuple L1
  | INT L1
",
    start: "Sum",
    input: |n| format!("(x{}) {}", ", x".repeat(n), "+ 1 ".repeat(n)),
};

/// A check for a mistake before the left recursion: `Pending` reads no seed, so its long walk
/// over the tokens is done once.
pub(super) const LOOKAHEAD_BEFORE: Case = Case {
    grammar: "
Paid = !Pending Paid 'x' L1
  | 'x' L1
Pending = Items 'q' L1
Items = 'x'* L1
",
    start: "Paid",
    input: |n| "x ".repeat(n),
};

/// `Sum` tries an arrow over `Product` before each `+`, so each growth of `Sum` reads `Product`
/// at the head, a left-recursive rung that writes a list in its own body. The growth of
/// `Product` is over and read no seed of `Sum`, so its list is not walked again.
pub(super) const FINISHED_RUNG: Case = Case {
    grammar: "
Sum = Product '->' Sum L1
  | Sum '+' Product L1
  | Product L1
Product = Product '*' INT L1
  | '[' INT (',' INT)* ']' L1
  | INT L1
",
    start: "Sum",
    input: |n| format!("[1{}]{}", ", 2".repeat(n), " + 3".repeat(n)),
};

/// `Inner` reads the seed of `Outer` and walks a list after `(`. Each growth of `Sum` makes
/// `Attempt` stale at the first token, where `Attempt` reads `Inner` at the second token. The
/// growth moves only the first token's version, so `Inner` stays good and its list is walked
/// once. One version for all tokens would walk it at each growth.
pub(super) const STALE_RULE: Case = Case {
    grammar: "
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
",
    start: "Sum",
    input: |n| format!("(1{}){}", ", 2".repeat(n), " + 3".repeat(n)),
};

/// A `*` is no rule and has no memo entry, so one written in the left-recursive rule itself,
/// before a token that fails, is walked again at each growth. Quadratic, and no worse; moved
/// to a rule of its own it is linear (`FAILED_ALTERNATIVE`). COMPLEXITY.md F35.
pub(super) const LOOP_INSIDE: Case = Case {
    grammar: "A = 'x'* 'q' L1\n  | A 'x' L1\n  | 'x' L1\n",
    start: "A",
    input: |n| "x ".repeat(n),
};

/// The paper's worst case: lookahead over a left-recursive rule at every token grows a match
/// from each token to the end, which no memo entry can share. Quadratic, and no worse.
pub(super) const LOOKAHEAD_EVERY_TOKEN: Case = Case {
    grammar: "S = (&E 'x')* L1\nE = E 'x' L1\n  | 'x' L1\n",
    start: "S",
    input: |n| "x ".repeat(n),
};

/// `Inner` and `Outer` are a cycle of two rules, so they stay marked, and so does each rule that
/// reads them, at any token: `Items` here reads them after its first number. So `Items` is
/// matched again at each growth of `Sum` at its own token, and walks its list. Quadratic, and no
/// worse; a list over items that read no cycle is linear (`FAILED_ALTERNATIVE`). COMPLEXITY.md
/// F35.
pub(super) const CYCLE_UNDER_A_LIST: Case = Case {
    grammar: "
Sum = Attempt L1
  | Sum '+' INT L1
  | Items L1
Attempt = Items 'q' L1
Items = INT (',' Outer)* L1
Outer = Inner L1
Inner = Outer 'w' L1
  | INT L1
",
    start: "Sum",
    input: |n| format!("1{}{}", ", 2".repeat(n), " + 3".repeat(n)),
};

/// `case.input` lexed at each of `sizes`, so that timing covers the parse alone.
pub(super) fn lexed(case: &Case, sizes: &[usize]) -> HashMap<usize, (String, Vec<Token>)> {
    sizes
        .iter()
        .map(|&m| {
            let text = (case.input)(m);
            let tokens = lex(&text).unwrap();
            (m, (text, tokens))
        })
        .collect()
}

/// Parses `text` by the grammar of `case` from its start rule; the parse must succeed.
pub(super) fn parses(g: &Grammar, case: &Case, (text, tokens): &(String, Vec<Token>)) {
    parse_with(g, text, tokens, case.start, TOP).unwrap();
}

#[test]
fn each_benchmark_input_parses_by_its_grammar_at_small_sizes() {
    let cases = [
        LONG_CHAIN,
        SHORT_CHAINS,
        FAILED_ALTERNATIVE,
        LOOKAHEAD_BEFORE,
        FINISHED_RUNG,
        STALE_RULE,
        LOOP_INSIDE,
        LOOKAHEAD_EVERY_TOKEN,
        CYCLE_UNDER_A_LIST,
    ];
    for case in &cases {
        let g = Grammar::read(&[case.grammar]).unwrap();
        for (_, input) in lexed(case, &[1, 2, 9]) {
            parses(&g, case, &input);
        }
    }
}
