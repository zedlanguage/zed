//! The head flag of sec:grammar ("The head flag"): in the head of an `if`, a `match`, a `for`
//! generator or a `for` filter, a `{` after a complete operand begins the body, so neither a
//! block operand nor an `else` tail's block is read there; every bracket pair clears the flag,
//! so parentheses, a call, an array or the construct's own body restore both; a display, a
//! brace-led type and a struct update need no guard; and `break` stands at the level of `Expr`,
//! so `if c || break { 1 } else { 2 }` does not parse. Each case puts one construct in one
//! position and gives the tree sec:grammar builds, written from the grammar text.

use zed_tests::trees::sx;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

use super::head_cases::HEAD_CASES;

#[test]
fn each_construct_in_a_head_gives_the_tree_of_the_head_flag() {
    let mut wrong = Vec::new();
    for &(text, want) in HEAD_CASES {
        let tokens = lex(text).unwrap_or_else(|e| panic!("{text}: {e}"));
        let got = match parse(text, &tokens, "Expr", TOP) {
            Ok(tree) => sx(text, &tokens, &tree),
            Err(_) => "ERROR".to_string(),
        };
        if got != want {
            wrong.push(format!("{text}\n  got  {got}\n  want {want}"));
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {} wrong:\n{}",
        wrong.len(),
        HEAD_CASES.len(),
        wrong.join("\n")
    );
}
