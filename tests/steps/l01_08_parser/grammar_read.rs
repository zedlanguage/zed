//! How the grammar reader reads `e % sep` (GRAMMAR-read-cost, COMPLEXITY.md F88): it keeps one
//! copy of `e`, so a chain or a nest of `%` is read in time linear in its length, and the
//! parser matches it as the `e (sep e)*` it stands for, node for node.

use std::collections::HashMap;

use zed_tests::scaling::check;
use zedc::lex::lex;
use zedc::parse::{Error, Grammar, Node, TOP, parse_with};

/// The nodes and root of the parse of `text` as `List`, or the error.
fn parsed(g: &Grammar, text: &str) -> Result<(Vec<Node>, usize), Error> {
    let tokens = lex(text).unwrap();
    parse_with(g, text, &tokens, "List", TOP).map(|mut t| (std::mem::take(&mut t.nodes), t.root))
}

/// A list of items, each `a` or `b` with an optional amount, separated by `,` or `;`: the
/// operand and the separator each hold a choice, so the branches each records are compared too.
#[test]
fn a_separated_list_parses_as_the_repetition_it_stands_for() {
    let item = "('a' | 'b' INT?)";
    let sep = "(',' | ';')";
    let short = Grammar::read(&[&format!("List = {item} % {sep} ','? L1\n")]).unwrap();
    let long = Grammar::read(&[&format!("List = {item} ({sep} {item})* ','? L1\n")]).unwrap();
    for text in [
        "a",
        "b 3",
        "a, b",
        "a; b 7, a,",
        "b 1; b 2; b 3; a",
        "a,,",
        "a b",
        ", a",
        "",
        "b 1;",
    ] {
        assert_eq!(parsed(&short, text), parsed(&long, text), "{text:?}");
    }
    assert!(parsed(&short, "a; b 7, a,").is_ok());
    assert!(parsed(&short, "a,,").is_err());
}

/// A separated list nested in a separated list: rows of cells, as a table is written.
#[test]
fn a_list_of_lists_parses_as_the_repetition_it_stands_for() {
    let short = Grammar::read(&["List = ('[' INT % ',' ']') % ';' L1\n"]).unwrap();
    let long =
        Grammar::read(&["List = ('[' INT (',' INT)* ']') (';' ('[' INT (',' INT)* ']'))* L1\n"])
            .unwrap();
    for text in ["[1]", "[1, 2]; [3]; [4, 5, 6]", "[1,]", "[1]; ", "[]"] {
        assert_eq!(parsed(&short, text), parsed(&long, text), "{text:?}");
    }
    assert!(parsed(&short, "[1, 2]; [3]; [4, 5, 6]").is_ok());
}

/// The grammar texts at `n` and `8n`, built before timing.
fn texts(n: usize, text: impl Fn(usize) -> String) -> HashMap<usize, String> {
    [n, 8 * n].into_iter().map(|m| (m, text(m))).collect()
}

/// `'x' % ',' % ',' …`: each `%` takes the whole expression before it as its operand. The old
/// reader copied that operand into both of its places, which doubled the expression per `%`.
#[test]
fn a_chain_of_separators_is_read_in_linear_time() {
    let texts = texts(2_000, |n| format!("List = 'x'{} L1\n", " % ','".repeat(n)));
    check("a grammar line of n chained `%`", 2_000, |n| {
        Grammar::read(&[&texts[&n]]).unwrap();
    });
}

/// `(('x' % ',') % ',') …`: the same through groups. The reader recurses once per group (the
/// `Complexity tradeoff:` comment at `Reader::within`), so the depths stay small.
#[test]
fn a_nest_of_separators_is_read_in_linear_time() {
    let texts = texts(32, |n| {
        let open = "(".repeat(n);
        let close = " % ',')".repeat(n);
        format!("List = {open}'x'{close} L1\n")
    });
    check("a grammar line of n nested `%`", 32, |n| {
        Grammar::read(&[&texts[&n]]).unwrap();
    });
}
