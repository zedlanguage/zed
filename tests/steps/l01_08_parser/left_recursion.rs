//! Left-recursive rules, by the Squirrel paper's algorithm: the cases of
//! `zed/grammar/leftrec.txt` give the reference parser's trees and errors here too, and a chain
//! of operators leans left.

use std::path::Path;

use zed_tests::trees::sx;
use zedc::lex::lex;
use zedc::parse::{Grammar, TOP, Tree, parse_with};

/// The tree of `text`, or `ERROR@k` with the token the parse stopped at and what it expected.
fn show(g: &Grammar, text: &str, start: &str, ring: u32) -> String {
    let tokens = lex(text).unwrap();
    match parse_with(g, text, &tokens, start, ring) {
        Ok(tree) => sx(text, &tokens, &tree),
        Err(e) => {
            let at = tokens
                .iter()
                .position(|t| t.span.start >= e.span.start)
                .unwrap_or(tokens.len());
            // The case file lists what was expected sorted, so that it does not depend on the
            // order in which the parse tries the alternatives; a message lists it in that order.
            let mut expected = e.expected;
            expected.sort();
            format!("ERROR@{at} {}", expected.join(" "))
        }
    }
}

#[test]
fn every_left_recursion_case_gives_its_tree() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../zed/grammar/leftrec.txt");
    let file = std::fs::read_to_string(path).unwrap();
    let mut blocks: Vec<(String, Vec<&str>)> = Vec::new();
    for line in file
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
    {
        match blocks.last_mut() {
            Some((_, cases)) if line.contains(" ::: ") => cases.push(line),
            Some((grammar, _)) if !line.starts_with("grammar ") => {
                grammar.push_str(line);
                grammar.push('\n');
            }
            _ => blocks.push((String::new(), Vec::new())),
        }
    }
    let (mut n, mut wrong) = (0, Vec::new());
    for (grammar, cases) in &blocks {
        let g = Grammar::read(&[grammar]).unwrap();
        for line in cases {
            let [start, text, want] = line.split(" ::: ").map(str::trim).collect::<Vec<_>>()[..]
            else {
                panic!("a case is `Rule ::: text ::: tree`: {line}");
            };
            let (start, ring) = match start.split_once('@') {
                Some((s, r)) => (s, r.parse().unwrap()),
                None => (start, TOP),
            };
            let got = show(&g, text, start, ring);
            n += 1;
            if !(got == want || want == "ERROR" && got.starts_with("ERROR")) {
                wrong.push(format!(
                    "{start}@{ring} | {text}\n  got  {got}\n  want {want}"
                ));
            }
        }
    }
    assert_eq!(n, 85, "the number of cases");
    assert!(
        wrong.is_empty(),
        "{} wrong:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

/// Arithmetic on an order's amounts: `-` and `/` give different answers leaning either way.
const AMOUNTS: &str = "
Sum = Sum '+' Term L1
  | Sum '-' Term L1
  | Term L1
Term = Term '*' Amount L1
  | Term '/' Amount L1
  | Amount L1
Amount = '(' Sum ')' L1
  | IDENT L1
  | INT L1
";

fn amounts() -> Grammar {
    Grammar::read(&[AMOUNTS]).unwrap()
}

#[test]
fn subtraction_and_division_lean_left() {
    let g = amounts();
    assert_eq!(
        show(&g, "price - discount - fee", "Sum", TOP),
        "((price - discount) - fee)"
    );
    assert_eq!(
        show(&g, "total / items * 100", "Sum", TOP),
        "((total / items) * 100)"
    );
    assert_eq!(
        show(&g, "net + tax - refund * 2 / rate + tip", "Sum", TOP),
        "(((net + tax) - ((refund * 2) / rate)) + tip)"
    );
}

#[test]
fn brackets_start_a_new_left_recursive_match() {
    let g = amounts();
    assert_eq!(
        show(&g, "price - (discount - fee) - tip", "Sum", TOP),
        "((price - (( (discount - fee) ))) - tip)"
    );
}

/// The nodes of the left spine from the root down: (alternative, first token, end token).
fn spine(tree: &Tree) -> Vec<(usize, usize, usize)> {
    let (mut out, mut n) = (Vec::new(), tree.root);
    loop {
        let node = &tree.nodes[n];
        out.push((node.alt, node.start, node.end));
        match node.kids.first() {
            Some(&k) if tree.nodes[k].rule == node.rule => n = k,
            _ => return out,
        }
    }
}

#[test]
fn each_operator_is_one_node_over_the_tokens_before_it() {
    let g = amounts();
    let text = "a - b + c";
    let tokens = lex(text).unwrap();
    let tree = parse_with(&g, text, &tokens, "Sum", TOP).unwrap();
    // `+` is alternative 0 and `-` alternative 1; alternative 2 is the seed.
    assert_eq!(spine(&tree), [(0, 0, 5), (1, 0, 3), (2, 0, 1)]);
}

#[test]
fn a_nodes_children_come_before_it() {
    let g = amounts();
    let text = "a - (b + c * d) - e / f";
    let tokens = lex(text).unwrap();
    let tree = parse_with(&g, text, &tokens, "Sum", TOP).unwrap();
    for (i, node) in tree.nodes.iter().enumerate() {
        assert!(node.kids.iter().all(|&k| k < i), "node {i}: {node:?}");
    }
}

#[test]
fn the_seed_is_the_only_operand_of_a_lone_amount() {
    let g = amounts();
    assert_eq!(show(&g, "price", "Sum", TOP), "price");
    assert_eq!(show(&g, "(price)", "Sum", TOP), "(( price ))");
}

#[test]
fn a_mistake_after_a_chain_is_reported_where_it_is() {
    let g = amounts();
    let text = "price - discount fee";
    let tokens = lex(text).unwrap();
    let err = parse_with(&g, text, &tokens, "Sum", TOP).unwrap_err();
    assert_eq!(&text[err.span.start..err.span.end], "fee");
    // In the order of the grammar: a product continues before a sum does.
    assert_eq!(err.expected, ["'*'", "'/'", "'+'", "'-'", "END"]);
}

#[test]
fn a_rule_that_only_calls_itself_fails_and_ends() {
    let g = Grammar::read(&["Loop = Loop L1\nMutual = Other L1\nOther = Mutual L1\n"]).unwrap();
    assert_eq!(show(&g, "x", "Loop", TOP), "ERROR@0 ");
    assert_eq!(show(&g, "x", "Mutual", TOP), "ERROR@0 ");
}
