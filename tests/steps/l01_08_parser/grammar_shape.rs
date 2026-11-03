//! The shape of the trees of sec:grammar: a left-associative operator is a left-recursive rule,
//! a `~` alternative leaves no node of its own, and each form is a rule of its own, so a message
//! names the form written.

use zed_tests::trees::sx;
use zedc::ast::build;
use zedc::lex::lex;
use zedc::parse::{Grammar, TOP, parse, parse_with};

/// The bracketing of `text` as `start`.
fn tree(text: &str, start: &str) -> String {
    let tokens = lex(text).unwrap();
    sx(text, &tokens, &parse(text, &tokens, start, TOP).unwrap())
}

/// The syntax tree of the expression `text`.
fn expr(text: &str) -> String {
    let tokens = lex(text).unwrap();
    let parsed = parse(text, &tokens, "Expr", TOP).unwrap();
    build(text, &tokens, &parsed).unwrap().to_string()
}

/// The rule names of the nodes of the parse of `text`, root first.
fn nodes(text: &str, start: &str) -> Vec<&'static str> {
    let tokens = lex(text).unwrap();
    let parsed = parse(text, &tokens, start, TOP).unwrap();
    (0..parsed.nodes.len())
        .rev()
        .map(|n| parsed.name(n))
        .collect()
}

#[test]
fn a_price_after_discount_and_tax_subtracts_from_the_left() {
    assert_eq!(
        tree("price - discount - tax + fee", "Expr"),
        "(((price - discount) - tax) + fee)"
    );
    assert_eq!(
        expr("price - discount - tax + fee"),
        "(+ (- (- price discount) tax) fee)"
    );
}

#[test]
fn a_rate_of_a_rate_divides_from_the_left() {
    assert_eq!(expr("km / hours / 2"), "(/ (/ km hours) 2)");
}

#[test]
fn a_power_of_a_power_stays_right_associative() {
    assert_eq!(tree("2 ** 3 ** 2", "Expr"), "(2 ** (3 ** 2))");
}

#[test]
fn a_comparison_chain_stays_flat() {
    assert_eq!(tree("0 < x <= 10", "Expr"), "(0 < x <= 10)");
    assert_eq!(tree("a == b == c", "Expr"), "(a == b == c)");
}

#[test]
fn a_call_chain_reads_from_the_left() {
    assert_eq!(
        expr("orders.paid(2024)[0].total"),
        "(. (index (call (. orders paid) 2024) 0) total)"
    );
}

#[test]
fn a_name_leaves_no_node_on_the_rungs_of_the_ladder() {
    assert_eq!(nodes("total", "Expr"), ["Expr", "Expr12", "Name"]);
}

#[test]
fn a_sum_has_one_node_per_operator() {
    let names = nodes("a + b + c", "Expr");
    assert_eq!(names.iter().filter(|n| **n == "Additive").count(), 2);
    assert!(!names.contains(&"Multiplicative"), "{names:?}");
    assert!(!names.contains(&"Primary"), "{names:?}");
}

#[test]
fn a_type_union_prints_flat_and_keeps_its_grouping() {
    assert_eq!(
        tree("Paid | Pending | Failed", "Type"),
        "((Paid | Pending) | Failed)"
    );
    assert_eq!(
        tree("Paid | (Pending | Failed)", "Type"),
        "(Paid | (( (Pending | Failed) )))"
    );
}

#[test]
fn an_alternative_past_its_ring_is_not_tried_through_a_mark() {
    let g = Grammar::read(&["E = ~T L5\n  | 'x' L1\nT = 'y' L5\n"]).unwrap();
    let text = "y";
    let tokens = lex(text).unwrap();
    assert!(parse_with(&g, text, &tokens, "E", 1).is_err());
    assert!(parse_with(&g, text, &tokens, "E", 5).is_ok());
}

#[test]
fn a_marked_alternative_gives_the_node_of_the_rule_it_names() {
    let g = Grammar::read(&["E = &'y' ~T L1\nT = 'y' L1\n"]).unwrap();
    let text = "y";
    let tokens = lex(text).unwrap();
    let parsed = parse_with(&g, text, &tokens, "E", TOP).unwrap();
    assert_eq!(parsed.nodes.len(), 1);
    assert_eq!(parsed.nodes[parsed.root].kids, [] as [usize; 0]);
}

#[test]
fn a_mark_is_refused_outside_the_top_of_its_alternative() {
    for (rule, want) in [
        (
            "E = 'x' (~T) L1\n",
            "a ~ mark must stand at the top of its alternative",
        ),
        ("E = ~T ~T L1\n", "an alternative holds at most one ~ mark"),
        ("E = ~'x' L1\n", "a ~ mark must be on a plain rule name"),
        ("E = ~IDENT L1\n", "a ~ mark must be on a plain rule name"),
        ("E = 'x' ~T L1\n", "beside a ~ mark"),
        ("E = ~T L2\n", "E marks T at L2, above its lowest layer L1"),
    ] {
        let text = format!("{rule}T = 'y' L1\n");
        let err = Grammar::read(&[&text]).unwrap_err().to_string();
        assert!(err.contains(want), "{rule}: {err}");
    }
}

/// Each tree below has one nesting per operator, so neither the parser nor the builder may
/// recurse on the length of a chain, nor may `Drop`.
#[test]
fn a_chain_of_a_million_operators_builds() {
    let text = "1 + ".repeat(1_000_000) + "2";
    let tokens = lex(&text).unwrap();
    let parsed = parse(&text, &tokens, "Expr", TOP).unwrap();
    build(&text, &tokens, &parsed).unwrap();
}

#[test]
fn a_chain_of_a_million_members_builds() {
    let text = "a".to_string() + &".b".repeat(1_000_000);
    let tokens = lex(&text).unwrap();
    let parsed = parse(&text, &tokens, "Expr", TOP).unwrap();
    build(&text, &tokens, &parsed).unwrap();
}
