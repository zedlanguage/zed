//! `{}` is the empty family wherever a brace is not in body position, and an empty block in
//! body position, after a match arm's or a lambda's `->`, an `else`, or an `if` or `for` head,
//! where a brace is a block whatever it contains (sec:lexical). An empty block exports nothing,
//! so it is an error with its own message naming the spelling of the empty family there.
//! Corpus program 19 wrote `#bad -> {}` for "no edits" and `#open(id:) -> { id -> #insert(0) }`
//! for a one-entry family; the second reads as a one-entry map in a brace that is a block, and is
//! rejected as a display in body position.

use super::check;

const EMPTY: &str = "error: this `{}` is an empty block, which exports nothing: a brace after \
                     `->`, `else`, or the head of an `if` or a `for` is a block; the empty family \
                     there is `{ {} }`, or `({})` after `->` or a fallback's `else`";

#[test]
fn the_empty_family_outside_body_position() {
    check(&[
        ("{}", "(map)"),
        ("({})", "(map)"),
        ("closing({})", "(call closing (map))"),
        (
            "patch(accts, delta: {})",
            "(call patch accts (delta: (map)))",
        ),
        (
            "{ accts = {}; accts }",
            "(block (= (accts) (map)) (return accts))",
        ),
        // A brace after a display entry's arrow is classified by its contents.
        ("{\"a\" -> {}}", "(map (-> (str \"a\") (map)))"),
    ]);
}

#[test]
fn the_empty_family_in_body_position_is_parenthesized_or_wrapped() {
    check(&[
        (
            "match tx { #open(id:) -> ({ id -> 0 }), #bad -> ({}) }",
            "(match tx (-> #open(id:) (map (-> id 0))) (-> #bad (map)))",
        ),
        (
            "match tx { #bad -> { {} } }",
            "(match tx (-> #bad (block (return (map)))))",
        ),
        ("tx -> ({})", "(fn (tx) (map))"),
        ("lookup(k) else ({})", "(else (call lookup k) (map))"),
        (
            "if ok { m } else { {} }",
            "(if ok (block (return m)) (block (return (map))))",
        ),
    ]);
}

#[test]
fn an_empty_block_in_body_position_is_rejected() {
    check(&[
        ("match tx { #bad -> {}, _ -> 1 }", EMPTY),
        ("tx -> {}", EMPTY),
        ("lookup(k) else {}", EMPTY),
        ("if ok { m } else {}", EMPTY),
        ("if ok {} else { m }", EMPTY),
        ("for k in m {}", EMPTY),
        // An `if` branch is a block, never a parenthesized display.
        ("if ok { m } else ({})", "syntax"),
    ]);
}

#[test]
fn a_brace_after_an_arm_arrow_is_a_block_whatever_it_holds() {
    check(&[
        // A block that returns the lambda `id -> 0` groups it; the one-entry family is
        // `({ id -> 0 })`.
        (
            "match tx { #open(id:) -> { (id -> 0) } }",
            "(match tx (-> #open(id:) (block (return (fn (id) 0)))))",
        ),
        // A block that binds and exports nothing keeps the general message.
        (
            "match tx { #bad -> { n = 1; } }",
            "error: this block exports nothing: end it with an expression or `return e;`",
        ),
    ]);
    // Without the grouping, the brace reads as the one-entry map and is rejected.
    assert!(
        super::sx("match tx { #open(id:) -> { id -> 0 } }")
            .starts_with("error: a brace after a match arm's `->` whose one content is the lambda")
    );
}
