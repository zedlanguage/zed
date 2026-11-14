//! Nests and chains past what a recursive parser, tree or formatter holds on a test thread's
//! 2 MiB stack (author P178: an unusual size is a benchmark). The old recursive code held 200
//! parentheses. `deep.rs` and `grammar_shape.rs` make each check at a few levels.

use zedc::ast::build;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

use crate::deep::{
    DEEP, FORMS, a_block_with_no_export_at_the_bottom, a_comment_at_the_bottom_of_blocks,
    a_missing_bracket_after_a_nest, an_error_at_the_bottom, an_error_in_a_string_hole, every_stage,
    parens,
};
use crate::grammar_shape::{builds, chains};

/// Each form of `deep.rs`, 4,000 deep, through every stage from text to text.
#[test]
fn each_form_4000_deep_passes_every_stage() {
    for (name, form) in FORMS {
        eprintln!("{name}");
        every_stage(&form(DEEP));
    }
}

/// Each error at the bottom of a nest 4,000 deep is reported at its place, and a comment at
/// the bottom of blocks 500 deep is kept.
#[test]
fn errors_and_a_comment_at_the_bottom_of_a_deep_nest() {
    an_error_at_the_bottom(DEEP);
    a_block_with_no_export_at_the_bottom(DEEP);
    an_error_in_a_string_hole(DEEP);
    a_missing_bracket_after_a_nest(DEEP);
    a_comment_at_the_bottom_of_blocks(500);
}

/// No depth is too great: a nest of twenty thousand parentheses, a hundred times what the 2 MiB
/// stack held, is lexed, parsed, built, printed and dropped on the test thread's stack.
#[test]
fn twenty_thousand_parentheses() {
    let text = parens(20_000);
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
    let e = build(&text, &tokens, &tree).unwrap();
    assert_eq!(e.to_string(), "1");
}

/// Neither the parser nor the builder may recurse on the length of a chain, nor may `Drop`.
#[test]
fn chains_of_a_hundred_thousand_operators_and_members_build() {
    for text in chains(100_000) {
        builds(&text);
    }
}
