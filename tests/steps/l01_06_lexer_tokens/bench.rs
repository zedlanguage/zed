//! Lexing keywords, operators, comments and doc comments, and rendering tokens by line, are of
//! order n log n in the length of the text (DESIGN.md Part G): the benchmarks of this step, run
//! by `tools/run_tests.sh --bench`. `scaling.rs` makes each of their checks at small sizes.

use zed_tests::scaling::{check, inputs};

/// TEST-dry-shared-units: `zedc::lex::in_parens` of one group of n operands, `(a0 + a1 + ...)`:
/// one lexing of the text and one pass over its tokens, the O(length) of its comment.
#[test]
fn one_group_of_n_operands_scales() {
    let texts = inputs(20_000, |n| {
        let terms: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        format!("({})", terms.join(" + "))
    });
    check("in_parens of one group of n operands", 20_000, |n| {
        assert!(zedc::lex::in_parens(&texts[&n]));
    });
}

use super::scaling::{
    code_lines, doc_comments, keywords_and_operators, lexes_a_doc_a_statement,
    lexes_every_keyword_and_operator, lexes_two_names, nested_comments, renders_a_line_a_line,
};

#[test]
fn many_keywords_and_operators_scale() {
    let texts = inputs(200, keywords_and_operators);
    check("lexing n lines of every keyword and operator", 200, |n| {
        lexes_every_keyword_and_operator(&texts[&n], n)
    });
}

#[test]
fn block_comments_nested_deep_scale() {
    let texts = inputs(20_000, nested_comments);
    check("lexing block comments nested n deep", 20_000, |n| {
        lexes_two_names(&texts[&n], n)
    });
}

#[test]
fn many_doc_comments_scale() {
    let texts = inputs(2_000, doc_comments);
    check("lexing n doc comments", 2_000, |n| {
        lexes_a_doc_a_statement(&texts[&n], n)
    });
}

#[test]
fn rendering_tokens_by_line_scales() {
    // Each line's tokens were found by a pass over every token of the text.
    let texts = inputs(2_000, code_lines);
    check("rendering the tokens of n lines", 2_000, |n| {
        renders_a_line_a_line(&texts[&n], n)
    });
}
