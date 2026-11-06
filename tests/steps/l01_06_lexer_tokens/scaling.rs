//! Lexing keywords, operators, comments and doc comments, and rendering tokens by line, are of
//! order n log n in the length of the text (DESIGN.md Part G).

use zed_tests::scaling::{check, inputs};
use zed_tests::tokens::render_lines;
use zedc::lex::{KEYWORDS, OPERATORS, lex, lex_with_docs};

#[test]
fn many_keywords_and_operators_scale() {
    let line = format!("{} {} @log #ok ", KEYWORDS.join(" "), OPERATORS.join(" "));
    let texts = inputs(200, |n| line.repeat(n));
    check("lexing n lines of every keyword and operator", 200, |n| {
        let want = (KEYWORDS.len() + OPERATORS.len() + 2) * n;
        assert_eq!(lex(&texts[&n]).unwrap().len(), want);
    });
}

#[test]
fn block_comments_nested_deep_scale() {
    let texts = inputs(20_000, |n| {
        format!("a {}{}b", "/* ".repeat(n), "*/ ".repeat(n))
    });
    check("lexing block comments nested n deep", 20_000, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), 2);
    });
}

#[test]
fn many_doc_comments_scale() {
    let texts = inputs(2_000, |n| "/// a doc\nx = 1;\n".repeat(n));
    check("lexing n doc comments", 2_000, |n| {
        let (tokens, docs) = lex_with_docs(&texts[&n]).unwrap();
        assert_eq!((tokens.len(), docs.len()), (4 * n, n));
    });
}

#[test]
fn rendering_tokens_by_line_scales() {
    // Each line's tokens were found by a pass over every token of the text.
    let texts = inputs(2_000, |n| {
        let text = "total = price * qty; // a comment\n".repeat(n);
        let tokens = lex(&text).unwrap();
        (text, tokens)
    });
    check("rendering the tokens of n lines", 2_000, |n| {
        let (text, tokens) = &texts[&n];
        assert_eq!(render_lines(text, tokens).lines().count(), n);
    });
}
