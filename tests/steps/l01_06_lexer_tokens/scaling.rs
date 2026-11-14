//! The long texts the benchmarks of `bench.rs` lex and render, and what each must give, checked
//! here at small sizes (TEST-bench-move-rest, P170).

use zed_tests::tokens::render_lines;
use zedc::lex::{KEYWORDS, OPERATORS, Token, lex, lex_with_docs};

/// `n` lines of every keyword and operator, an annotation and an atom.
pub(super) fn keywords_and_operators(n: usize) -> String {
    let line = format!("{} {} @log #ok ", KEYWORDS.join(" "), OPERATORS.join(" "));
    line.repeat(n)
}

pub(super) fn lexes_every_keyword_and_operator(text: &str, n: usize) {
    let want = (KEYWORDS.len() + OPERATORS.len() + 2) * n;
    assert_eq!(lex(text).unwrap().len(), want);
}

/// Block comments nested `n` deep between two names.
pub(super) fn nested_comments(n: usize) -> String {
    format!("a {}{}b", "/* ".repeat(n), "*/ ".repeat(n))
}

pub(super) fn lexes_two_names(text: &str, _: usize) {
    assert_eq!(lex(text).unwrap().len(), 2);
}

/// `n` doc comments, each before a statement of four tokens.
pub(super) fn doc_comments(n: usize) -> String {
    "/// a doc\nx = 1;\n".repeat(n)
}

pub(super) fn lexes_a_doc_a_statement(text: &str, n: usize) {
    let (tokens, docs) = lex_with_docs(text).unwrap();
    assert_eq!((tokens.len(), docs.len()), (4 * n, n));
}

/// `n` lines of code and a comment, with their tokens.
pub(super) fn code_lines(n: usize) -> (String, Vec<Token>) {
    let text = "total = price * qty; // a comment\n".repeat(n);
    let tokens = lex(&text).unwrap();
    (text, tokens)
}

pub(super) fn renders_a_line_a_line((text, tokens): &(String, Vec<Token>), n: usize) {
    assert_eq!(render_lines(text, tokens).lines().count(), n);
}

#[test]
fn each_benchmark_text_lexes_as_its_benchmark_expects_at_small_sizes() {
    type Case = (fn(usize) -> String, fn(&str, usize));
    let cases: [Case; 3] = [
        (keywords_and_operators, lexes_every_keyword_and_operator),
        (nested_comments, lexes_two_names),
        (doc_comments, lexes_a_doc_a_statement),
    ];
    for (make, expect) in cases {
        for n in [1, 2, 9] {
            expect(&make(n), n);
        }
    }
    for n in [1, 2, 9] {
        renders_a_line_a_line(&code_lines(n), n);
    }
}
