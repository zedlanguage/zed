use super::render;
use zed_tests::tokens::render_lines;
use zedc::lex::{Doc, lex, lex_with_docs};

/// The `sec:tour_failure` example of EXAMPLES.md, section 12, from the copy
/// `zed/fences/examples.md`: it lexes, and each form of the lexer it shows gives its tokens.
#[test]
fn expected_example_program() {
    let fence = zed_tests::fences::examples()
        .into_iter()
        .find(|f| f.text.starts_with("// [d4] sec:tour_failure"))
        .expect("EXAMPLES.md holds the sec:tour_failure example");
    let tokens = lex(&fence.text).unwrap_or_else(|e| panic!("{}: {e}", fence.at));
    let out = render_lines(&fence.text, &tokens);
    for piece in [
        "#syntaxError ( pos : int )",
        "?. server ?. port «else» 8080₍10₎ ;",
        "= «match» parse",
        "-> str[\"bad at \" ${pos}] ,",
        "r «is» «not» Config",
        "a «else» 0₍10₎ ) >< ( + ) ;",
    ] {
        assert!(out.contains(piece), "{piece}\n{out}");
    }
}

#[test]
fn doc_comments_are_collected_and_other_comments_dropped() {
    let src = "/// The order total.\n///\n////  a ruled line, not a doc\n//   a plain comment\n/** a block comment */\n///   indented text keeps all but one space\ntotal = 1;";
    let (tokens, docs) = lex_with_docs(src).unwrap();
    assert_eq!(render(&tokens), "total = 1₍10₎ ;");
    let texts: Vec<&str> = docs.iter().map(|d: &Doc| d.text.as_str()).collect();
    assert_eq!(
        texts,
        [
            "The order total.",
            "",
            "  indented text keeps all but one space"
        ]
    );
    assert_eq!(
        &src[docs[0].span.start..docs[0].span.end],
        "/// The order total."
    );
}

#[test]
fn block_comments_nest() {
    let src = "a /* outer /* inner */ still out */ b /* /* */ */ c";
    assert_eq!(render(&lex(src).unwrap()), "a b c");
    let src = "x /* /* only the inner closes */ y";
    let e = lex(src).unwrap_err();
    assert_eq!((e.span.start, e.span.end), (2, src.len()));
    assert_eq!(
        e.to_string(),
        "this block comment, opened with `/*`, is not closed before the end of the file. Write `*/` \
         where the comment should end."
    );
    // Two comments open inside it: each needs its own `*/`, and the message counts them.
    let src = "x /* /* /* only the innermost closes */ y";
    assert_eq!(
        lex(src).unwrap_err().to_string(),
        "this block comment, opened with `/*`, is not closed before the end of the file: block \
         comments nest, so each `/*` inside it needs its own `*/`, and 2 `*/` are missing. Write \
         the missing `*/`, the last where the comment should end."
    );
}

#[test]
fn a_comment_delimiter_in_a_string_is_text() {
    assert_eq!(
        render(&lex(r#"url = "http://x/*y*/"; // c"#).unwrap()),
        r#"url = str["http://x/*y*/"] ;"#
    );
}
