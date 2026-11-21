use super::render;
use zed_tests::tokens::render_lines;
use zedc::lex::{Doc, lex, lex_with_docs};

/// The `sec:tour_failure` example of EXAMPLES.md, section 12, the case of
/// [`expected_example_program`]; [`the_example_is_that_of_the_spec`] checks it against the spec.
const TOUR_FAILURE: &str = "\
// [d4] sec:tour_failure
parse : (Utf8String) -> Config | #syntaxError(pos: int)     // an assumed input, shown as a type — no ';' (sec:lexical)
conf = parse(text) else #syntaxError -> defaultConfig;
port = parse(text)?.server?.port else #syntaxError -> 8080;
msg  = match parse(text) { #syntaxError(pos:) -> \"bad at ${pos}\", c -> c.name };
results = files.map(f -> read(f)).map(b -> parse(b));   // File -> Config | #syntaxError(pos: int) | #ioError | #notFound: the atoms ride through
good = results.where(r -> r is Config);
bad  = results.where(r -> r is not Config);
amounts = files.map(f -> int(read(f)));                 // int | #invalid | #ioError | #notFound
sumKept   = amounts.where(a -> a is int) >< (+);
sumZeroed = amounts.map(a -> a else (#invalid | #ioError | #notFound) -> 0) >< (+);";

/// [`TOUR_FAILURE`] is the one fence of EXAMPLES.md whose first line is its first line, read in
/// place (a later fence's first line goes on to name sec:ports too).
#[cfg(feature = "spec")]
#[test]
fn the_example_is_that_of_the_spec() {
    let found: Vec<String> = zed_tests::fences::examples()
        .into_iter()
        .filter(|f| f.text.starts_with("// [d4] sec:tour_failure\n"))
        .map(|f| f.text)
        .collect();
    assert_eq!(found, [TOUR_FAILURE]);
}

/// The `sec:tour_failure` example ([`TOUR_FAILURE`]) lexes, and each form of the lexer it shows
/// gives its tokens.
#[test]
fn expected_example_program() {
    let tokens = lex(TOUR_FAILURE).unwrap_or_else(|e| panic!("{e}"));
    let out = render_lines(TOUR_FAILURE, &tokens);
    for piece in [
        "#syntaxError ( pos : int )",
        "?. server ?. port «else» #syntaxError -> 8080₍10₎ ;",
        "= «match» parse",
        "-> str[\"bad at \" ${pos}] ,",
        "r «is» «not» Config",
        "a «else» ( #invalid | #ioError | #notFound ) -> 0₍10₎ ) >< ( + ) ;",
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
