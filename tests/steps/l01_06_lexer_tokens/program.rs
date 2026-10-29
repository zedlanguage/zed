use super::render;
use zedc::lex::{Doc, lex, lex_with_docs};

/// The `sec:tour_failure` example of EXAMPLES.md, copied.
const TOUR_FAILURE: &str = r#"// [d4] sec:tour_failure
parse : (String) -> Config | #syntaxError(pos: int)     // an assumed input, shown as a type — no ';' (sec:lexical)
conf = parse(text) else defaultConfig;
port = parse(text)?.server?.port else 8080;
msg  = match parse(text) { #syntaxError(pos:) -> "bad at ${pos}", c -> c.name };
results = files.map(f -> read(f)).map(b -> parse(b));   // File -> Config | #syntaxError(pos: int) | #ioError | #notFound: the atoms ride through
good = results.where(r -> r is Config);
bad  = results.where(r -> r is not Config);
amounts = files.map(f -> int(read(f)));                 // int | #invalid | #ioError | #notFound
sumKept   = amounts.where(a -> a is int) >< (+);
sumZeroed = amounts.map(a -> a else 0) >< (+);
"#;

#[test]
fn golden_example_program() {
    let tokens = lex(TOUR_FAILURE).unwrap();
    // One rendered line per source line.
    let mut lines: Vec<String> = Vec::new();
    for line in TOUR_FAILURE.lines().scan(0, |at, l| {
        let start = *at;
        *at += l.len() + 1;
        Some((start, *at))
    }) {
        let on: Vec<_> = tokens
            .iter()
            .filter(|t| t.span.start >= line.0 && t.span.start < line.1)
            .cloned()
            .collect();
        lines.push(render(&on));
    }
    insta::assert_snapshot!(lines.join("\n"));
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
        "the block comment is not closed (1 `*/` missing)"
    );
}

#[test]
fn a_comment_delimiter_in_a_string_is_text() {
    assert_eq!(
        render(&lex(r#"url = "http://x/*y*/"; // c"#).unwrap()),
        r#"url = str["http://x/*y*/"] ;"#
    );
}
