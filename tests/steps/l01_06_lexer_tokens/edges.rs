//! Completeness of atoms, annotations, operators and comments (TEST-complete-lex, author
//! P189): each word an atom or annotation may hold, each pair of operators that could be read
//! two ways, each comment at the edges of the file and of other comments, and the doc comment
//! forms. The case list is `COMPLETENESS.md`.

use super::render;
use zedc::lex::{ErrorKind, Span, Tok, comments, lex, lex_fence, lex_with_docs};

fn ok(src: &str) -> String {
    render(&lex(src).unwrap_or_else(|e| panic!("{src:?}: {e}")))
}

#[test]
fn an_atom_or_annotation_holds_any_name() {
    for (src, want) in [
        ("#_x", "#_x"),
        ("#x'", "#x'"),
        ("#x1", "#x1"),
        ("#X", "#X"),
        ("#if", "#if"),
        ("#true", "#true"),
        ("@if", "@if"),
        ("@test", "@test"),
        ("@x'", "@x'"),
        ("@_x", "@_x"),
        ("#a#b", "#a #b"),
        ("#a.b", "#a . b"),
        ("@a(b)", "@a ( b )"),
        ("f(#ok)", "f ( #ok )"),
    ] {
        assert_eq!(ok(src), want, "{src}");
    }
    // `#_` is the operator, as the grammar orders `#_` among the operators.
    assert_eq!(ok("a #_ b"), "a #_ b");
    assert_eq!(lex("#_").unwrap()[0].tok, Tok::Op("#_"));
}

#[test]
fn a_mark_with_no_name_after_it_is_an_error_at_the_mark() {
    for (src, at) in [
        ("#1", 0),
        ("#", 0),
        ("x #", 2),
        ("@", 0),
        ("@1", 0),
        ("@_", 0),
    ] {
        let e = lex(src).unwrap_err();
        assert_eq!(e.span.start, at, "{src}: {e}");
    }
    // `#'` and `@'`: a `'` alone is no name.
    assert!(lex("#'").is_err());
}

#[test]
fn a_keyword_differs_from_a_name_only_in_case() {
    assert_eq!(lex("If").unwrap()[0].tok, Tok::Name("If".into()));
    assert_eq!(lex("TRUE").unwrap()[0].tok, Tok::Name("TRUE".into()));
    assert_eq!(ok("if(x)"), "«if» ( x )");
    assert_eq!(ok("_(x)"), "_ ( x )");
}

#[test]
fn each_run_of_operator_characters_is_read_longest_first() {
    for (src, want) in [
        ("-->", "- ->"),
        ("....", "... ."),
        (".....", "... .."),
        ("x<-1", "x <- 1₍10₎"),
        ("x<-?1", "x <- ? 1₍10₎"),
        ("2*.5", "2₍10₎ *. 5₍10₎"),
        (":::", ":: :"),
        ("===", "== ="),
        ("!==", "!= ="),
        ("<=>", "<= >"),
        ("&&&", "&& &"),
        ("|||", "|| |"),
        ("+++", "++ +"),
        (">>", "> >"),
        ("<<", "< <"),
        ("->->", "-> ->"),
        ("..<=", "..< ="),
        ("?.?", "?. ?"),
        ("^^", "^ ^"),
        ("><>", ">< >"),
        ("\\\\", "\\ \\"),
    ] {
        assert_eq!(ok(src), want, "{src}");
    }
}

#[test]
fn an_arrow_or_ellipsis_beyond_ascii_is_no_operator() {
    for c in ['→', '…', '≤', '≠', '×', '−'] {
        let src = format!("a {c} b");
        let e = lex(&src).unwrap_err();
        assert_eq!((e.kind, e.span.start), (ErrorKind::Unexpected(c), 2), "{c}");
    }
    // In a fence of the documentation, `…` is an elision, read as a name, at the top level only.
    let toks = lex_fence("f(…) = …;").unwrap();
    assert_eq!(render(&toks), "f ( … ) = … ;");
    assert!(lex_fence("a → b").is_err());
    assert!(lex_fence(r#""${…}""#).is_err());
    // In a fence's string text it is text.
    assert_eq!(render(&lex_fence(r#""…""#).unwrap()), r#"str["…"]"#);
}

#[test]
fn a_comment_at_the_edges_of_the_file_and_of_tokens() {
    for (src, want) in [
        ("//", ""),
        ("// c", ""),
        ("a//c", "a"),
        ("a// c\nb", "a b"),
        ("/**/", ""),
        ("/***/", ""),
        ("/*/ */x", "x"),
        ("/* // */ x", "x"),
        ("// /*\nx", "x"),
        ("/* \" */ x", "x"),
        ("/* \"\"\" */ x", "x"),
        ("a/**/b", "a b"),
        ("a/ /b", "a / / b"),
        ("x /*/*/**/*/*/ y", "x y"),
        ("x */", "x * /"),
    ] {
        assert_eq!(ok(src), want, "{src:?}");
    }
}

#[test]
fn an_unclosed_block_comment_runs_to_the_end_of_the_file() {
    for (src, start) in [("a /*b", 2), ("/*", 0), ("/*/", 0), ("/* */ /*", 6)] {
        let e = lex(src).unwrap_err();
        assert!(matches!(e.kind, ErrorKind::BadComment(_)), "{src}");
        assert_eq!((e.span.start, e.span.end), (start, src.len()), "{src}");
    }
}

#[test]
fn each_form_of_a_doc_comment() {
    let docs = |src: &str| -> Vec<String> {
        lex_with_docs(src)
            .unwrap()
            .1
            .into_iter()
            .map(|d| d.text)
            .collect()
    };
    for (src, want) in [
        ("///", vec![""]),
        ("///x", vec!["x"]),
        ("/// x", vec!["x"]),
        ("///  x", vec![" x"]),
        ("///\tx", vec!["\tx"]),
        ("/// x \n", vec!["x "]),
        ("/// a\n/// b", vec!["a", "b"]),
        ("////", vec![]),
        ("//// x", vec![]),
        ("// / x", vec![]),
        ("/** x */", vec![]),
        ("/* /// x */", vec![]),
        ("x = \"/// x\";", vec![]),
        // DESIGN.md sec:lexical: a doc comment is a comment that starts with exactly three `/`,
        // wherever it stands; attaching it to a declaration is a later step's.
        ("x = 1; /// one", vec!["one"]),
    ] {
        assert_eq!(docs(src), want, "{src:?}");
    }
    let (_, d) = lex_with_docs("a\n/// b\nc").unwrap();
    assert_eq!(d[0].span, Span { start: 2, end: 7 });
}

#[test]
fn the_comments_of_a_file_are_listed_in_order_without_those_in_strings() {
    fn spans(src: &str) -> Vec<&str> {
        let toks = lex(src).unwrap();
        comments(src, &toks)
            .into_iter()
            .map(|s| &src[s.start..s.end])
            .collect()
    }
    assert_eq!(spans(""), Vec::<&str>::new());
    assert_eq!(spans("// a"), ["// a"]);
    assert_eq!(
        spans("/* a */ x // b\ny /* c /* d */ */"),
        ["/* a */", "// b", "/* c /* d */ */"]
    );
    assert_eq!(spans("/// d\nx"), ["/// d"]);
    // A comment in a string or in a hole is part of the string's token.
    assert_eq!(spans(r#"s = "// a ${x /* b */}"; // c"#), ["// c"]);
    assert_eq!(spans("a/**//**/b"), ["/**/", "/**/"]);
}
