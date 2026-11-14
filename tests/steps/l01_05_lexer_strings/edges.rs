//! Completeness of string literals (TEST-complete-lex, author P189): each escape at its
//! bounds, each `$` that is not a hole, the forms of `"""` stripping not covered elsewhere,
//! and what a hole may hold. The case list is `COMPLETENESS.md`.

use super::{parts, text};
use zedc::lex::lex;

/// The span and message of the error lexing `src`, which must be an error in a string.
fn error(src: &str) -> (usize, usize, String) {
    let e = lex(src).expect_err(src);
    (e.span.start, e.span.end, e.to_string())
}

#[test]
fn each_code_point_escape_at_its_bounds() {
    for (src, want) in [
        (r#""\u{0}""#, "\0"),
        (r#""\u{41}""#, "A"),
        (r#""\u{0000000041}""#, "A"),
        (r#""\u{1f600}""#, "\u{1f600}"),
        (r#""\u{D7FF}""#, "\u{d7ff}"),
        (r#""\u{E000}""#, "\u{e000}"),
        (r#""\u{10FFFF}""#, "\u{10ffff}"),
        (r#""\u{41}\u{42}""#, "AB"),
    ] {
        assert_eq!(text(src), want, "{src}");
    }
}

#[test]
fn each_code_point_that_names_no_character_is_an_error_over_the_escape() {
    for src in [
        r#""\u{DFFF}""#,
        r#""\u{dc00}""#,
        r#""\u{110000}""#,
        r#""\u{FFFFFFFF}""#,
        r#""\u{FFFFFFFFF}""#,
    ] {
        let (start, end, why) = error(src);
        assert_eq!((start, end), (1, src.len() - 1), "{src}");
        assert!(why.contains("names no Unicode character"), "{src}: {why}");
    }
}

#[test]
fn each_malformed_code_point_escape_is_an_error_at_its_backslash_u() {
    for src in [
        r#""\u{1F600""#,
        r#""\u{G}""#,
        r#""\u{ 41}""#,
        r#""\u""#,
        r#""\U{41}""#,
    ] {
        let (start, end, why) = error(src);
        assert_eq!((start, end), (1, 3), "{src}");
        assert!(
            why.starts_with("`\\u` starts a code point") || why.starts_with("`\\U` is no escape"),
            "{src}: {why}"
        );
    }
}

#[test]
fn an_escape_in_a_triple_quoted_string_is_decoded_as_in_a_one_line_string() {
    // An escaped `"` before the closing `"""` is text, so the text may end in `"` this way.
    assert_eq!(text(r#""""a\"""""#), "a\"");
    assert_eq!(text(r#""""\$ \${x} \\""""#), r"$ ${x} \");
    assert_eq!(text(r#""""\u{e9}""""#), "é");
    let (start, end, _) = error(r#""""\q""""#);
    assert_eq!((start, end), (3, 5));
}

#[test]
fn a_dollar_that_opens_no_hole_is_text() {
    for (src, want) in [
        (r#""$5""#, "$5"),
        (r#""a$""#, "a$"),
        (r#""$""#, "$"),
        (r#""$$""#, "$$"),
        (r#""$ {x}""#, "$ {x}"),
        (r#""{x}""#, "{x}"),
        (r#""}""#, "}"),
    ] {
        assert_eq!(text(src), want, "{src}");
    }
}

#[test]
fn the_empty_and_one_line_triple_quoted_strings() {
    assert_eq!(text(r#""""""""#), "");
    assert_eq!(text(r#""""abc""""#), "abc");
    assert_eq!(text("\"\"\"\n\"\"\""), "");
}

#[test]
fn stripping_reads_only_the_lines_of_the_delimiters() {
    // A space after the opening `"""` means it does not end its line: kept as written.
    assert_eq!(text("\"\"\" \n  a\n  \"\"\""), " \n  a\n  ");
    // A hole right after the opening `"""` means it does not end its line either.
    assert_eq!(
        parts("\"\"\"${x}\n  a\n  \"\"\""),
        [r#"${Name("x")}"#, "\n  a\n  "]
    );
    // A closing `"""` at the start of its line strips nothing but the two line breaks.
    assert_eq!(text("\"\"\"\n  a\n\"\"\""), "  a");
    // The closing line's indentation is the indentation removed, even when the first line is
    // indented further.
    assert_eq!(text("\"\"\"\n      a\n    b\n    \"\"\""), "  a\nb");
    // Tabs and spaces must match exactly, character by character.
    let (start, end, why) = error("\"\"\"\n \ta\n\t \"\"\"");
    assert_eq!((start, end), (4, 6));
    assert!(why.contains("indented less than the closing"), "{why}");
}

#[test]
fn a_hole_may_hold_any_token_and_nothing() {
    for (src, want) in [
        (r#""${}""#, vec!["${}"]),
        (r#""${ }""#, vec!["${}"]),
        (r#""${ {a} }""#, vec![r#"${Op("{") Name("a") Op("}")}"#]),
        (r#""${if}""#, vec![r#"${Keyword("if")}"#]),
        (r#""${#ok}""#, vec![r#"${Atom("ok")}"#]),
        (r#""${@test}""#, vec![r#"${Annot("test")}"#]),
        (r#""${_}""#, vec!["${Wildcard}"]),
        (r#""${1.5r}""#, vec![r#"${Rat("1.5")}"#]),
        (
            r#""${f("}")}""#,
            vec![r#"${Name("f") Op("(") Str([Text("}")]) Op(")")}"#],
        ),
        (
            r#""${f("{")}""#,
            vec![r#"${Name("f") Op("(") Str([Text("{")]) Op(")")}"#],
        ),
        (r#""${a /* } */}""#, vec![r#"${Name("a")}"#]),
    ] {
        assert_eq!(parts(src), want, "{src}");
    }
}

#[test]
fn a_lexical_error_in_a_hole_is_placed_in_the_file() {
    for (src, at) in [
        (r#""${1__0}""#, "1__0"),
        (r#""${x $ y}""#, "$"),
        (r#""${"\q"}""#, r"\q"),
        (r#"s = "a${0x}b";"#, "0x"),
    ] {
        let (start, end, _) = error(src);
        assert_eq!(&src[start..end], at, "{src}");
    }
}

#[test]
fn an_unclosed_hole_of_a_triple_quoted_string_is_an_error() {
    for src in ["\"\"\"${x\"\"\"", "\"\"\"${x\n", "\"\"\"${ {x }\"\"\""] {
        assert!(lex(src).is_err(), "{src:?}");
    }
}

#[test]
fn a_string_is_one_token_beside_others() {
    let kinds = |src: &str| -> Vec<String> {
        lex(src)
            .unwrap()
            .iter()
            .map(|t| format!("{:?}", t.tok))
            .collect()
    };
    assert_eq!(
        kinds(r#""a""b""#),
        [r#"Str([Text("a")])"#, r#"Str([Text("b")])"#]
    );
    assert_eq!(kinds(r#"f"a""#), [r#"Name("f")"#, r#"Str([Text("a")])"#]);
    assert_eq!(kinds(r#""a"++"b""#).len(), 3);
    // Four quotes: an empty `"""` string needs six, so this opens a `"""` string that the
    // fourth quote starts the text of and that never closes.
    assert!(lex(r#""""""#).is_err());
}

#[test]
fn nested_parts_print_and_compare_as_derived() {
    let tok = |src: &str| lex(src).unwrap().remove(0).tok;
    // `Part`'s `Debug` gives the output of `#[derive(Debug)]`: a hole of two tokens, the first
    // a string of two parts.
    assert_eq!(
        format!("{:?}", tok(r#""${"a${b}" c}""#)),
        r#"Str([Hole { tokens: [Token { tok: Str([Text("a"), Hole { tokens: [Token { tok: Name("b"), span: Span { start: 7, end: 8 } }], span: Span { start: 5, end: 9 } }]), span: Span { start: 3, end: 10 } }, Token { tok: Name("c"), span: Span { start: 11, end: 12 } }], span: Span { start: 1, end: 13 } }])"#
    );
    // Its equality looks through nested holes and tells apart each way two parts differ.
    assert_eq!(tok(r#""${"a${b}" c}""#), tok(r#""${"a${b}" c}""#));
    for (a, b) in [
        (r#""a""#, r#""${a}""#),
        (r#""a""#, r#""b""#),
        (r#""${a}""#, r#""${ a}""#),
        (r#""${a b}""#, r#""${ab }""#),
        (r#""${a  }""#, r#""${ a }""#),
        (r#""${"${a}"}""#, r#""${"${b}"}""#),
    ] {
        assert_ne!(tok(a), tok(b), "{a} {b}");
    }
}
