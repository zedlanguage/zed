//! DESIGN.md sec:lexical: a message names a character that may not show on screen (general
//! category Cc, among others) by its code point and never prints it. A backslash before such a
//! character is no escape (FAIL-lex-escape-invisible, found by TEST-complete-lex, author P189).

use zedc::lex::lex;

#[test]
fn a_backslash_before_a_character_that_does_not_show_names_it_by_its_code_point() {
    for (src, code) in [("\"\"\"a\\\nb\"\"\"", "U+000A"), ("\"a\\\tb\"", "U+0009")] {
        let why = lex(src).expect_err(src).to_string();
        assert!(
            why.contains(code) && !why.contains(['\n', '\t']),
            "{src:?}: {why:?}"
        );
    }
}

/// The other characters that may not show: a line break in a `"` string, a carriage return, a
/// zero width space (Cf), a no-break space (Zs), a combining mark alone (no width) and a private
/// use character (Co). Each is named by its code point, not printed, and the span is the
/// backslash and that character.
#[test]
fn every_character_that_may_not_show_is_named_by_its_code_point() {
    for (c, code) in [
        ('\n', "U+000A"),
        ('\r', "U+000D"),
        ('\u{200B}', "U+200B"),
        ('\u{A0}', "U+00A0"),
        ('\u{301}', "U+0301"),
        ('\u{E000}', "U+E000"),
    ] {
        let src = format!("\"a\\{c}b\"");
        let e = lex(&src).expect_err(&src);
        let why = e.to_string();
        assert!(
            why.contains(code) && !why.contains(c) && why.contains("is no escape"),
            "{src:?}: {why:?}"
        );
        assert_eq!((e.span.start, e.span.end), (2, 3 + c.len_utf8()), "{src:?}");
    }
}

/// A character that shows is quoted as written (control, as before the fix).
#[test]
fn a_backslash_before_a_character_that_shows_quotes_it() {
    for (src, quoted) in [("\"\\q\"", "`\\q`"), ("\"\\é\"", "`\\é`")] {
        let why = lex(src).expect_err(src).to_string();
        assert!(
            why.starts_with(&format!("{quoted} is no escape.")),
            "{why:?}"
        );
    }
}
