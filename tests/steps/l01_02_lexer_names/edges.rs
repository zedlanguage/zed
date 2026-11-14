//! Completeness of names (TEST-complete-lex, author P189): the wildcard and a keyword before a
//! `'`, each character `Space` takes between two names, and each control character it does not
//! take. The lexer and the grammar engine read each case alike. The case list is
//! `COMPLETENESS.md`.

use zed_tests::step_helpers::m0_03_grammar_tools::{design, spec_dir};
use zed_tools::spec::Spec;
use zedc::lex::{ErrorKind, Tok, lex};

use super::invisible::invisible;

/// Whether the grammar engine reads a text, from a spec in the directory `name`, one per test
/// since the tests run at once.
fn engine(name: &str) -> impl Fn(&str) -> bool {
    let dir = spec_dir(name, &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    move |text| zed_tools::syntax::lex(&spec.lexical, text).is_ok()
}

#[test]
fn a_prime_after_the_wildcard_or_a_keyword_is_an_error() {
    let engine_reads = engine("names_edges_prime");
    // DESIGN.md sec:lexical: `Wildcard = '_' !NameChar` and `Keyword = KeywordWord !NameChar`,
    // and `'` is no name character, so each is read first and the `'` starts no token.
    for (text, at) in [("_'", 1), ("x = _';", 5), ("if'", 2), ("true'", 4)] {
        let e = lex(text).expect_err(text);
        assert_eq!(
            (e.kind, e.span.start),
            (ErrorKind::Unexpected('\''), at),
            "{text}"
        );
        assert!(!engine_reads(text), "{text}");
    }
    // A longer word is a name and takes its `'`.
    assert_eq!(lex("iff'").unwrap()[0].tok, Tok::Name("iff'".into()));
    assert_eq!(lex("_x'").unwrap()[0].tok, Tok::Name("_x'".into()));
}

#[test]
fn each_character_space_takes_separates_two_names() {
    let engine_reads = engine("names_edges_space");
    // `Space = [ \t\r\n]+`: a `\r` that `load` has not turned into `\n` is space too.
    for text in ["a b", "a\tb", "a\nb", "a\rb", "a\r\nb", "a \t\r\n b"] {
        let names: Vec<_> = lex(text).unwrap().into_iter().map(|t| t.tok).collect();
        assert_eq!(
            names,
            [Tok::Name("a".into()), Tok::Name("b".into())],
            "{text:?}"
        );
        assert!(engine_reads(text), "{text:?}");
    }
}

#[test]
fn a_control_character_space_does_not_take_is_an_error_named_by_its_code_point() {
    let engine_reads = engine("names_edges_control");
    // Form feed, vertical tab, delete and next line (U+0085) are of general category Cc.
    for (c, hex) in [
        ('\u{c}', "C"),
        ('\u{b}', "B"),
        ('\u{7f}', "7F"),
        ('\u{85}', "85"),
    ] {
        let text = format!("a{c}b");
        let e = lex(&text).expect_err(&text);
        let message = e.to_string();
        assert_eq!(
            (e.kind, e.span.start, e.span.end, &message),
            (
                ErrorKind::Unexpected(c),
                1,
                1 + c.len_utf8(),
                &invisible(hex)
            ),
            "{text:?}"
        );
        assert!(!message.contains(c), "{text:?}");
        assert!(!engine_reads(&text), "{text:?}");
    }
}
