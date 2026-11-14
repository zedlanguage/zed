//! DESIGN.md sec:lexical, the string row: in a `"""` string whose closing `"""` begins its line,
//! "a line of only spaces and tabs becomes empty", whatever its length
//! (FAIL-lex-deep-blank-line, found by TEST-complete-lex, author P189).

use zedc::lex::{Part, Tok, lex};

/// The parts of the one string literal `src`.
fn parts(src: &str) -> Vec<Part> {
    let mut toks = lex(src).unwrap_or_else(|e| panic!("{src:?}: {e}"));
    assert_eq!(toks.len(), 1, "{src:?}: {toks:?}");
    match toks.pop().unwrap().tok {
        Tok::Str(parts) => parts,
        other => panic!("{src:?}: {other:?}"),
    }
}

/// The text of the one string literal `src`, which has no hole.
fn text(src: &str) -> String {
    match parts(src).as_slice() {
        [] => String::new(),
        [Part::Text(s)] => s.to_string(),
        other => panic!("{src:?}: {other:?}"),
    }
}

#[test]
fn a_blank_line_deeper_than_the_indentation_becomes_empty() {
    assert_eq!(text("\"\"\"\n  a\n      \n  b\n  \"\"\""), "a\n\nb");
    assert_eq!(text("\"\"\"\n\ta\n\t\t\n\tb\n\t\"\"\""), "a\n\nb");
}

/// Blank lines shorter than the indentation, as long, longer, of spaces and tabs mixed, and the
/// last line before the closing `"""`, each become empty.
#[test]
fn a_blank_line_of_any_length_becomes_empty() {
    for (src, want) in [
        ("\"\"\"\n    a\n  \n    b\n    \"\"\"", "a\n\nb"),
        ("\"\"\"\n    a\n    \n    b\n    \"\"\"", "a\n\nb"),
        ("\"\"\"\n    a\n     \t  \n    b\n    \"\"\"", "a\n\nb"),
        ("\"\"\"\n  a\n\t \t\n  b\n  \"\"\"", "a\n\nb"),
        ("\"\"\"\n  a\n      \n  \"\"\"", "a\n"),
        ("\"\"\"\n      \n  a\n  \"\"\"", "\na"),
    ] {
        assert_eq!(text(src), want, "{src:?}");
    }
}

/// A line of spaces that a hole ends is no blank line, since it goes on in the hole: it loses
/// the indentation and keeps the rest (control). A line indented deeper keeps what lies past the
/// indentation (control).
#[test]
fn a_line_that_goes_on_in_a_hole_or_holds_text_keeps_its_deeper_spaces() {
    let p = parts("\"\"\"\n  a\n    ${x}\n  \"\"\"");
    let [Part::Text(head), Part::Hole { .. }] = p.as_slice() else {
        panic!("{p:?}")
    };
    assert_eq!(head.as_str(), "a\n  ");
    assert_eq!(text("\"\"\"\n  a\n      b\n  \"\"\""), "a\n    b");
}
