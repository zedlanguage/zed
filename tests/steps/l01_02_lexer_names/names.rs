//! Where a name starts and ends, and what is the wildcard.

use zedc::lex::{ErrorKind, Tok, lex};

/// The tokens of `text`, a name as written and the wildcard as `(wildcard)`, or the error's
/// kind and byte offset.
fn toks(text: &str) -> Result<Vec<String>, (ErrorKind, usize)> {
    match lex(text) {
        Ok(ts) => Ok(ts
            .into_iter()
            .map(|t| match t.tok {
                Tok::Name(n) => n,
                Tok::Wildcard => "(wildcard)".into(),
                other => format!("{other:?}"),
            })
            .collect()),
        Err(e) => Err((e.kind, e.span.start)),
    }
}

fn ok(text: &str) -> Vec<String> {
    toks(text).unwrap_or_else(|e| panic!("{text:?}: {e:?}"))
}

#[test]
fn names_as_programs_write_them() {
    assert_eq!(
        ok("invoiceTotal unit_price x1 X_2 lineItems\ttaxRate\n"),
        [
            "invoiceTotal",
            "unit_price",
            "x1",
            "X_2",
            "lineItems",
            "taxRate"
        ]
    );
}

#[test]
fn a_bare_underscore_is_the_wildcard_and_an_underscore_before_a_name_character_is_a_name() {
    assert_eq!(
        ok("_ _unused __init__ _1 total_"),
        ["(wildcard)", "_unused", "__init__", "_1", "total_"]
    );
}

#[test]
fn a_trailing_prime_is_part_of_the_name_and_only_one_is_read() {
    // The next generation of a loop's state (sec:generations).
    assert_eq!(ok("pos' count' x'y"), ["pos'", "count'", "x'", "y"]);
    assert_eq!(toks("x''"), Err((ErrorKind::Unexpected('\''), 2)));
    assert_eq!(toks("'x"), Err((ErrorKind::Unexpected('\''), 0)));
}

#[test]
fn a_name_cannot_start_with_a_digit_or_a_combining_mark() {
    // A digit starts a number, which must not run into a name (step L1.3).
    assert!(matches!(toks("1st"), Err((ErrorKind::BadNumber(_), 0))));
    assert_eq!(toks("\u{301}a"), Err((ErrorKind::Unexpected('\u{301}'), 0)));
}

#[test]
fn spans_are_byte_ranges_of_the_text() {
    let ts = lex("größe  x'").unwrap();
    let spans: Vec<_> = ts.iter().map(|t| (t.span.start, t.span.end)).collect();
    assert_eq!(spans, [(0, 7), (9, 11)]);
}
