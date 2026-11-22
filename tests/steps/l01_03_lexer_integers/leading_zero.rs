//! A decimal number other than `0` does not start with `0`. In C, C++, Java, Go and JavaScript
//! outside strict mode `010` is the octal 8, and Python 3 rejects it for that reason (PEP 3127).
//! Zed rejects it, offering the number without the zeros and, for an integer whose digits are
//! all below 8, the `0o` form. As an error of the source it carries the sec:diagnostics row
//! "Decimal number with a leading `0`", the note that names the readings of other languages
//! and Zed's prefixes, and each repair (plan row PITFALL-leading-zero).

use zedc::lex::{ErrorKind, lex};
use zedc::rejection::Row;

/// The error lexing `text`: its kind is `LeadingZero`; its span and message.
fn error(text: &str) -> (usize, usize, String) {
    let e = lex(text).expect_err(text);
    assert!(
        matches!(e.kind, ErrorKind::LeadingZero { .. }),
        "{text:?}: {e:?}"
    );
    (e.span.start, e.span.end, e.to_string())
}

/// The note DESIGN.md's row "Decimal number with a leading `0`" asks for.
const NOTE: &str = "C, Java, Go and JavaScript read a number with a leading `0` as octal, \
                    so `0755` is 493 there; Zed writes octal as `0o755`, binary as `0b1011` \
                    and hexadecimal as `0xFF`";

#[test]
fn the_error_of_the_source_carries_the_row_the_note_and_each_repair() {
    for (text, repairs) in [
        ("x = 0755;", &["755", "0o755"][..]),
        ("x = 09;", &["9"][..]),
        ("x = 00.5;", &["0.5"][..]),
    ] {
        let e = zedc::ast::Error::from(lex(text).unwrap_err());
        assert_eq!(e.row, Some(Row::LeadingZero), "{text:?}");
        let notes: Vec<&str> = e.notes.iter().map(|n| n.text.as_str()).collect();
        let mut expected = vec![NOTE.to_string()];
        expected.extend(repairs.iter().map(|r| format!("repair: `{r}`")));
        assert_eq!(notes, expected, "{text:?}");
    }
}

/// The headline for a literal with an octal reading.
fn with_octal(n: &str, decimal: &str, octal: &str) -> String {
    format!(
        "`{n}` is no number: a leading `0` is octal in C. Try `{decimal}`, or `{octal}` for the octal number."
    )
}

/// The headline for a literal with no octal reading.
fn decimal_only(n: &str, decimal: &str) -> String {
    format!("`{n}` is no number: a leading `0` is octal in C. Try `{decimal}` instead.")
}

#[test]
fn a_decimal_integer_with_a_leading_zero_is_rejected_with_both_readings() {
    assert_eq!(error("010"), (0, 3, with_octal("010", "10", "0o10")));
    assert_eq!(
        error("x = 0755;"),
        (4, 8, with_octal("0755", "755", "0o755"))
    );
    assert_eq!(error("007"), (0, 3, with_octal("007", "7", "0o7")));
    assert_eq!(error("0_7"), (0, 3, with_octal("0_7", "7", "0o7")));
    // With a digit 8 or 9 there is no octal reading, and the decimal one is the only repair.
    assert_eq!(error("09"), (0, 2, decimal_only("09", "9")));
    // `00` is rejected too; its first repair is `0`.
    assert!(error("00").2.contains("Try `0`"), "{:?}", error("00"));
}

#[test]
fn a_float_or_rational_with_a_leading_zero_is_rejected() {
    assert_eq!(error("00.5"), (0, 4, decimal_only("00.5", "0.5")));
    assert_eq!(error("01e3"), (0, 4, decimal_only("01e3", "1e3")));
    assert_eq!(error("03r"), (0, 3, decimal_only("03r", "3r")));
}

#[test]
fn zero_and_the_other_forms_are_unchanged() {
    for text in [
        "0", "0x0F", "0o17", "0b01", "0.5", "0.05", "1.05", "1e-05", "0r", "0.5r", "10", "1_000",
    ] {
        assert!(lex(text).is_ok(), "{text}");
    }
}
