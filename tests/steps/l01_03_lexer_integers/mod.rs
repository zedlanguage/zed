//! Step L1.3: integer literals in four bases, with `_` between digits.

use zedc::lex::{Tok, lex};

/// The integers of `text` as `(base, digits)`.
fn ints(text: &str) -> Vec<(u32, String)> {
    lex(text)
        .unwrap_or_else(|e| panic!("{text:?}: {e}"))
        .into_iter()
        .map(|t| match t.tok {
            Tok::Int { radix, digits } => (radix, digits),
            other => panic!("{text:?}: {other:?}"),
        })
        .collect()
}

fn int(radix: u32, digits: &str) -> (u32, String) {
    (radix, digits.into())
}

#[test]
fn literals_as_programs_write_them() {
    // A megabyte, a file mode, an RGB color, a flag mask, and a port.
    assert_eq!(
        ints("1_048_576 0o755 0xFF_88_00 0b1011 8080"),
        [
            int(10, "1048576"),
            int(8, "755"),
            int(16, "FF8800"),
            int(2, "1011"),
            int(10, "8080")
        ]
    );
}

#[test]
fn a_literal_keeps_every_digit_whatever_its_size() {
    // 2^64 and 2^128 + 1, which no machine integer holds: the width is chosen from the use.
    let big = "340282366920938463463374607431768211457";
    assert_eq!(
        ints(&format!("18446744073709551616 {big}")),
        [int(10, "18446744073709551616"), int(10, big)]
    );
}

#[test]
fn leading_zeros_are_decimal_digits_and_hex_digits_keep_their_case() {
    assert_eq!(
        ints("007 0 00 0xdeadBEEF"),
        [
            int(10, "007"),
            int(10, "0"),
            int(10, "00"),
            int(16, "deadBEEF")
        ]
    );
}

#[test]
fn golden_malformed_numbers() {
    let cases = [
        "timeout 200ms",
        "count 1__000",
        "count 1_000_",
        "mask 0b1012",
        "mode 0o789",
        "color 0x",
        "color 0xG0",
        "big 0X1F",
        "flags 0b_101",
        "day 1d",
    ];
    let out: Vec<String> = cases
        .iter()
        .map(|c| {
            let e = lex(c).unwrap_err();
            format!("{c:<16} [{}..{}] {e}", e.span.start, e.span.end)
        })
        .collect();
    insta::assert_snapshot!(out.join("\n"));
}

#[test]
fn a_number_ends_where_a_name_character_does_not_follow() {
    // `_` is a name character, so it must be followed by a digit to stay in the number.
    let toks = lex("12 3").unwrap();
    assert_eq!(
        toks.iter()
            .map(|t| (t.span.start, t.span.end))
            .collect::<Vec<_>>(),
        [(0, 2), (3, 4)]
    );
}
