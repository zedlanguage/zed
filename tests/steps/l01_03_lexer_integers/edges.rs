//! Completeness of integer literals (TEST-complete-lex, author P189): each base at its
//! smallest and with `_`, each malformed form with its message, and what may stand next to an
//! integer. The case list is `COMPLETENESS.md`.

use zedc::lex::{ErrorKind, Tok, lex};

/// The tokens of `text` in the form `Debug` prints them.
fn toks(text: &str) -> Vec<String> {
    lex(text)
        .unwrap_or_else(|e| panic!("{text:?}: {e}"))
        .into_iter()
        .map(|t| format!("{:?}", t.tok))
        .collect()
}

fn int(radix: u32, digits: &str) -> String {
    format!(
        "{:?}",
        Tok::Int {
            radix,
            digits: digits.to_string().into()
        }
    )
}

/// The error lexing `text`: its span and message.
fn error(text: &str) -> (usize, usize, String) {
    let e = lex(text).expect_err(text);
    assert!(matches!(e.kind, ErrorKind::BadNumber(_)), "{text:?}: {e:?}");
    (e.span.start, e.span.end, e.to_string())
}

#[test]
fn each_base_at_one_digit_and_with_groups() {
    let cases = [
        ("0", int(10, "0")),
        ("9", int(10, "9")),
        ("0x0", int(16, "0")),
        ("0xf", int(16, "f")),
        ("0xF", int(16, "F")),
        ("0o0", int(8, "0")),
        ("0o7", int(8, "7")),
        ("0b0", int(2, "0")),
        ("0b1", int(2, "1")),
        ("1_2", int(10, "12")),
        ("0xa_B_c", int(16, "aBc")),
        ("0o1_7", int(8, "17")),
        ("0b1_0_1", int(2, "101")),
        ("0b0000", int(2, "0000")),
        ("0x00ff", int(16, "00ff")),
        // `e` is a hex digit, so this is no exponent.
        ("0x1e5", int(16, "1e5")),
        ("0xE", int(16, "E")),
    ];
    for (text, want) in cases {
        assert_eq!(toks(text), [want], "{text}");
    }
}

#[test]
fn every_misplaced_underscore_is_named() {
    // `_` stands only between two digits of the number's base.
    let stray = |n: &str| {
        format!(
            "the number `{n}` has a `_` that does not stand between two digits, and `_` may \
             stand only between two digits, as in `1_000_000`. Remove that `_`."
        )
    };
    for (text, n) in [
        ("1_", "1_"),
        ("0xFF_", "0xFF_"),
        ("0o7_", "0o7_"),
        ("0b1_", "0b1_"),
        ("0x1__2", "0x1__2"),
        ("1_000__000", "1_000__000"),
    ] {
        assert_eq!(error(text), (0, text.len(), stray(n)), "{text}");
    }
    // Right after the base's mark no digit follows, so the mark is what is wrong.
    let no_digit = |p: char, base: u32, example: &str| {
        format!(
            "`0{p}` starts a number in base {base}, and no digit of base {base} follows it. Write \
             the digits after `0{p}`, as in `{example}`."
        )
    };
    assert_eq!(error("0x_1"), (0, 4, no_digit('x', 16, "0x1F")));
    assert_eq!(error("0o_1"), (0, 4, no_digit('o', 8, "0o17")));
    // A leading `_` makes a name, not a number.
    assert_eq!(toks("_1"), [format!("{:?}", Tok::Name("_1".into()))]);
}

#[test]
fn a_base_mark_with_no_digit_of_its_base_is_named() {
    let no_digit = |p: char, base: u32, example: &str| {
        format!(
            "`0{p}` starts a number in base {base}, and no digit of base {base} follows it. Write \
             the digits after `0{p}`, as in `{example}`."
        )
    };
    assert_eq!(error("0o"), (0, 2, no_digit('o', 8, "0o17")));
    assert_eq!(error("0b"), (0, 2, no_digit('b', 2, "0b101")));
    assert_eq!(error("0o8"), (0, 3, no_digit('o', 8, "0o17")));
    assert_eq!(error("0b2"), (0, 3, no_digit('b', 2, "0b101")));
    assert_eq!(error("x = 0x;"), (4, 6, no_digit('x', 16, "0x1F")));
}

#[test]
fn every_capital_base_mark_is_named() {
    for (text, p) in [("0X1", 'X'), ("0O7", 'O'), ("0B1", 'B')] {
        let lower = p.to_ascii_lowercase();
        assert_eq!(
            error(text),
            (
                0,
                3,
                format!(
                    "`0{p}` is written with a capital `{p}`, and a number's base is marked with a \
                     small letter: `0x`, `0o` or `0b`. Write `0{lower}`."
                )
            ),
            "{text}"
        );
    }
}

#[test]
fn an_integer_takes_no_suffix_but_r() {
    // DESIGN.md sec:lexical: `1n` is a number running into a name, and `1f64` is rejected with
    // the format-suffix message.
    assert_eq!(
        error("1n"),
        (
            0,
            2,
            "the number `1` runs into the name `n` with nothing between them, and a number must \
             not run into a name. Put an operator or a space between them, as in `1 * n`."
                .into()
        )
    );
    assert_eq!(
        error("1f64"),
        (
            0,
            4,
            "A format suffix needs a decimal literal: `1f64`. Try `1.0f64` instead.".into()
        )
    );
    assert_eq!(
        error("x = 42f32;"),
        (
            4,
            9,
            "A format suffix needs a decimal literal: `42f32`. Try `42.0f32` instead.".into()
        )
    );
    // A digit of a larger base runs into a name in a smaller one.
    assert_eq!(error("0x1g").0..error("0x1g").1, 0..4);
    assert!(error("0x1g").2.contains("runs into the name `g`"));
    // An integer in a base other than ten takes no `r` either.
    assert!(
        error("0b1r")
            .2
            .contains("is a rational written in another base")
    );
    assert!(
        error("0o7r")
            .2
            .contains("is a rational written in another base")
    );
}

#[test]
fn what_may_stand_right_after_an_integer() {
    let name = |n: &str| format!("{:?}", Tok::Name(n.into()));
    let op = |o: &'static str| format!("{:?}", Tok::Op(o));
    let one = int(10, "1");
    // An operator, a bracket or a separator ends the number; there is no signed literal.
    for (text, want) in [
        ("-1", vec![op("-"), one.clone()]),
        ("1+2", vec![one.clone(), op("+"), int(10, "2")]),
        ("1;", vec![one.clone(), op(";")]),
        ("1)", vec![one.clone(), op(")")]),
        (
            "f(1,2)",
            vec![
                name("f"),
                op("("),
                one.clone(),
                op(","),
                int(10, "2"),
                op(")"),
            ],
        ),
        ("a[0x1F]", vec![name("a"), op("["), int(16, "1F"), op("]")]),
        ("1::x", vec![one.clone(), op("::"), name("x")]),
        ("1//c", vec![one.clone()]),
        ("1/*c*/2", vec![one.clone(), int(10, "2")]),
        ("0x1.f", vec![int(16, "1"), op("."), name("f")]),
        ("0b1.0", vec![int(2, "1"), op("."), int(10, "0")]),
    ] {
        assert_eq!(toks(text), want, "{text}");
    }
    // A string, an atom and an annotation are tokens of their own.
    assert_eq!(toks("1\"a\"").len(), 2);
    assert_eq!(toks("1#ok").len(), 2);
    // `'` marks a name, and a number is none.
    let e = lex("1'").unwrap_err();
    assert_eq!((e.kind, e.span.start), (ErrorKind::Unexpected('\''), 1));
}

#[test]
fn a_letter_beyond_ascii_right_after_a_number_is_an_error() {
    // It continues no name and starts no token: `1é` is not a number and a name.
    for text in ["1é", "0x1é", "2.5µ"] {
        assert!(lex(text).is_err(), "{text}");
    }
}

#[test]
fn an_integer_in_a_hole_is_lexed_as_in_code() {
    let toks = lex(r#""${0x1F}${1_0}""#).unwrap();
    assert_eq!(
        format!("{:?}", toks[0].tok),
        r#"Str([Hole { tokens: [Token { tok: Int { radix: 16, digits: "1F" }, span: Span { start: 3, end: 7 } }], span: Span { start: 1, end: 8 } }, Hole { tokens: [Token { tok: Int { radix: 10, digits: "10" }, span: Span { start: 10, end: 13 } }], span: Span { start: 8, end: 14 } }])"#
    );
    let e = lex(r#""${0x}""#).unwrap_err();
    assert_eq!((e.span.start, e.span.end), (3, 5));
}
