//! Completeness of float and rational literals (TEST-complete-lex, author P189): each format
//! suffix, each form of a real before `r`, each place an exponent or `_` may and may not go,
//! and what may stand next to a float. The case list is `COMPLETENESS.md`.

use super::{float, rat, toks};
use zed_kernel::num::FloatFormat;
use zedc::lex::{ErrorKind, Tok, lex};

fn forced(s: &str, f: FloatFormat) -> Tok {
    Tok::Float {
        digits: s.to_string().into(),
        forced: Some(f),
    }
}

fn int(d: &str) -> Tok {
    Tok::Int {
        radix: 10,
        digits: d.to_string().into(),
    }
}

/// The span and message of the number error lexing `text`.
fn error(text: &str) -> (usize, usize, String) {
    let e = lex(text).expect_err(text);
    assert!(matches!(e.kind, ErrorKind::BadNumber(_)), "{text:?}: {e:?}");
    (e.span.start, e.span.end, e.to_string())
}

#[test]
fn the_suffixes_f32_and_f64_force_the_format_of_each_form_of_a_decimal() {
    // DESIGN.md sec:lexical, the float row: `0.1f64`, `0.5f32`.
    assert_eq!(toks("0.1f64"), [forced("0.1", FloatFormat::F64)]);
    assert_eq!(toks("0.5f32"), [forced("0.5", FloatFormat::F32)]);
    assert_eq!(toks("1e9f64"), [forced("1e9", FloatFormat::F64)]);
    assert_eq!(toks("1.5e-3f32"), [forced("1.5e-3", FloatFormat::F32)]);
    assert_eq!(toks("1_000.5f64"), [forced("1000.5", FloatFormat::F64)]);
    assert_eq!(toks("2E+10f64"), [forced("2E+10", FloatFormat::F64)]);
}

#[test]
fn a_suffix_is_written_in_small_letters_and_alone() {
    // `F64` is no suffix, so the number runs into a name.
    for text in [
        "1.5F64", "1.5f64r", "1.5f64x", "1.5f6", "1.5f128", "1.5f64_",
    ] {
        let (start, end, _) = error(text);
        assert_eq!((start, end), (0, text.len()), "{text}");
    }
}

#[test]
fn the_suffixes_f16_and_bf16_are_rejected_until_their_formats_come() {
    // DESIGN.md sec:lexical: until step L1.18a, `f16` and `bf16` are rejected with the same
    // literal at `f64` as the repair.
    for (text, d, name, decimal) in [
        ("1.5f16", "1.5", "f16", "1.5"),
        ("1.5bf16", "1.5", "bf16", "1.5"),
        ("1e9f16", "1e9", "f16", "1e9"),
        ("2f16", "2", "f16", "2.0"),
        ("2bf16", "2", "bf16", "2.0"),
    ] {
        assert_eq!(
            error(text),
            (
                0,
                text.len(),
                format!(
                    "The format suffix `{name}` is not available: `{d}{name}`. Try `{decimal}f64` \
                     instead."
                )
            ),
            "{text}"
        );
    }
}

#[test]
fn each_form_of_a_real_takes_r() {
    assert_eq!(toks("1e5r"), [rat("1e5")]);
    assert_eq!(toks("1E5r"), [rat("1E5")]);
    assert_eq!(toks("1e-5r"), [rat("1e-5")]);
    assert_eq!(toks("0r"), [rat("0")]);
    assert_eq!(toks("0.0r"), [rat("0.0")]);
    assert_eq!(toks("1_0.0_1e1_0r"), [rat("10.01e10")]);
}

#[test]
fn an_exponent_and_its_groups() {
    assert_eq!(toks("1e1_0"), [float("1e10")]);
    assert_eq!(toks("1e0"), [float("1e0")]);
    assert_eq!(toks("1e-0"), [float("1e-0")]);
    assert_eq!(toks("1E-5"), [float("1E-5")]);
    assert_eq!(toks("00.5"), [float("00.5")]);
    assert_eq!(toks("0.000"), [float("0.000")]);
    // A `_` after the exponent mark or its sign stands between no two digits.
    for text in ["1e_1", "1e+_1", "1_.5"] {
        assert!(lex(text).is_err(), "{text}");
    }
}

#[test]
fn a_second_dot_or_exponent_starts_a_new_token() {
    let dot = Tok::Op(".");
    assert_eq!(toks("1.5.5"), [float("1.5"), dot, int("5")]);
    assert_eq!(
        toks("1.5..2.5"),
        [float("1.5"), Tok::Op(".."), float("2.5")]
    );
    assert_eq!(toks("1e5.5"), [float("1e5"), Tok::Op("."), int("5")]);
    assert_eq!(
        toks("1.5.x"),
        [float("1.5"), Tok::Op("."), Tok::Name("x".into())]
    );
    // A float in base 16 is not written: `0x1.8` is the integer, a dot and an integer.
    assert_eq!(
        toks("0x1.8"),
        [
            Tok::Int {
                radix: 16,
                digits: "1".to_string().into()
            },
            Tok::Op("."),
            int("8")
        ]
    );
    // A second exponent mark runs into a name.
    assert!(lex("1e5e5").is_err());
}

#[test]
fn what_may_stand_next_to_a_float() {
    assert_eq!(toks("-1.5"), [Tok::Op("-"), float("1.5")]);
    assert_eq!(toks("2*.5"), [int("2"), Tok::Op("*."), int("5")]);
    assert_eq!(toks("1.5+2.5"), [float("1.5"), Tok::Op("+"), float("2.5")]);
    assert_eq!(toks("1e-3-1"), [float("1e-3"), Tok::Op("-"), int("1")]);
    assert_eq!(
        toks("(0.5f64)"),
        [Tok::Op("("), forced("0.5", FloatFormat::F64), Tok::Op(")")]
    );
    assert_eq!(toks("1.5r/3r"), [rat("1.5"), Tok::Op("/"), rat("3")]);
    let e = lex("1.5'").unwrap_err();
    assert_eq!((e.kind, e.span.start), (ErrorKind::Unexpected('\''), 3));
}

#[test]
fn a_float_in_a_hole_is_lexed_as_in_code() {
    let toks = lex(r#""${0.5f32}${1e5r}""#).unwrap();
    assert_eq!(
        format!("{:?}", toks[0].tok),
        r#"Str([Hole { tokens: [Token { tok: Float { digits: "0.5", forced: Some(F32) }, span: Span { start: 3, end: 9 } }], span: Span { start: 1, end: 10 } }, Hole { tokens: [Token { tok: Rat("1e5"), span: Span { start: 12, end: 16 } }], span: Span { start: 10, end: 17 } }])"#
    );
    let e = lex(r#""${1.5f16}""#).unwrap_err();
    assert_eq!((e.span.start, e.span.end), (3, 9));
}

#[test]
fn a_dot_with_no_digit_after_it_ends_the_integer_before_a_letter() {
    // DESIGN.md sec:lexical: `Real = Decimal '.' Decimal Exponent? | Decimal Exponent`, so `1.e`
    // is the integer `1`, the operator `.` and the name `e`: a member access, not a float.
    assert_eq!(
        toks("t() = 1.e;")[4..7],
        [int("1"), Tok::Op("."), Tok::Name("e".into())]
    );
    assert_eq!(toks("1.E"), [int("1"), Tok::Op("."), Tok::Name("E".into())]);
}

#[test]
fn a_decimal_beyond_the_range_of_every_float_format_is_one_float_token() {
    // The lexer keeps the digits; whether the value fits a format is the checker's question
    // (DESIGN.md L1.26b), and at `rat` every decimal is exact.
    for s in ["1e999999999999", "1e-999999999999", "1e400", "1.5e-400"] {
        assert_eq!(toks(s), [float(s)], "{s}");
    }
}
