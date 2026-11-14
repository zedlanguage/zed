//! The L1 prelude words on scalars (`words::word`, plan row TEST-complete-kernel, author P189):
//! the casts `int`, `rat`, `f64` and `f32` from each source kind, `String`, `abs`, `len`,
//! `lower`, `upper`, `trim`, `codePoint`, `scalar`, `utf8` and `fromUtf8`, each at its edge
//! inputs and every atom it gives. Expected results from DESIGN.md L1.18 and L1.39c.

use std::mem::discriminant;

use num_bigint::BigInt;

use crate::num::Rat;
use crate::term::Prim;
use crate::value::{Family, Value};
use crate::words::word;

fn int(n: i64) -> Value {
    Value::Int(n)
}

fn rat(n: i64, d: i64) -> Value {
    Value::rat(Rat::new(BigInt::from(n), BigInt::from(d)).expect("a nonzero denominator"))
}

fn big(n: BigInt) -> Value {
    Value::int(n)
}

fn s(t: &str) -> Value {
    Value::str(t)
}

fn atom(name: &str) -> Value {
    Value::atom(name)
}

fn bytes(b: &[i64]) -> Value {
    Value::Family(Family::of(
        b.iter().enumerate().map(|(i, &b)| (i as i64, b)),
    ))
}

/// The same kind and the same text, so `-0.0` differs from `0.0`, a NaN equals a NaN, and `5`
/// differs from `5r`.
fn same(a: &Value, b: &Value) -> bool {
    discriminant(a) == discriminant(b) && a.to_string() == b.to_string()
}

/// Each `(word, argument, result)` gives the result; `None` is a type error.
fn check(cases: &[(Prim, Value, Option<Value>)]) {
    for (p, x, want) in cases {
        let got = word(*p, x);
        match (got, want) {
            (Ok(g), Some(w)) => assert!(same(&g, w), "{}({x}) = {g}, expected {w}", p.written()),
            (Err(_), None) => {}
            (g, w) => panic!("{}({x}) = {g:?}, expected {w:?}", p.written()),
        }
    }
}

/// `int(s)`: an optional `-` and ASCII decimal digits, leading zeros included; anything else,
/// digits of another script among it, is `#invalid` (DESIGN.md L1.18).
#[test]
fn int_of_a_string() {
    let wide = "123456789012345678901234567890";
    check(&[
        (Prim::CastInt, s("0"), Some(int(0))),
        (Prim::CastInt, s("007"), Some(int(7))),
        (Prim::CastInt, s("-0"), Some(int(0))),
        (Prim::CastInt, s("-12"), Some(int(-12))),
        (Prim::CastInt, s("9223372036854775807"), Some(int(i64::MAX))),
        (
            Prim::CastInt,
            s("-9223372036854775808"),
            Some(int(i64::MIN)),
        ),
        (
            Prim::CastInt,
            s("9223372036854775808"),
            Some(big(BigInt::from(1u64 << 63))),
        ),
        (
            Prim::CastInt,
            s(wide),
            Some(big(wide.parse().expect("digits"))),
        ),
        (Prim::CastInt, s(""), Some(atom("invalid"))),
        (Prim::CastInt, s("-"), Some(atom("invalid"))),
        (Prim::CastInt, s("+5"), Some(atom("invalid"))),
        (Prim::CastInt, s(" 5"), Some(atom("invalid"))),
        (Prim::CastInt, s("5 "), Some(atom("invalid"))),
        (Prim::CastInt, s("1.0"), Some(atom("invalid"))),
        (Prim::CastInt, s("1e3"), Some(atom("invalid"))),
        (Prim::CastInt, s("--1"), Some(atom("invalid"))),
        (Prim::CastInt, s("٤٢"), Some(atom("invalid"))),
        (Prim::CastInt, s("4٢"), Some(atom("invalid"))),
        (Prim::CastInt, s("４２"), Some(atom("invalid"))),
    ]);
}

/// `rat(s)`: what `String` writes for a `rat` (`3r`, `-1r/3r`), the same without the `r`s, or a
/// decimal with digits on both sides of the point; a zero denominator and any other text
/// `#invalid` (DESIGN.md L1.18).
#[test]
fn rat_of_a_string() {
    check(&[
        (Prim::CastRat, s("3r"), Some(rat(3, 1))),
        (Prim::CastRat, s("3"), Some(rat(3, 1))),
        (Prim::CastRat, s("0r"), Some(rat(0, 1))),
        (Prim::CastRat, s("-1r/3r"), Some(rat(-1, 3))),
        (Prim::CastRat, s("-1/3"), Some(rat(-1, 3))),
        (Prim::CastRat, s("0.25"), Some(rat(1, 4))),
        (Prim::CastRat, s("-0.5"), Some(rat(-1, 2))),
        (Prim::CastRat, s("00.50"), Some(rat(1, 2))),
        (Prim::CastRat, s("1r/0r"), Some(atom("invalid"))),
        (Prim::CastRat, s("1/0"), Some(atom("invalid"))),
        (Prim::CastRat, s("1r/3"), Some(atom("invalid"))),
        (Prim::CastRat, s("1/3r"), Some(atom("invalid"))),
        (Prim::CastRat, s("1r/-3r"), Some(atom("invalid"))),
        (Prim::CastRat, s(".5"), Some(atom("invalid"))),
        (Prim::CastRat, s("5."), Some(atom("invalid"))),
        (Prim::CastRat, s("+1r"), Some(atom("invalid"))),
        (Prim::CastRat, s("r"), Some(atom("invalid"))),
        (Prim::CastRat, s(""), Some(atom("invalid"))),
        (Prim::CastRat, s("1e3"), Some(atom("invalid"))),
        (Prim::CastRat, s("٣r"), Some(atom("invalid"))),
    ]);
}

/// `f64(s)` and `f32(s)`: an optional `-`, then `inf`, `nan`, or digits with an optional
/// fraction and exponent, correctly rounded; `#overflow` for a finite text past the largest
/// finite value, a value at most half the least subnormal is a signed zero with no atom, and
/// any other text `#invalid` (DESIGN.md L1.18). `f32(s)` rounds once from the digits.
#[test]
fn floats_of_a_string() {
    let f = |x: f64| Some(Value::float(x));
    let g = |x: f32| Some(Value::float32(x));
    // Just past the midpoint of 1 and the next `f32`: once from the digits it rounds up,
    // through the nearest `f64` (the midpoint itself) it would round to even, 1.
    let past_mid = "1.000000059604644775390625001";
    check(&[
        (Prim::CastF64, s("0"), f(0.0)),
        (Prim::CastF64, s("-0"), f(-0.0)),
        (Prim::CastF64, s("3"), f(3.0)),
        (Prim::CastF64, s("0.1"), f(0.1)),
        (Prim::CastF64, s("-2.5e-3"), f(-2.5e-3)),
        (Prim::CastF64, s("1.0e300"), f(1e300)),
        (Prim::CastF64, s("inf"), f(f64::INFINITY)),
        (Prim::CastF64, s("-inf"), f(f64::NEG_INFINITY)),
        (Prim::CastF64, s("nan"), f(f64::NAN)),
        (Prim::CastF64, s("1e-400"), f(0.0)),
        (Prim::CastF64, s("-1e-400"), f(-0.0)),
        (Prim::CastF64, s("5e-324"), f(f64::from_bits(1))),
        (Prim::CastF64, s("1e400"), Some(atom("overflow"))),
        (Prim::CastF64, s("-1e400"), Some(atom("overflow"))),
        (Prim::CastF64, s("+5"), Some(atom("invalid"))),
        (Prim::CastF64, s(".5"), Some(atom("invalid"))),
        (Prim::CastF64, s("5."), Some(atom("invalid"))),
        (Prim::CastF64, s("infinity"), Some(atom("invalid"))),
        (Prim::CastF64, s("Inf"), Some(atom("invalid"))),
        (Prim::CastF64, s("1e"), Some(atom("invalid"))),
        (Prim::CastF64, s(""), Some(atom("invalid"))),
        (Prim::CastF64, s("١.٥"), Some(atom("invalid"))),
        (Prim::CastF32, s("0.1"), g(0.1)),
        (Prim::CastF32, s("-0"), g(-0.0)),
        (Prim::CastF32, s(past_mid), g(1.0 + f32::EPSILON)),
        (Prim::CastF32, s("1e39"), Some(atom("overflow"))),
        (Prim::CastF32, s("1e-50"), g(0.0)),
        (Prim::CastF32, s("-inf"), g(f32::NEG_INFINITY)),
        (Prim::CastF32, s("nan"), g(f32::NAN)),
        (Prim::CastF32, s("x"), Some(atom("invalid"))),
    ]);
}

/// Casts between the number kinds: the value when it is the same number, `#inexact` when a
/// number in range has no equal one, `#overflow` past the largest finite float, `#invalid` for
/// an infinity or the NaN at an exact kind; `f64` of an `f32` always exact (DESIGN.md L1.18,
/// "Casts are domain proofs").
#[test]
fn casts_between_number_kinds() {
    let two53 = 1i64 << 53;
    let two_1024 = big(BigInt::from(1) << 1024u32);
    check(&[
        (Prim::CastInt, int(5), Some(int(5))),
        (Prim::CastInt, rat(4, 2), Some(int(2))),
        (
            Prim::CastInt,
            Value::rat(Rat::int(BigInt::from(1) << 70u32)),
            Some(big(BigInt::from(1) << 70u32)),
        ),
        (Prim::CastInt, rat(1, 3), Some(atom("inexact"))),
        (Prim::CastInt, Value::float(2.0), Some(int(2))),
        (Prim::CastInt, Value::float(-0.0), Some(int(0))),
        (Prim::CastInt, Value::float(2.5), Some(atom("inexact"))),
        (
            Prim::CastInt,
            Value::float(1e20),
            Some(big(BigInt::from(100_000_000_000_000_000_000u128))),
        ),
        (
            Prim::CastInt,
            Value::float(f64::INFINITY),
            Some(atom("invalid")),
        ),
        (Prim::CastInt, Value::float(f64::NAN), Some(atom("invalid"))),
        (Prim::CastInt, Value::float32(-3.0), Some(int(-3))),
        (
            Prim::CastInt,
            Value::float32(f32::NEG_INFINITY),
            Some(atom("invalid")),
        ),
        (Prim::CastRat, int(5), Some(rat(5, 1))),
        (
            Prim::CastRat,
            two_1024.clone(),
            Some(Value::rat(Rat::int(BigInt::from(1) << 1024u32))),
        ),
        (Prim::CastRat, Value::float(0.375), Some(rat(3, 8))),
        (
            Prim::CastRat,
            Value::float(0.1),
            Some(Value::rat(
                Rat::new(BigInt::from(3602879701896397u64), BigInt::from(1u64 << 55))
                    .expect("nonzero"),
            )),
        ),
        (Prim::CastRat, Value::float(f64::NAN), Some(atom("invalid"))),
        (Prim::CastRat, rat(-1, 3), Some(rat(-1, 3))),
        (Prim::CastF64, int(two53), Some(Value::float(two53 as f64))),
        (Prim::CastF64, int(two53 + 1), Some(atom("inexact"))),
        (
            Prim::CastF64,
            int(-two53 - 2),
            Some(Value::float(-(two53 as f64) - 2.0)),
        ),
        (Prim::CastF64, rat(1, 4), Some(Value::float(0.25))),
        (Prim::CastF64, rat(1, 3), Some(atom("inexact"))),
        (Prim::CastF64, two_1024.clone(), Some(atom("overflow"))),
        (Prim::CastF64, Value::float(-2.5), Some(Value::float(-2.5))),
        (
            Prim::CastF64,
            Value::float32(0.1),
            Some(Value::float(f64::from(0.1f32))),
        ),
        (
            Prim::CastF64,
            Value::float32(f32::NAN),
            Some(Value::float(f64::NAN)),
        ),
        (
            Prim::CastF32,
            int(1 << 24),
            Some(Value::float32(16_777_216.0)),
        ),
        (Prim::CastF32, int((1 << 24) + 1), Some(atom("inexact"))),
        (Prim::CastF32, Value::float(0.5), Some(Value::float32(0.5))),
        (Prim::CastF32, Value::float(0.1), Some(atom("inexact"))),
        (Prim::CastF32, Value::float(1e300), Some(atom("overflow"))),
        (
            Prim::CastF32,
            Value::float(f64::NEG_INFINITY),
            Some(Value::float32(f32::NEG_INFINITY)),
        ),
        (
            Prim::CastF32,
            Value::float(f64::NAN),
            Some(Value::float32(f32::NAN)),
        ),
        (
            Prim::CastF32,
            Value::float32(-0.0),
            Some(Value::float32(-0.0)),
        ),
        (Prim::CastF32, two_1024, Some(atom("overflow"))),
        // A float narrowed keeps the sign of a zero (FAIL-values-cast-negzero), as `f64` of an
        // `f64` keeps the value whole; a rational has no sign of zero to keep.
        (
            Prim::CastF32,
            Value::float(-0.0),
            Some(Value::float32(-0.0)),
        ),
        (Prim::CastF32, Value::float(0.0), Some(Value::float32(0.0))),
        (Prim::CastF64, Value::float(-0.0), Some(Value::float(-0.0))),
        (Prim::CastF64, Value::float(0.0), Some(Value::float(0.0))),
        // The least `f32` subnormal, `2^-149`, is exact; a float below half of it rounds to a
        // zero, which is not equal to it, at either sign.
        (
            Prim::CastF32,
            Value::float(f64::from(f32::from_bits(1))),
            Some(Value::float32(f32::from_bits(1))),
        ),
        (Prim::CastF32, Value::float(1e-46), Some(atom("inexact"))),
        (Prim::CastF32, Value::float(-1e-46), Some(atom("inexact"))),
        // The largest `f32` is exact; the next `f64` above it is past the format's range,
        // though it rounds to the largest `f32` (A36), at either sign.
        (
            Prim::CastF32,
            Value::float(f64::from(f32::MAX)),
            Some(Value::float32(f32::MAX)),
        ),
        (
            Prim::CastF32,
            Value::float(f64::from(f32::MAX).next_up()),
            Some(atom("overflow")),
        ),
        (
            Prim::CastF32,
            Value::float(-f64::from(f32::MAX).next_up()),
            Some(atom("overflow")),
        ),
    ]);
}

/// A cast of a value that is neither a number nor a string is a type error (DESIGN.md L1.18),
/// as is each other word at a kind it does not take.
#[test]
fn words_at_kinds_they_do_not_take() {
    let t = Value::tuple(vec![int(1)]);
    let mut cases = Vec::new();
    for p in [Prim::CastInt, Prim::CastRat, Prim::CastF64, Prim::CastF32] {
        for x in [Value::Bool(true), t.clone(), atom("a"), bytes(&[1])] {
            cases.push((p, x, None));
        }
    }
    for p in [
        Prim::Len,
        Prim::Lower,
        Prim::Upper,
        Prim::Trim,
        Prim::CodePoint,
        Prim::Utf8,
    ] {
        cases.push((p, int(1), None));
    }
    for p in [Prim::Abs, Prim::Scalar] {
        cases.push((p, s("1"), None));
    }
    cases.push((Prim::Scalar, Value::float(97.0), None));
    cases.push((Prim::FromUtf8, s("a"), None));
    cases.push((
        Prim::FromUtf8,
        Value::Family(Family::of([(0i64, "a")])),
        None,
    ));
    check(&cases);
}

/// `abs` at each kind and sign, `i64::MIN` widening past a word, `-0.0`, and the NaN.
#[test]
fn abs_at_each_kind() {
    check(&[
        (Prim::Abs, int(0), Some(int(0))),
        (Prim::Abs, int(-3), Some(int(3))),
        (Prim::Abs, int(3), Some(int(3))),
        (
            Prim::Abs,
            int(i64::MIN),
            Some(big(BigInt::from(1u64 << 63))),
        ),
        (
            Prim::Abs,
            big(-(BigInt::from(1) << 100u32)),
            Some(big(BigInt::from(1) << 100u32)),
        ),
        (
            Prim::Abs,
            big(BigInt::from(1) << 100u32),
            Some(big(BigInt::from(1) << 100u32)),
        ),
        (Prim::Abs, rat(-1, 3), Some(rat(1, 3))),
        (Prim::Abs, rat(1, 3), Some(rat(1, 3))),
        (Prim::Abs, Value::float(-0.0), Some(Value::float(0.0))),
        (
            Prim::Abs,
            Value::float(f64::NEG_INFINITY),
            Some(Value::float(f64::INFINITY)),
        ),
        (
            Prim::Abs,
            Value::float(-f64::NAN),
            Some(Value::float(f64::NAN)),
        ),
        (Prim::Abs, Value::float32(-1.5), Some(Value::float32(1.5))),
    ]);
}

/// `len` counts code points; `lower` and `upper` are Unicode's full case mappings, so
/// `upper("straße")` is `"STRASSE"` and a final `Σ` lowers to `ς`; `trim` removes Unicode white
/// space at both ends (DESIGN.md L1.18).
#[test]
fn string_words() {
    check(&[
        (Prim::Len, s(""), Some(int(0))),
        (Prim::Len, s("a"), Some(int(1))),
        (Prim::Len, s("aé😀"), Some(int(3))),
        (Prim::Upper, s(""), Some(s(""))),
        (Prim::Upper, s("straße"), Some(s("STRASSE"))),
        (Prim::Upper, s("abc é 1"), Some(s("ABC É 1"))),
        (Prim::Upper, s("ﬁ"), Some(s("FI"))),
        (Prim::Lower, s(""), Some(s(""))),
        (Prim::Lower, s("ABC É"), Some(s("abc é"))),
        (Prim::Lower, s("ΟΔΟΣ"), Some(s("οδος"))),
        (Prim::Lower, s("ΣΑΣ ΣΑΣ"), Some(s("σας σας"))),
        (Prim::Lower, s("İ"), Some(s("i\u{307}"))),
        (Prim::Trim, s(""), Some(s(""))),
        (Prim::Trim, s("   "), Some(s(""))),
        (Prim::Trim, s("ab"), Some(s("ab"))),
        (Prim::Trim, s("  a b \t\n"), Some(s("a b"))),
        (Prim::Trim, s("\u{3000}é\u{2003}"), Some(s("é"))),
        (Prim::Trim, s("\u{a0}x\u{85}"), Some(s("x"))),
        (Prim::Trim, s("\u{200b}x"), Some(s("\u{200b}x"))),
    ]);
}

/// `codePoint` of a string of one scalar, `#notScalar` otherwise; `scalar` of a code point,
/// `#notScalar` for a surrogate, a negative number or one past `0x10FFFF` (DESIGN.md L1.39c).
#[test]
fn code_points_and_scalars() {
    check(&[
        (Prim::CodePoint, s("a"), Some(int(97))),
        (Prim::CodePoint, s("é"), Some(int(233))),
        (Prim::CodePoint, s("😀"), Some(int(0x1F600))),
        (Prim::CodePoint, s("\u{0}"), Some(int(0))),
        (Prim::CodePoint, s(""), Some(atom("notScalar"))),
        (Prim::CodePoint, s("ab"), Some(atom("notScalar"))),
        (Prim::CodePoint, s("e\u{301}"), Some(atom("notScalar"))),
        (Prim::Scalar, int(97), Some(s("a"))),
        (Prim::Scalar, int(0), Some(s("\u{0}"))),
        (Prim::Scalar, int(0x10FFFF), Some(s("\u{10FFFF}"))),
        (Prim::Scalar, int(0xD7FF), Some(s("\u{D7FF}"))),
        (Prim::Scalar, int(0xD800), Some(atom("notScalar"))),
        (Prim::Scalar, int(0xDFFF), Some(atom("notScalar"))),
        (Prim::Scalar, int(0xE000), Some(s("\u{E000}"))),
        (Prim::Scalar, int(0x110000), Some(atom("notScalar"))),
        (Prim::Scalar, int(-1), Some(atom("notScalar"))),
        (Prim::Scalar, int(i64::MAX), Some(atom("notScalar"))),
        (
            Prim::Scalar,
            big(BigInt::from(1) << 100u32),
            Some(atom("notScalar")),
        ),
    ]);
}

/// `utf8(s)` is its bytes keyed from 0, `utf8("aé")` is `[97, 195, 169]` and `utf8("")` empty;
/// `fromUtf8(b)` reads the bytes back in key order, and is `#badUtf8` for an overlong form, a
/// surrogate, a scalar past `0x10FFFF`, a truncated or stray continuation byte, or a value that
/// is no byte (DESIGN.md L1.39c).
#[test]
fn utf8_both_ways() {
    let bad = || Some(atom("badUtf8"));
    check(&[
        (Prim::Utf8, s("aé"), Some(bytes(&[97, 195, 169]))),
        (Prim::Utf8, s(""), Some(Value::Family(Family::default()))),
        (Prim::Utf8, s("😀"), Some(bytes(&[0xF0, 0x9F, 0x98, 0x80]))),
        (Prim::FromUtf8, bytes(&[97, 195, 169]), Some(s("aé"))),
        (
            Prim::FromUtf8,
            Value::Family(Family::default()),
            Some(s("")),
        ),
        (
            Prim::FromUtf8,
            bytes(&[0xF0, 0x9F, 0x98, 0x80]),
            Some(s("😀")),
        ),
        (Prim::FromUtf8, bytes(&[0]), Some(s("\u{0}"))),
        (Prim::FromUtf8, bytes(&[192, 128]), bad()),
        (Prim::FromUtf8, bytes(&[0xE0, 0x80, 0x80]), bad()),
        (Prim::FromUtf8, bytes(&[0xED, 0xA0, 0x80]), bad()),
        (Prim::FromUtf8, bytes(&[0xF4, 0x90, 0x80, 0x80]), bad()),
        (Prim::FromUtf8, bytes(&[0xC3]), bad()),
        (Prim::FromUtf8, bytes(&[0x80]), bad()),
        (Prim::FromUtf8, bytes(&[97, 0xFF]), bad()),
        (Prim::FromUtf8, bytes(&[256]), bad()),
        (Prim::FromUtf8, bytes(&[-1]), bad()),
        (
            Prim::FromUtf8,
            Value::Family(Family::of([(0i64, big(BigInt::from(1) << 70u32))])),
            bad(),
        ),
    ]);
    // Read in key order, whatever order the family was built in.
    let shuffled = Value::Family(Family::of([(2i64, 169i64), (0, 97), (1, 195)]));
    check(&[(Prim::FromUtf8, shuffled, Some(s("aé")))]);
    // The round trip over each width of code point.
    let text = "a\u{7f}\u{80}é\u{7ff}\u{800}\u{ffff}\u{10000}\u{10ffff}";
    let b = word(Prim::Utf8, &s(text)).expect("bytes");
    check(&[(Prim::FromUtf8, b, Some(s(text)))]);
}

/// `String(x)`: a string is itself; a float the shortest text that reads back (`0.1`,
/// `1.0e300`, `inf`, `nan`, `-0.0`, an `f32` at its own width); an integer its digits; a `rat`
/// `-1r/3r`; an atom with a payload by name `#err(code: 3)`; a set by its members (DESIGN.md
/// L1.17, L1.18).
#[test]
fn string_of_each_kind() {
    let err = Value::atom_named("err", vec![("code".into(), int(3))]).expect("one field");
    let errs = Value::atom_with(
        "errs",
        vec![Value::Family(Family::set([atom("a"), atom("b")]))],
    );
    check(&[
        (Prim::Show, s("a\"b"), Some(s("a\"b"))),
        (Prim::Show, s(""), Some(s(""))),
        (Prim::Show, Value::float(0.1), Some(s("0.1"))),
        (Prim::Show, Value::float(1e300), Some(s("1.0e300"))),
        (Prim::Show, Value::float(f64::INFINITY), Some(s("inf"))),
        (Prim::Show, Value::float(f64::NEG_INFINITY), Some(s("-inf"))),
        (Prim::Show, Value::float(f64::NAN), Some(s("nan"))),
        (Prim::Show, Value::float(-0.0), Some(s("-0.0"))),
        (Prim::Show, Value::float32(0.1), Some(s("0.1"))),
        (
            Prim::Show,
            Value::float32(f32::from_bits(1)),
            Some(s("1.0e-45")),
        ),
        (
            Prim::Show,
            big(BigInt::from(1) << 70u32),
            Some(s("1180591620717411303424")),
        ),
        (Prim::Show, rat(-1, 3), Some(s("-1r/3r"))),
        (Prim::Show, rat(3, 1), Some(s("3r"))),
        (Prim::Show, err, Some(s("#err(code: 3)"))),
        (Prim::Show, errs, Some(s("#errs({#a, #b})"))),
        (Prim::Show, int(-7), Some(s("-7"))),
        (Prim::Show, Value::Bool(false), Some(s("false"))),
    ]);
    // A tuple prints as the printer writes it, an `f32` member with its suffix.
    let t = Value::tuple(vec![int(1), Value::float32(0.5), s("a")]);
    let text = t.to_string();
    assert!(text.contains("0.5f32"), "{text}");
    check(&[(Prim::Show, t, Some(s(&text)))]);
}
