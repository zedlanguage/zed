//! The casts (step L1.18): a cast to a float format is the nearest float, ties to even, the
//! infinity of its sign past the range; `int` of a number is accepted only where the checker
//! proves it whole, and is otherwise a compile error with the rounding functions as its menu;
//! `#invalid` when the source is not a `T` at all.

use super::x;
use num_bigint::BigUint;
use zed_kernel::{Prim, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::{elab, errors};

#[test]
fn reading_a_quantity_from_a_form_field() {
    assert_eq!(x("int(\"42\")"), "42");
    assert_eq!(x("int(\"-7\")"), "-7");
    assert_eq!(x("int(text(\"4 2\"))"), "#invalid");
    assert_eq!(x("int(text(\"\"))"), "#invalid");
    assert_eq!(
        x("int(text(\"+5\"))"),
        "#invalid",
        "a sign is only `-`, as `String` writes it"
    );
    assert_eq!(x("int(text(\"twelve\")) else #invalid -> 1"), "1");
    assert_eq!(
        x("int(\"123456789012345678901234567890\")"),
        "123456789012345678901234567890"
    );
}

#[test]
fn a_float_to_int_must_be_whole() {
    assert_eq!(x("int(3.0f64)"), "3");
    assert_eq!(x("int(1.0e20f64)"), "100000000000000000000");
    // An infinity or the NaN is not whole either.
    assert!(!errors("x = int(1.0f64 / 0.0);\n").is_empty());
    assert!(!errors("x = int(0.0f64 / 0.0);\n").is_empty());
    // A constant the checker lists: an operation on `rat` literals alone.
    assert_eq!(x("int(6r/2r)"), "3");
    // A number the checker does not prove whole is a compile error whose menu is the six
    // rounding functions (DESIGN.md sec:facets and step L1.18), whatever value it holds. A
    // constant's menu names the value each fix gives, `k is 4`; a call the checker does not list
    // yet (step L1.39) names the type, `k is int`.
    for (written, value) in [("7r/2r", "4"), ("rat(7) / rat(2)", "int"), ("2.5f64", "2")] {
        let got = errors(&format!("k = int({written});\n"));
        assert_eq!(got.len(), 1, "{got:?}");
        let msg = &got[0];
        assert_eq!(
            msg.lines().next(),
            Some(
                format!(
                    "No `int` equals the value: `int({written})`. Try `round({written})` instead."
                )
                .as_str()
            ),
            "{msg}"
        );
        assert!(msg.contains(&format!("k = round({written});")), "{msg}");
        assert!(msg.contains(&format!("k is {value}")), "{msg}");
        assert!(msg.ends_with(&format!(" [int({written})]")), "{msg}");
    }
    // A parameter's menu names each fix's type: a NaN or an infinity has no whole number.
    let got = errors("f(x: f64) = int(x);\n");
    assert_eq!(got.len(), 1, "{got:?}");
    let msg = &got[0];
    assert_eq!(
        msg.lines().next(),
        Some("No `int` equals the value: `int(x)`. Try `round(x)` instead."),
        "{msg}"
    );
    assert!(
        msg.contains("f(x: f64) = round(x);                 round(x) is int | #NaN | #overflow"),
        "{msg}"
    );
    assert!(msg.ends_with(" [int(x)]"), "{msg}");
}

/// `int(x)` of a parameter with no written type is judged over the parameter's domain, as
/// `int(x)` with `x: f64` is (DESIGN.md sec:corner_cases, "Casts are domain proofs"): the cast
/// takes no `rat`, `f64` or `f32` the checker does not prove whole, so a call with `0.5` is
/// rejected, and a call with an `int` or a text is not. Before the fix the checker accepted
/// each program below that passes `0.5`, typed `r` as `int` or `int | #invalid`, and the run
/// stopped at "`int` applied to `f64`, which is not whole" (seed 7289870353889267556 of
/// l01_26 `accepted_random_programs_raise_no_type_error`).
#[test]
fn an_int_cast_of_a_parameter_takes_no_float() {
    for p in [
        "f(positional x) = int(x);\nr = f(0.5);\n",
        "f(positional x) = int(if 0 == x { 2 } else { x });\nr = f(0.5);\n",
        "r = (v0 -> int(v0))(0.5);\n",
        "r = (v0 -> int(if 0 == v0 { 2 } else { v0 }))(0.5);\n",
        "r = (v0 -> int(if v0 > 1 { 2.0 } else { v0 }))(0.5);\n",
        "f(positional x) = int(x);\nr = f(2r);\n",
        "f(positional x) = int(x);\nr = f(2.0f32);\n",
    ] {
        assert!(elab(p).is_err(), "accepted: {p}");
    }
    for p in [
        "f(positional x) = int(x);\nr = f(3);\n",
        "f(positional x) = int(x);\nr = f(\"7\");\n",
        "r = (v0 -> int(if 0 == v0 { 2 } else { v0 }))(5);\n",
        "f(positional x) = int(round(x));\nr = f(0.5);\n",
    ] {
        assert_eq!(elab(p).err(), None, "{p}");
    }
}

#[test]
fn a_float_is_an_exact_rational() {
    assert_eq!(x("rat(0.5f64)"), "1r/2r");
    assert_eq!(x("rat(0.1f64)"), "3602879701896397r/36028797018963968r");
    assert_eq!(x("rat(-3)"), "-3r");
    assert_eq!(x("rat(1.0f64 / 0.0)"), "#overflow");
}

/// No `rat` stands for an infinity or the NaN, so `rat` gives them as a rounding word does:
/// `#overflow` and `#NaN` (DESIGN.md step L1.18's test, sec:corner_cases "Casts are domain
/// proofs"; author P361), at either sign and in either float format.
#[test]
fn rat_of_an_infinity_is_overflow_and_of_the_nan_is_nan() {
    assert_eq!(x("rat(f64(\"inf\"))"), "#overflow");
    assert_eq!(x("rat(f64(\"nan\"))"), "#NaN");
    assert_eq!(x("rat(f64(\"-inf\"))"), "#overflow");
    assert_eq!(x("rat(f32(\"inf\"))"), "#overflow");
    assert_eq!(x("rat(f32(\"-inf\"))"), "#overflow");
    assert_eq!(x("rat(f32(\"nan\"))"), "#NaN");
    // The largest finite floats are numbers, and `rat` of each is exact.
    assert_eq!(
        x("rat(f64(\"1.7976931348623157e308\")) == rat((2^53 - 1) * 2^971)"),
        "true"
    );
    assert_eq!(
        x("rat(f32(\"3.4028235e38\")) == rat((2^24 - 1) * 2^104)"),
        "true"
    );
}

#[test]
fn a_rational_reads_as_string_writes_it_or_as_a_decimal() {
    assert_eq!(x("rat(\"1r/3r\")"), "1r/3r");
    assert_eq!(x("rat(\"1/2\")"), "1r/2r");
    assert_eq!(x("rat(\"3r\")"), "3r");
    assert_eq!(x("rat(\"0.25\")"), "1r/4r");
    assert_eq!(x("rat(text(\"1/0\"))"), "#invalid");
    assert_eq!(x("rat(text(\".5\"))"), "#invalid");
    assert_eq!(x("rat(String(5r/7r)) == 5r/7r"), "true");
}

#[test]
fn a_number_to_f64_rounds_to_nearest_ties_to_even() {
    assert_eq!(x("f64(3)"), "3.0");
    assert_eq!(
        x("f64(2^60)"),
        "1152921504606847000.0",
        "the shortest digits that read back"
    );
    assert_eq!(
        x("f64(2^60 + 1)"),
        "1152921504606847000.0",
        "2^60 + 1 needs 61 bits and rounds to 2^60"
    );
    assert_eq!(x("f64(3r/8r)"), "0.375");
    assert_eq!(x("f64(rat(1) / rat(3))"), "0.3333333333333333");
    // The lines of DESIGN.md sec:facets: of literals alone the cast rounds as at run time.
    assert_eq!(x("f64(1r/3r)"), "0.3333333333333333");
    assert_eq!(x("f64(9007199254740993)"), "9007199254740992.0");
    assert_eq!(x("f64(9007199254740995)"), "9007199254740996.0");
    assert_eq!(x("f64(10^309)"), "inf");
    assert_eq!(x("f64(rat(1) / rat(2^1074))"), "5.0e-324");
    // Half the least subnormal is a tie between it and zero, which is even.
    assert_eq!(x("f64(rat(1) / rat(2^1075))"), "0.0");
    assert_eq!(x("f64(rat(3) / rat(2^1076))"), "5.0e-324");
}

#[test]
fn a_float_reads_correctly_rounded_and_past_the_range_is_infinite() {
    assert_eq!(x("f64(\"0.1\") == 0.1"), "true");
    assert_eq!(x("f64(\"2.5e-3\")"), "0.0025");
    assert_eq!(x("f64(\"7\")"), "7.0");
    assert_eq!(x("f64(text(\"1e400\"))"), "inf");
    assert_eq!(x("f64(text(\"-1e400\"))"), "-inf");
    assert_eq!(x("f64(text(\"1,5\"))"), "#invalid");
    assert_eq!(x("f64(text(\"infinity\"))"), "#invalid");
    assert_eq!(x("f64(text(\"1e\"))"), "#invalid");
}

/// Step L1.18: a cast to a float format rounds to nearest, ties to even, as IEEE 754 does (IEEE
/// Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 4.3; the full comment is in
/// zed-kernel `num.rs`, enum `Rounding`). The
/// largest `f64` is `(2^53 - 1) * 2^971`; a number below it plus half its last unit rounds to
/// it, and one at or past that midpoint (a tie, whose even side is the infinity) is the
/// infinity of its sign.
#[test]
fn a_number_beyond_the_largest_float_rounds_to_it_or_to_infinity() {
    let max = "(2^53 - 1) * 2^971";
    assert_eq!(x(&format!("f64({max})")), "1.7976931348623157e308");
    assert_eq!(x(&format!("f64(-({max}))")), "-1.7976931348623157e308");
    assert_eq!(x(&format!("f64({max} + 1)")), "1.7976931348623157e308");
    assert_eq!(x(&format!("f64(-({max}) - 1)")), "-1.7976931348623157e308");
    assert_eq!(x(&format!("f64({max} - 1)")), "1.7976931348623157e308");
    assert_eq!(x("f64(2^1024)"), "inf");
    assert_eq!(x("f64(-(2^1024))"), "-inf");
    // Rats beyond it, with and without a binary form, and just inside it.
    assert_eq!(
        x(&format!("f64(rat({max}) + 1r/2r)")),
        "1.7976931348623157e308"
    );
    assert_eq!(x("f64(rat(10^400) / 3r)"), "inf");
    assert_eq!(x("f64(rat(3)^700)"), "inf");
    assert_eq!(
        x(&format!("f64(rat({max}) - 1r/2r)")),
        "1.7976931348623157e308"
    );
    assert_eq!(x("f64(1r / rat(3)^700)"), "0.0");
    // `f32`: its largest is `(2^24 - 1) * 2^104`, from an int, a rat or an `f64`.
    let max32 = "(2^24 - 1) * 2^104";
    assert_eq!(x(&format!("f32({max32})")), "3.4028235e38f32");
    assert_eq!(x(&format!("f32({max32} + 1)")), "3.4028235e38f32");
    assert_eq!(x(&format!("f32({max32} - 1)")), "3.4028235e38f32");
    assert_eq!(x("f32(rat(2^128))"), "inff32");
    assert_eq!(
        x(&format!("f32({max32} + 2^103)")),
        "inff32",
        "the midpoint, a tie, to even"
    );
    assert_eq!(x(&format!("f32({max32} + 2^103 - 1)")), "3.4028235e38f32");
    assert_eq!(x("f32(real(1.0e39f64))"), "inff32");
    assert_eq!(x("f32(real(-1.0e39f64))"), "-inff32");
    assert_eq!(x(&format!("f32(f64({max32}))")), "3.4028235e38f32");
    // An infinity is not finite: `f32` keeps it, `rat` of it is `#overflow`, and `int` of a
    // float not proved whole is rejected.
    assert_eq!(x("String(f32(real(1.0e308f64 * 10.0f64)))"), "\"inf\"");
    assert_eq!(x("rat(real(1.0e308f64 * 10.0f64))"), "#overflow");
    // `int` and `rat` have no largest value.
    assert_eq!(x("round(rat(2^2000)) == 2^2000"), "true");
    assert_eq!(x("rat(2^2000) == rat(2^2000)"), "true");
}

#[test]
fn an_int_read_from_text_takes_leading_zeros_and_a_minus_zero() {
    // A meter reading padded to a fixed width: `int(s)` reads an optional `-` and decimal
    // digits, any number of them, so leading zeros are read (unlike `rat`, which reads only
    // what `String` writes; see rat_text.rs).
    assert_eq!(x("int(\"007\")"), "7");
    assert_eq!(x("int(\"-007\")"), "-7");
    assert_eq!(x("int(\"000\")"), "0");
    // The integers have one zero, so `-0` is that zero.
    assert_eq!(x("int(\"-0\")"), "0");
    assert_eq!(x("int(\"-0\") == int(\"0\")"), "true");
    assert_eq!(x("String(int(\"-00\"))"), "\"0\"");
}

#[test]
fn digits_of_other_scripts_are_not_read() {
    // Decimal digits are the ASCII `0` to `9` (DESIGN.md step L1.18), so 42 written in
    // Arabic-Indic digits (U+0664 U+0662) is no number, nor are Devanagari or fullwidth
    // digits, nor ASCII and Arabic-Indic digits mixed.
    assert_eq!(x("int(text(\"\u{664}\u{662}\"))"), "#invalid");
    assert_eq!(x("int(text(\"-\u{664}\u{662}\"))"), "#invalid");
    assert_eq!(x("int(text(\"4\u{662}\"))"), "#invalid");
    assert_eq!(x("int(text(\"\u{96a}\u{968}\"))"), "#invalid");
    assert_eq!(x("int(text(\"\u{ff14}\u{ff12}\"))"), "#invalid");
    assert_eq!(x("rat(text(\"\u{664}\u{662}\"))"), "#invalid");
    assert_eq!(x("f64(text(\"\u{664}\u{662}\"))"), "#invalid");
    assert_eq!(x("f64(text(\"1e\u{662}\"))"), "#invalid");
}

/// The sign bit of an `f64`.
const NEGATIVE: u64 = 1 << 63;

/// The bits of `f64(text)` as the kernel reads it, so that `0.0` and `-0.0`, which `==` takes
/// as equal, are told apart.
fn f64_bits(text: &str) -> u64 {
    match zed_kernel::eval(&Term::Prim(
        Prim::CastF64,
        vec![Term::Lit(Value::str(text))],
    ))
    .unwrap()
    {
        Value::Float(f) => f.get().to_bits(),
        other => panic!("f64({text:?}) gave {other}"),
    }
}

#[test]
fn a_float_read_from_text_keeps_the_sign_of_zero() {
    assert_eq!(f64_bits("-0"), NEGATIVE);
    assert_eq!(f64_bits("-0.0"), NEGATIVE);
    assert_eq!(f64_bits("-0e9"), NEGATIVE);
    assert_eq!(f64_bits("0"), 0);
    assert_eq!(f64_bits("0.0"), 0);
    // The same through a program: `String` writes the sign of a zero.
    assert_eq!(x("f64(\"-0\")"), "-0.0");
    assert_eq!(x("String(f64(text(\"-0\")))"), "\"-0.0\"");
    assert_eq!(x("f64(\"0\")"), "0.0");
}

#[test]
fn a_float_text_below_the_least_subnormal_reads_as_a_signed_zero() {
    // A sensor log that writes a reading of 1e-400 has written a number too small for an
    // f64: it is correctly rounded like any other, to zero with the text's sign, and no atom.
    assert_eq!(f64_bits("1e-400"), 0);
    assert_eq!(f64_bits("-1e-400"), NEGATIVE);
    assert_eq!(x("f64(\"1e-400\")"), "0.0");
    assert_eq!(x("f64(\"-1e-400\")"), "-0.0");
    assert_eq!(x("f64(text(\"-1e-400\"))"), "-0.0");
    // At most half the least subnormal is zero. 2^-1075 = 5^1075 * 10^-1075 exactly, half of
    // 2^-1074, a tie that rounds to the even neighbor, zero; one more digit past its last
    // makes it nearer to 2^-1074, the least subnormal, whose bits are 1.
    let half = format!("{}e-1075", BigUint::from(5u32).pow(1075));
    assert_eq!(f64_bits(&half), 0);
    assert_eq!(f64_bits(&format!("-{half}")), NEGATIVE);
    let above = format!("{}1e-1076", BigUint::from(5u32).pow(1075));
    assert_eq!(f64_bits(&above), 1);
    assert_eq!(f64_bits(&format!("-{above}")), NEGATIVE | 1);
}

#[test]
fn a_cast_of_a_kind_it_does_not_take_is_a_type_error() {
    assert_eq!(
        errors("x = int(true);\n"),
        ["`int` does not take (true): no arrow of `int` takes these types. [int(true)]"]
    );
    assert_eq!(
        errors("x = len(3);\n"),
        ["`len` does not take (3): no arrow of `len` takes these types. [len(3)]"]
    );
}

/// `"p0" ++ "p1" ++ …`: each piece is longer than a block of a string holds, so the string is
/// held as a join of the pieces and a cast writes it out to read it.
fn joined(pieces: &[String]) -> String {
    let quoted: Vec<String> = pieces.iter().map(|p| format!("\"{p}\"")).collect();
    quoted.join(" ++ ")
}

#[test]
fn a_number_received_in_pieces_reads_as_one() {
    // An account balance sent in three packets: a sign and digits, digits, digits.
    let pieces = [
        format!("-{}", "1234567890".repeat(13)),
        "9876543210".repeat(13),
        "5".repeat(130),
    ];
    assert_eq!(x(&format!("int({})", joined(&pieces))), pieces.concat());
    // A character that is not a digit in the middle piece makes the whole text no int.
    let bad = [
        "1".repeat(130),
        format!("x{}", "1".repeat(130)),
        "1".repeat(130),
    ];
    assert_eq!(x(&format!("int({})", joined(&bad))), "#invalid");
    // A fraction whose `/` falls in the last piece, (2·10^387 + 1) / 4, in lowest terms as
    // `String` writes it.
    let fraction = [
        format!("2{}", "0".repeat(129)),
        "0".repeat(130),
        format!("{}1r/4r", "0".repeat(127)),
    ];
    assert_eq!(x(&format!("rat({})", joined(&fraction))), fraction.concat());
    // A decimal whose point falls in the first piece reads as the same text unjoined.
    let decimal = [
        format!("0.{}", "3".repeat(130)),
        "7".repeat(130),
        "1".repeat(130),
    ];
    assert_eq!(
        x(&format!(
            "rat({}) == rat(\"{}\")",
            joined(&decimal),
            decimal.concat()
        )),
        "true"
    );
    // A float of 393 digits after the point rounds to the nearest f64, and one past the
    // largest f64 is the infinity, written in pieces as in one.
    let half = [
        format!("0.5{}", "0".repeat(130)),
        "0".repeat(130),
        format!("{}1", "0".repeat(130)),
    ];
    assert_eq!(x(&format!("f64({})", joined(&half))), "0.5");
    let huge = [
        format!("1{}", "0".repeat(130)),
        "0".repeat(130),
        "0".repeat(140),
    ];
    assert_eq!(x(&format!("f64({})", joined(&huge))), "inf");
}

#[test]
fn a_number_joined_from_a_thousand_pieces_reads_as_one() {
    // A `foldl` of `++` over a thousand pieces of 130 digits: the string is a tree whose middle
    // holds nodes of nodes, and each cast reads it in order. The chain is a kernel term, so
    // the text is joined by the evaluator as the program's `++` joins it.
    let pieces: Vec<String> = (0..1000)
        .map(|i| char::from(b'1' + (i % 9) as u8).to_string().repeat(130))
        .collect();
    let cast = |p: Prim, before: &str, after: &str| {
        let join = |a: Term, s: &str| Term::Prim(Prim::Concat, vec![a, Term::Lit(Value::str(s))]);
        let text = pieces
            .iter()
            .fold(Term::Lit(Value::str(before)), |t, s| join(t, s));
        let text = join(text, after);
        zed_kernel::eval(&Term::Prim(p, vec![text]))
            .unwrap()
            .to_string()
    };
    let digits = pieces.concat();
    assert_eq!(cast(Prim::CastInt, "-", ""), format!("-{digits}"));
    assert_eq!(cast(Prim::CastRat, "", "r"), format!("{digits}r"));
    let read = |s: &str| {
        zed_kernel::eval(&Term::Prim(Prim::CastF64, vec![Term::Lit(Value::str(s))]))
            .unwrap()
            .to_string()
    };
    assert_eq!(cast(Prim::CastF64, "0.", ""), read(&format!("0.{digits}")));
    // It differs from 1/9 in its 131st digit, far below half a unit in the last place of an
    // f64, so it rounds to the f64 nearest 1/9, as 21 ones do.
    assert_eq!(
        cast(Prim::CastF64, "0.", ""),
        read(&format!("0.{}", "1".repeat(21)))
    );
}
