//! Cases of DESIGN.md step L1.18 that the other files of this step leave out, one test per
//! construct. COMPLETENESS.md beside this file lists every case and the test that covers it.

use super::x;
use zed_tests::step_helpers::l01_16_elaboration::elab;

/// `int(s)` reads an optional `-` and ASCII digits and nothing else.
#[test]
fn an_int_text_is_a_minus_and_digits_alone() {
    let cases = [
        ("0", "0"),
        ("-007", "-7"),
        ("18446744073709551616", "18446744073709551616"),
        ("-18446744073709551617", "-18446744073709551617"),
        (" 7", "#invalid"),
        ("7 ", "#invalid"),
        ("-", "#invalid"),
        ("--1", "#invalid"),
        ("-+1", "#invalid"),
        ("1.0", "#invalid"),
        ("1e3", "#invalid"),
        ("0x10", "#invalid"),
        ("1_000", "#invalid"),
        ("nan", "#invalid"),
        ("inf", "#invalid"),
    ];
    for (s, want) in cases {
        assert_eq!(x(&format!("int(text(\"{s}\"))")), want, "int(\"{s}\")");
    }
}

/// `rat(s)` reads what `String` writes for a `rat`, the same without the `r`s, or a decimal with
/// digits on both sides of the point (rat_text.rs lists the texts `String` never writes).
#[test]
fn a_rat_text_takes_the_written_forms_and_no_others() {
    let cases = [
        ("-1r/3r", "-1r/3r"),
        ("-1/3", "-1r/3r"),
        ("0r", "0r"),
        ("-0.5", "-1r/2r"),
        ("10.00", "10r"),
        ("1 / 2", "#invalid"),
    ];
    for (s, want) in cases {
        assert_eq!(x(&format!("rat(text(\"{s}\"))")), want, "rat(\"{s}\")");
    }
}

/// `f64(s)` reads an optional `-` and then `inf`, `nan`, or digits with an optional fraction and
/// exponent; any other text is `#invalid`.
#[test]
fn an_f64_text_reads_inf_nan_and_signed_forms() {
    let cases = [
        ("inf", "inf"),
        ("-inf", "-inf"),
        ("nan", "nan"),
        ("-nan", "nan"),
        ("0", "0.0"),
        ("-0.0", "-0.0"),
        ("2.5e3", "2500.0"),
        ("25e-1", "2.5"),
        ("007.5", "7.5"),
        ("1e309", "#overflow"),
        ("-1e309", "#overflow"),
        ("", "#invalid"),
        ("-", "#invalid"),
        (" 1", "#invalid"),
        ("1 ", "#invalid"),
        ("Infinity", "#invalid"),
        ("NaN", "#invalid"),
        ("e5", "#invalid"),
        ("1e", "#invalid"),
        ("0x1p3", "#invalid"),
        // `String` writes the exponent with `e` and a sign only as `-`, as it writes an `int`.
        ("1e-5", "0.00001"),
        ("1E5", "#invalid"),
        ("1e+5", "#invalid"),
        ("5.", "#invalid"),
        ("-.5", "#invalid"),
        ("1e5.0", "#invalid"),
        // DESIGN.md L1.18 names these three.
        ("+5", "#invalid"),
        (".5", "#invalid"),
        ("infinity", "#invalid"),
    ];
    for (s, want) in cases {
        assert_eq!(x(&format!("f64(text(\"{s}\"))")), want, "f64(\"{s}\")");
    }
}

/// `f32(s)` reads what `f64(s)` reads, rounded once from the digits to `f32`.
#[test]
fn an_f32_text_reads_what_an_f64_text_reads() {
    let cases = [
        ("inf", "inff32"),
        ("-inf", "-inff32"),
        ("nan", "nanf32"),
        ("-0", "-0.0f32"),
        ("0.1", "0.1f32"),
        ("3.4028235e38", "3.4028235e38f32"),
        ("3.5e38", "#overflow"),
        ("1e-50", "0.0f32"),
        ("-1e-50", "-0.0f32"),
        ("1e-45", "1.0e-45f32"),
        ("+1", "#invalid"),
        (".5", "#invalid"),
        ("infinity", "#invalid"),
        ("٤٢", "#invalid"),
    ];
    for (s, want) in cases {
        assert_eq!(x(&format!("f32(text(\"{s}\"))")), want, "f32(\"{s}\")");
    }
}

/// `int` and `rat` of an infinity or the NaN are `#invalid`, at `f32` as at `f64`.
#[test]
fn int_and_rat_of_a_float_that_is_no_number_are_invalid() {
    for e in [
        "real(1.0f64 / 0.0)",
        "real(-1.0f64 / 0.0)",
        "real(0.0f64 / 0.0)",
    ] {
        assert_eq!(x(&format!("int({e})")), "#invalid", "int({e})");
        assert_eq!(x(&format!("rat({e})")), "#invalid", "rat({e})");
        assert_eq!(x(&format!("int(f32({e}))")), "#invalid", "int(f32({e}))");
        assert_eq!(x(&format!("rat(f32({e}))")), "#invalid", "rat(f32({e}))");
    }
    assert_eq!(x("rat(real(-0.0f64))"), "0r");
    assert_eq!(x("int(real(-0.0f64))"), "0");
}

/// `f64` of an `int` or a `rat` is the equal float, `#overflow` beyond the largest finite `f64`
/// and `#inexact` otherwise; the run of integers `f64` holds ends at 2^53.
#[test]
fn f64_of_an_int_or_rat_is_equal_or_fails_by_the_reason() {
    assert_eq!(x("f64(whole(2^53))"), "9007199254740992.0");
    assert_eq!(x("f64(whole(2^53 + 1))"), "#inexact");
    assert_eq!(x("f64(whole(2^53 + 2))"), "9007199254740994.0");
    assert_eq!(x("f64(whole(-(2^53) - 1))"), "#inexact");
    assert_eq!(x("f64(whole(2^1024))"), "#overflow");
    assert_eq!(x("f64(whole(-(2^1024)))"), "#overflow");
    assert_eq!(x("f64(rat(whole(3)) / 4r)"), "0.75");
    assert_eq!(x("f64(rat(whole(1)) / 3r)"), "#inexact");
    assert_eq!(x("f64(rat(whole(-1)) / 3r)"), "#inexact");
    assert_eq!(x("f64(rat(whole(2^1026)) / 3r)"), "#overflow");
    assert_eq!(x("f64(rat(whole(0)))"), "0.0");
}

/// `f32` of an `int`, a `rat` or an `f64` is the equal `f32`, `#overflow` for a finite value
/// beyond the largest finite `f32` and `#inexact` otherwise; the run of integers ends at 2^24.
#[test]
fn f32_of_an_int_rat_or_f64_is_equal_or_fails_by_the_reason() {
    assert_eq!(x("f32(whole(2^24))"), "16777216.0f32");
    assert_eq!(x("f32(whole(2^24 + 1))"), "#inexact");
    assert_eq!(x("f32(whole(-(2^24) - 1))"), "#inexact");
    assert_eq!(x("f32(whole(2^128))"), "#overflow");
    assert_eq!(x("f32(rat(whole(1)) / 4r)"), "0.25f32");
    assert_eq!(x("f32(rat(whole(1)) / 10r)"), "#inexact");
    assert_eq!(x("f32(real(0.5f64))"), "0.5f32");
    assert_eq!(x("f32(real(0.1f64))"), "#inexact");
    assert_eq!(x("f32(real(1.0e39f64))"), "#overflow");
    assert_eq!(x("f32(real(-1.0e39f64))"), "#overflow");
    assert_eq!(x("f32(real(1.0f64 / 0.0))"), "inff32");
    assert_eq!(x("f32(real(-1.0f64 / 0.0))"), "-inff32");
    assert_eq!(x("f32(real(0.0f64 / 0.0))"), "nanf32");
    assert_eq!(x("f32(real(1.0e-50f64))"), "#inexact");
    // An `f32` is its own `f32`.
    assert_eq!(x("f32(f32(text(\"1.5\")))"), "1.5f32");
    assert_eq!(x("f32(f32(text(\"nan\")))"), "nanf32");
}

/// `f64` of an `f32` is always exact.
#[test]
fn f64_of_an_f32_is_exact() {
    assert_eq!(x("f64(f32(text(\"0.1\")))"), "0.10000000149011612");
    assert_eq!(x("f64(f32(text(\"-inf\")))"), "-inf");
    assert_eq!(x("f64(f32(text(\"nan\")))"), "nan");
    assert_eq!(x("f64(f32(text(\"-0\")))"), "-0.0");
    assert_eq!(x("f64(f32(text(\"1e-45\")))"), "1.401298464324817e-45");
}

/// A cast of a value that is neither a number nor a string is a type error.
#[test]
fn a_cast_of_a_tuple_atom_or_bool_is_a_type_error() {
    for cast in ["int", "rat", "f64", "f32"] {
        for arg in ["(1, 2)", "true", "(1.0f64,)", "\"a\" < \"b\""] {
            let src = format!("x = {cast}({arg});\n");
            assert!(elab(&src).is_err(), "{src} is accepted");
        }
    }
}

/// The merge of several operands' failures is `#errs` of the set of distinct failures, in
/// arithmetic of every number kind, in a comparison and in `sum`.
#[test]
fn failures_merge_in_every_kind_and_in_sum() {
    assert_eq!(
        x("int(text(\"a\")) + int(real(0.5f64)) + 1 div whole(0)"),
        "#errs({#divByZero, #inexact, #invalid})"
    );
    assert_eq!(
        x("rat(text(\"a\")) * rat(real(0.0f64 / 0.0)) + 1r / rat(whole(0))"),
        "#errs({#divByZero, #invalid})"
    );
    assert_eq!(
        x("f64(text(\"a\")) - f64(whole(2^53 + 1))"),
        "#errs({#inexact, #invalid})"
    );
    assert_eq!(
        x("f32(text(\"1e39\")) / f32(text(\"x\"))"),
        "#errs({#invalid, #overflow})"
    );
    assert_eq!(
        x("int(text(\"a\")) < int(real(0.5f64))"),
        "#errs({#inexact, #invalid})"
    );
    assert_eq!(
        x("sum((int(text(\"a\")), 2, int(real(0.5f64))))"),
        "#errs({#inexact, #invalid})"
    );
    assert_eq!(x("sum((int(text(\"a\")), int(text(\"b\"))))"), "#invalid");
    assert_eq!(
        x("-int(text(\"a\"))"),
        "#invalid",
        "one operand passes its atom on"
    );
}

/// `sum` of one component is that component, of each number kind.
#[test]
fn sum_of_one_component_and_of_each_kind() {
    assert_eq!(x("sum((7,))"), "7");
    assert_eq!(x("sum((2r/3r,))"), "2r/3r");
    assert_eq!(x("sum((f32(text(\"0.1\")), f32(text(\"0.2\"))))"), "0.3f32");
    assert_eq!(x("sum((real(1.0f64 / 0.0), real(-1.0f64 / 0.0)))"), "nan");
    assert_eq!(x("sum((9223372036854775807, 1))"), "9223372036854775808");
}

/// `sum` on mixed number kinds, or on a value that is not a number, is a type error.
#[test]
fn sum_of_mixed_kinds_is_a_type_error() {
    for t in [
        "(whole(1), 2r)",
        "(1r, 2.0f64)",
        "(f32(1), 2.0f64)",
        "(1, \"2\")",
        "(1, true)",
    ] {
        let src = format!("{}x = sum({t});\n", super::PASS);
        assert!(elab(&src).is_err(), "{src} is accepted");
    }
}

/// `abs`, `-x`, `min` and `max` of `f32` are exact.
#[test]
fn f32_abs_negation_min_and_max_are_exact() {
    assert_eq!(x("abs(f32(text(\"-0.1\")))"), "0.1f32");
    assert_eq!(x("abs(f32(text(\"-0\")))"), "0.0f32");
    assert_eq!(x("-f32(text(\"0.1\"))"), "-0.1f32");
    assert_eq!(x("-f32(text(\"0\"))"), "-0.0f32");
    assert_eq!(x("abs(f32(text(\"-inf\")))"), "inff32");
    assert_eq!(x("abs(f32(text(\"nan\")))"), "nanf32");
    assert_eq!(x("min(f32(text(\"0.1\")), f32(text(\"0.2\")))"), "0.1f32");
    assert_eq!(x("max(f32(text(\"0.1\")), f32(text(\"0.2\")))"), "0.2f32");
    assert_eq!(x("abs(real(-0.0f64))"), "0.0");
    assert_eq!(x("abs(real(-1.0f64 / 0.0))"), "inf");
    assert_eq!(x("abs(-0r)"), "0r");
    assert_eq!(x("abs(0)"), "0");
}

/// Division by `0.0` or `-0.0`, and `0.0 ^ n` with `n < 0`, give the IEEE infinity at `f32` as
/// at `f64`.
#[test]
fn division_by_a_float_zero_and_zero_to_a_negative_power_are_infinite() {
    assert_eq!(x("real(1.0f64) / real(-0.0f64)"), "-inf");
    assert_eq!(x("real(-1.0f64) / real(-0.0f64)"), "inf");
    assert_eq!(x("real(0.0f64) / real(0.0f64)"), "nan");
    assert_eq!(x("f32(text(\"1\")) / f32(text(\"0\"))"), "inff32");
    assert_eq!(x("f32(text(\"1\")) / f32(text(\"-0\"))"), "-inff32");
    assert_eq!(x("f32(text(\"-1\")) / f32(text(\"0\"))"), "-inff32");
    assert_eq!(x("f32(text(\"0\")) / f32(text(\"0\"))"), "nanf32");
    assert_eq!(x("real(0.0f64) ^ real(-1.0f64)"), "inf");
    assert_eq!(x("f32(text(\"0\")) ^ whole(-1)"), "inff32");
    assert_eq!(x("f32(text(\"-0\")) ^ whole(-1)"), "-inff32");
    assert_eq!(x("f32(text(\"-0\")) ^ whole(-2)"), "inff32");
}

/// `x ^ y` of two `f32` values is the IEEE power rounded to `f32`.
#[test]
fn an_f32_to_an_f32_power_is_the_ieee_power() {
    assert_eq!(x("f32(text(\"2\")) ^ f32(text(\"0.5\"))"), "1.4142135f32");
    assert_eq!(x("f32(text(\"-1\")) ^ f32(text(\"0.5\"))"), "nanf32");
    assert_eq!(x("f32(text(\"nan\")) ^ f32(text(\"0\"))"), "nanf32");
    assert_eq!(x("f32(text(\"2\")) ^ f32(text(\"128\"))"), "inff32");
    assert_eq!(x("f32(text(\"2\")) ^ f32(text(\"-150\"))"), "0.0f32");
}

/// `x ^ n` with `x : f32` and `n : int`: an exponent beyond ±2^53 is read as the `f64` nearest
/// it of the same parity, so a negative base keeps the sign of the exact power.
#[test]
fn an_f32_to_a_huge_int_power_keeps_the_sign_of_the_exact_power() {
    assert_eq!(x("f32(text(\"-1\")) ^ whole(2^60 + 1)"), "-1.0f32");
    assert_eq!(x("f32(text(\"-1\")) ^ whole(2^60)"), "1.0f32");
    assert_eq!(x("f32(text(\"-1\")) ^ whole(-(2^60) - 1)"), "-1.0f32");
    assert_eq!(x("f32(text(\"-2\")) ^ whole(2^60 + 1)"), "-inff32");
    assert_eq!(x("f32(text(\"-0.5\")) ^ whole(2^60 + 1)"), "-0.0f32");
    assert_eq!(x("f32(text(\"1\")) ^ whole(2^100)"), "1.0f32");
}

/// `String` writes every kind of data; floats in their shortest form, a signed zero with its
/// sign, a payload atom as written with its fields in code-point order.
#[test]
fn string_writes_each_kind_of_data() {
    assert_eq!(x("String(real(-0.0f64))"), "\"-0.0\"");
    assert_eq!(x("String(real(1.0f64 / 0.0))"), "\"inf\"");
    assert_eq!(x("String(real(0.0f64 / 0.0))"), "\"nan\"");
    assert_eq!(x("String(f32(text(\"0.1\")))"), "\"0.1\"");
    assert_eq!(x("String(f32(text(\"-inf\")))"), "\"-inf\"");
    assert_eq!(x("String(-2r/4r)"), "\"-1r/2r\"");
    assert_eq!(x("String((#none, 1))"), "\"(#none, 1)\"");
    assert_eq!(
        x("String((#err(b: 1, a: \"x\"),))"),
        "\"(#err(a: \\\"x\\\", b: 1),)\""
    );
    assert_eq!(x("String(((1, 2), \"\"))"), "\"((1, 2), \\\"\\\")\"");
    assert_eq!(x("String(2^64)"), "\"18446744073709551616\"");
    assert_eq!(x("\"${(1, #a)}\""), "\"(1, #a)\"");
    assert_eq!(x("\"${\"q\"}\""), "\"q\"");
}

/// `String(x)` and interpolation show data, so a value that holds a function is a type error.
#[test]
fn showing_a_function_is_a_type_error() {
    let f = "f(positional v: int) = v;\n";
    for e in [
        "String(f)",
        "String((f, 1))",
        "String(#box(f))",
        "\"${f}\"",
        "\"${(1, (f,))}\"",
    ] {
        let src = format!("{f}x = {e};\n");
        assert!(elab(&src).is_err(), "{src} is accepted");
    }
}

/// `len` counts code points; `lower` and `upper` are Unicode's full case mappings; `trim`
/// removes Unicode white space at both ends and nothing inside.
#[test]
fn string_words_on_empty_and_unicode_text() {
    assert_eq!(x("len(\"\")"), "0");
    assert_eq!(x("len(\"😀\")"), "1");
    assert_eq!(
        x("len(\"e\\u{301}\")"),
        "2",
        "a combining mark is a code point"
    );
    assert_eq!(x("upper(\"\")"), "\"\"");
    assert_eq!(x("upper(\"ŉ\")"), "\"ʼN\"", "a full mapping that lengthens");
    assert_eq!(x("lower(\"ΑΣ\")"), "\"ας\"", "a final sigma");
    assert_eq!(x("lower(\"İ\") == \"i\\u{307}\""), "true");
    assert_eq!(x("upper(\"ﬁ\")"), "\"FI\"");
    assert_eq!(x("trim(\"\")"), "\"\"");
    assert_eq!(x("trim(\" \\t\\n \")"), "\"\"");
    assert_eq!(x("trim(\"\\u{a0}a b\\u{2028}\")"), "\"a b\"");
    assert_eq!(
        x("trim(\"\\u{200b}a\")"),
        "\"\\u{200B}a\"",
        "a zero-width space is no white space"
    );
    assert_eq!(x("len(trim(\"\\u{85}x\\u{85}\"))"), "1");
}

/// Euclidean `div` and `mod` at zero, at one, and past a machine word; `mod` by zero is
/// `#divByZero` as `div` is.
#[test]
fn euclidean_div_and_mod_at_the_edges() {
    let cases = [
        ("0 div whole(5)", "0"),
        ("0 mod whole(-5)", "0"),
        ("7 mod whole(0)", "#divByZero"),
        ("-7 div whole(1)", "-7"),
        ("-7 mod whole(1)", "0"),
        ("-7 div whole(-1)", "7"),
        ("-(2^70) div whole(-(2^35))", "34359738368"),
        ("(-(2^70) - 1) mod whole(2^35)", "34359738367"),
        ("(-(2^70) - 1) div whole(2^35)", "-34359738369"),
        ("5 mod whole(-(2^70))", "5"),
        ("-5 mod whole(-(2^70))", "1180591620717411303419"),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}

/// A loose atom an operand carries in passes through every cast, `String`, interpolation, `sum`
/// and the number and string words, as a failure does (DESIGN.md sec:failure, "An operation
/// that always fails is rejected", limit (2), and "A cast of an atom gives the atom"); the
/// type error of a cast is for data that is neither a number nor a string.
#[test]
fn a_loose_atom_passes_through_casts_and_words() {
    for e in [
        "int(#none)",
        "rat(#none)",
        "f64(#none)",
        "f32(#none)",
        "String(#none)",
        "\"${#none}\"",
        "abs(#none)",
        "len(#none)",
        "-#none",
        "sum((#none, 1))",
        "#none + 1",
    ] {
        assert_eq!(x(e), "#none", "{e}");
    }
    assert_eq!(x("int(#e(code: 2))"), "#e(code: 2)");
}

/// A one-component tuple is written with its comma, alone and inside `String`.
#[test]
fn a_one_component_tuple_keeps_its_comma() {
    assert_eq!(x("(1,)"), "(1,)");
    assert_eq!(x("String((1,))"), "\"(1,)\"");
}

/// The evaluator's own check (DESIGN.md L1.17: it catches a bug in the checker): a cast or a
/// string word applied to a kind it does not take, reaching the evaluator, is a type error and
/// not a value.
#[test]
fn the_evaluator_refuses_a_word_on_a_kind_it_does_not_take() {
    use zed_kernel::term::build::{lit, prim};
    use zed_kernel::{KernelError, Prim, Value, eval};
    let pair = Value::tuple(vec![Value::Int(1), Value::Int(2)]);
    for (p, v) in [
        (Prim::CastInt, pair.clone()),
        (Prim::CastRat, pair.clone()),
        (Prim::CastF64, Value::Bool(true)),
        (Prim::CastF32, pair),
        (Prim::Len, Value::Int(3)),
        (Prim::Lower, Value::Bool(false)),
    ] {
        let err = eval(&prim(p, vec![lit(v)])).unwrap_err();
        assert!(matches!(err, KernelError::Type(_)), "{p:?}: {err:?}");
    }
}

/// `f32(n)` of an `int` the checker shows within ±2^24, the run of integers `f32` holds, is
/// exact, with no `#inexact`; one past either bound keeps it, as `f64(n)` within ±2^53 does
/// (l01_26 `exact_casts.rs`).
#[test]
fn f32_of_an_int_shown_within_two_to_the_24_is_exact() {
    use zed_tests::step_helpers::l01_26_type_resolution::sig;
    let under = |test: &str| {
        let src = format!("f(positional n: int) = if {test} {{ f32(n) }} else {{ 0.0f32 }};\n");
        sig(&src, "f")
    };
    assert_eq!(under("n >= 0 && n <= 100"), "(int) -> f32");
    assert_eq!(under("n >= -16777216 && n <= 16777216"), "(int) -> f32");
    assert_eq!(
        under("n >= -16777217 && n <= 16777216"),
        "(int) -> f32 | #inexact"
    );
    assert_eq!(
        under("n >= -16777216 && n <= 16777217"),
        "(int) -> f32 | #inexact"
    );
}

/// A string is printed as a Zed string literal that reads back as the same text (DESIGN.md
/// sec:diagnostics, "Characters a terminal does not show are printed escaped"): `\\`, `\"`,
/// `\n`, `\r`, `\t`, `\0`, `\$` before `{` alone, and `\u{X}` for a character with no visible
/// form of its own; a `'` and every visible character are written as themselves. Inside a tuple
/// the same, and `String` of that tuple is a text that holds the escapes, printed escaped again.
#[test]
fn a_printed_string_escapes_what_a_terminal_does_not_show() {
    let cases = [
        (r#""a\\b""#, r#""a\\b""#),
        (r#""say \"hi\"""#, r#""say \"hi\"""#),
        (r#""1\n2\r3\t4\05""#, r#""1\n2\r3\t4\05""#),
        (r#""\${h} $5 $""#, r#""\${h} $5 $""#),
        (r#""it's""#, r#""it's""#),
        (r#""\u{7}e\u{301}\u{200B}""#, r#""\u{7}e\u{301}\u{200B}""#),
        (r#""é 面 😀""#, r#""é 面 😀""#),
        (r#"("a\n", 1)"#, r#"("a\n", 1)"#),
        (r#"String(("a\n", 1))"#, r#""(\"a\\n\", 1)""#),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}
