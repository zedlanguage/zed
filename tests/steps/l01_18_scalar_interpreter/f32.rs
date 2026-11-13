//! `f32`, IEEE 754 binary32, beside `f64` (DESIGN.md L1.17, L1.18; row FLOAT-f32): its
//! literals and printing, arithmetic rounded once to `f32`, NaN, signed zero, subnormals,
//! overflow, the casts and their exact range of integers, order, and `f32 ^ int`.

use zed_tests::step_helpers::l01_16_elaboration::{errors, value};

use super::x;

#[test]
fn an_f32_prints_the_shortest_text_that_reads_back_in_f32() {
    assert_eq!(x("0.1f32"), "0.1f32");
    assert_eq!(x("String(0.1f32)"), "\"0.1\"");
    // The same value read in `f64` shows it is the `f32` nearest 0.1, not 0.1 itself.
    assert_eq!(x("String(f64(0.1f32))"), "\"0.10000000149011612\"");
    assert_eq!(x("String(2.0f32)"), "\"2.0\"");
    assert_eq!(x("String(16777216.0f32)"), "\"16777216.0\"");
}

#[test]
fn arithmetic_rounds_once_to_f32() {
    // At `f64` the sum is 0.30000000000000004; at `f32` it is the `f32` nearest 0.3.
    assert_eq!(x("String(0.1f32 + 0.2f32)"), "\"0.3\"");
    assert_eq!(x("String(0.1f64 + 0.2f64)"), "\"0.30000000000000004\"");
    assert_eq!(x("String(1.0f32 / 3.0f32)"), "\"0.33333334\"");
    assert_eq!(x("String(-(1.5f32) * 2.0f32 - 0.5f32)"), "\"-3.5\"");
}

#[test]
fn nan_in_gives_nan_out() {
    let nan = "f32(text(\"nan\"))";
    assert_eq!(x(&format!("String({nan} + 1.0f32)")), "\"nan\"");
    assert_eq!(x(&format!("String({nan} * 0.0f32)")), "\"nan\"");
    // Even `nan ^ 0`, which IEEE 754 makes 1, is the NaN, as at `f64`.
    assert_eq!(x(&format!("String({nan} ^ 0.0f32)")), "\"nan\"");
    assert_eq!(x("String(f64(text(\"nan\")) ^ 0.0f64)"), "\"nan\"");
    assert_eq!(x(&format!("String({nan} ^ whole(3))")), "\"nan\"");
    assert_eq!(x(&format!("{nan} == {nan}")), "false");
    assert_eq!(x(&format!("{nan} < 1.0f32")), "false");
}

#[test]
fn signed_zero_keeps_its_sign_and_equals_zero() {
    assert_eq!(x("String(-0.0f32)"), "\"-0.0\"");
    assert_eq!(x("-0.0f32 == 0.0f32"), "true");
    assert_eq!(x("String(0.0f32 * -1.0f32)"), "\"-0.0\"");
    assert_eq!(x("String(f64(-0.0f32))"), "\"-0.0\"");
}

#[test]
fn subnormals_are_held_and_halve_to_zero_by_ties_to_even() {
    assert_eq!(x("String(1.0e-45f32)"), "\"1.0e-45\"");
    assert_eq!(x("String(1.0e-45f32 * 3.0f32)"), "\"4.0e-45\"");
    // The least subnormal halved is a tie between 0 and itself; ties go to the even, 0.
    assert_eq!(x("String(1.0e-45f32 / 2.0f32)"), "\"0.0\"");
    assert_eq!(x("String(f64(1.0e-45f32))"), "\"1.401298464324817e-45\"");
}

#[test]
fn overflow_rounds_to_infinity() {
    assert_eq!(x("String(3.0e38f32 * 2.0f32)"), "\"inf\"");
    assert_eq!(x("String(-3.0e38f32 * 2.0f32)"), "\"-inf\"");
    // The same product at `f64` is finite.
    assert_eq!(x("String(3.0e38f64 * 2.0f64)"), "\"6.0e38\"");
    // Text past the largest `f32` is not read as infinity, as at `f64`.
    assert_eq!(x("f32(text(\"1e39\"))"), "#inexact");
    assert_eq!(x("f64(text(\"1e400\"))"), "#inexact");
}

#[test]
fn casts_to_f32_are_exact_or_fail() {
    // 2^24 is the last of the run of integers `f32` holds; 2^24 + 1 is not an `f32`.
    assert_eq!(x("f32(16777216)"), "16777216.0f32");
    assert_eq!(x("f32(whole(16777217))"), "#inexact");
    assert_eq!(x("f32(whole(-16777216))"), "-16777216.0f32");
    assert_eq!(x("f32(real(0.5f64))"), "0.5f32");
    assert_eq!(x("f32(real(0.1f64))"), "#inexact");
    assert_eq!(x("f32(1r / 4r)"), "0.25f32");
    // Read straight from the digits: `f32("0.1")` is the `f32` nearest 0.1.
    assert_eq!(x("f32(text(\"0.1\")) == 0.1f32"), "true");
    assert_eq!(x("f32(text(\"x\"))"), "#invalid");
}

#[test]
fn casts_from_f32() {
    assert_eq!(x("f64(0.1f32) == 0.10000000149011612f64"), "true");
    assert_eq!(x("int(4.0f32)"), "4");
    assert_eq!(x("rat(0.75f32)"), "3r/4r");
    assert_eq!(x("int(f32(text(\"2.5\")))"), "#inexact");
    assert_eq!(x("int(f32(text(\"inf\")))"), "#invalid");
}

#[test]
fn a_cast_that_always_fails_is_rejected() {
    for src in [
        "x = f32(16777217);\n",
        "x = f32(0.1f64);\n",
        "x = int(2.5f32);\n",
    ] {
        assert!(!errors(src).is_empty(), "{src}");
    }
}

#[test]
fn f32_values_are_ordered_as_ieee_754() {
    assert_eq!(x("0.1f32 < 0.2f32"), "true");
    assert_eq!(x("min(1.5f32, -2.0f32)"), "-2.0f32");
    assert_eq!(x("max(1.5f32, -2.0f32)"), "1.5f32");
    assert_eq!(x("abs(-2.5f32)"), "2.5f32");
}

#[test]
fn an_f32_to_an_int_power_is_an_f32() {
    assert_eq!(x("(-2.0f32) ^ whole(3)"), "-8.0f32");
    assert_eq!(x("2.0f32 ^ whole(-2)"), "0.25f32");
    assert_eq!(x("0.5f32 ^ 2.0f32"), "0.25f32");
    // An exponent past 2^53 keeps its parity, so the sign of a negative base's power is right.
    assert_eq!(x("(-1.0f32) ^ whole(9007199254740993)"), "-1.0f32");
    assert_eq!(x("(-1.0f32) ^ whole(9007199254740994)"), "1.0f32");
    assert_eq!(x("(-1.0f32) ^ whole(-9007199254740993)"), "-1.0f32");
    // A decimal literal base stays the exact `rat` (L1.17, `0.5 ^ n`).
    assert_eq!(x("0.5 ^ whole(-2)"), "4r");
}

#[test]
fn a_use_fixes_a_decimal_literal_at_f32() {
    let src = "h(positional v: f32) = v;\ny = h(0.1);\nz = y + 0.2;\n";
    assert_eq!(value(src, "y"), "0.1f32");
    assert_eq!(value(src, "z"), "0.3f32");
    let src = "g(x) = x * 2;\ny = g(x: 1.5f32);\n";
    assert_eq!(value(src, "y"), "3.0f32");
    // An exponent of `^` at `f32`: a decimal literal takes `f32`, there being no `f32 ^ f64`;
    // an integer literal keeps its `int` through `f32 ^ int`.
    let src = "h(positional v: f32) = v ^ 0.5;\ny = h(0.25f32);\n";
    assert_eq!(value(src, "y"), "0.5f32");
    let src = "h(positional v: f32) = v ^ 2;\ny = h(1.5f32);\n";
    assert_eq!(value(src, "y"), "2.25f32");
    let src = "g(x) = x ^ 0.5;\ny = g(x: 0.25f32);\n";
    assert_eq!(value(src, "y"), "0.5f32");
}

#[test]
fn a_literal_left_the_formats_f32_and_f64_takes_f64() {
    // `^` at an `int` base and a decimal exponent has no arrow at `rat`, so it leaves the
    // literal the float formats alone; it takes `f64`, as it did before `f32` was a carrier.
    // (At the top level, `y = 2^-1.0` is an operation on literals alone, rejected as before.)
    assert_eq!(value("g() = 2^-1.0;\ny = g();\n", "y"), "0.5");
    let src = "f(positional n) = 2^n;\ny = f(2.0);\nz = f(3);\n";
    assert_eq!(value(src, "y"), "4.0");
    assert_eq!(value(src, "z"), "8");
    // A literal `rat` may still take is not chosen: `0.5 * 2` and `y = 0.5` stay rejected.
    for src in ["y = 0.5 * 2;\n", "y = 0.5;\n"] {
        assert!(
            errors(src)
                .iter()
                .any(|e| e.starts_with("Nothing gives the literal `0.5` a carrier")),
            "{src}: {:?}",
            errors(src)
        );
    }
}
