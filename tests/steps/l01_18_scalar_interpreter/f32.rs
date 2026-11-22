//! `f32`, IEEE 754 binary32, beside `f64` (DESIGN.md L1.17, L1.18; row FLOAT-f32): its
//! literals and printing, arithmetic rounded once to `f32`, NaN, signed zero, subnormals,
//! overflow, the casts and their exact range of integers, order, and `f32 ^ int`. IEEE Std
//! 754-2019, doi:10.1109/IEEESTD.2019.8766229, is cited in zed-kernel: the format (section 3.6)
//! at `num/float_text.rs`, enum `FloatFormat`; rounding (section 4.3) at `num.rs`, enum
//! `Rounding`; arithmetic (section 5.4.1) at `eval.rs`, fn `prim_on`, `Prim::Sqrt`; `pow`
//! (section 9.2) there at `Prim::Pow`; comparisons (section 5.11) at `value.rs`,
//! `Value::surface_cmp`.

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
    // Text past the largest `f32` reads as the infinity, as at `f64` (step L1.18).
    assert_eq!(x("String(f32(text(\"1e39\")))"), "\"inf\"");
    assert_eq!(x("String(f32(text(\"-1e39\")))"), "\"-inf\"");
    assert_eq!(x("String(f64(text(\"1e400\")))"), "\"inf\"");
}

#[test]
fn casts_to_f32_round_to_nearest_ties_to_even() {
    // 2^24 is the last of the run of integers `f32` holds; 2^24 + 1 is not an `f32` and is a
    // tie, to the even 2^24; 2^24 + 3 is a tie to the even 2^24 + 4.
    assert_eq!(x("f32(16777216)"), "16777216.0f32");
    assert_eq!(x("f32(whole(16777217))"), "16777216.0f32");
    assert_eq!(x("f32(whole(16777219))"), "16777220.0f32");
    assert_eq!(x("f32(whole(-16777216))"), "-16777216.0f32");
    assert_eq!(x("f32(real(0.5f64))"), "0.5f32");
    assert_eq!(x("f32(real(0.1f64)) == 0.1f32"), "true");
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
    assert_eq!(x("round(f32(text(\"2.5\")))"), "2");
    assert_eq!(x("round(f32(text(\"inf\")))"), "#overflow");
}

#[test]
fn a_float_cast_of_literals_rounds_and_an_int_cast_not_whole_is_rejected() {
    // Since step L1.18 a cast to a float format never fails: of literals alone it rounds as
    // at run time. `int` of a value the checker does not prove whole is rejected.
    assert_eq!(x("f32(16777217)"), "16777216.0f32");
    assert_eq!(x("f32(0.1f64) == 0.1f32"), "true");
    assert!(!errors("x = int(2.5f32);\n").is_empty());
    assert_eq!(x("int(2.0f32)"), "2");
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
    // A decimal literal base does not take `f32` through `f32 ^ int`. DESIGN.md L1.17 makes
    // `0.5 ^ n` with `n : int` an `f64` alone; zedc has no arrow `f64 ^ int` yet and gives the
    // exact `rat` (row POW-domains, item 4).
    assert_eq!(x("0.5 ^ whole(-2)"), "4r");
}

/// An integer exponent of a generic power keeps its `int` where its base is an `f32`, so the
/// power is the arrow `f32 ^ int`, taken in `f64` and rounded once (DESIGN.md L1.18), not
/// `f32 ^ f32` (plan row DOC-lit-follows-exponent-f32). The two differ at `2.67 ^ 6`: `f32`'s
/// `powf` gives `362.2994`, the power in `f64` rounded gives `362.29944`.
#[test]
fn a_generic_exponent_keeps_its_int_at_an_f32_base() {
    let src = "f(positional x) = x * (2.67 ^ 6);\na = f(1.0f32);\nb = f(1.0f64);\n";
    assert_eq!(value(src, "a"), x("2.67f32 ^ whole(6)"));
    assert_eq!(value(src, "a"), "362.29944f32");
    assert_eq!(value(src, "b"), x("2.67f64 ^ 6.0f64"));
    // An exponent that is an operation on integer literals keeps its `int` in the same way.
    let src = "f(positional x) = x * (2.67 ^ (5 + 1));\na = f(1.0f32);\n";
    assert_eq!(value(src, "a"), "362.29944f32");
    // The base is the generic value itself: at `f32` the exponent `(1 + 1)` stays the `int` 2
    // (no `f32` arm in the follows, so the cast 7beecd868 dropped is never reached), at `f64` it
    // is cast once, at `int` it is the `int`.
    let src = "p(positional x) = x ^ (1 + 1);\na = p(3.0f32);\nb = p(3.0f64);\nc = p(3);\n";
    assert_eq!(value(src, "a"), "9.0f32");
    assert_eq!(value(src, "b"), "9.0");
    assert_eq!(value(src, "c"), "9");
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
    // At the top level, `y = 2^-1.0` takes `f64` too (POW-top-body-agree).
    assert_eq!(value("g() = 2^-1.0;\ny = g();\n", "y"), "0.5");
    assert_eq!(value("y = 2^-1.0;\n", "y"), "0.5");
    let src = "f(positional n) = 2^n;\ny = f(2.0);\nz = f(3);\n";
    assert_eq!(value(src, "y"), "4.0");
    assert_eq!(value(src, "z"), "8");
    // A decimal that nothing fixes takes `f64` though `rat` may take it too (DESIGN.md step
    // L1.26b, author decision 2026-11-12): `0.5 * 2` is `1.0` and `y = 0.5` is `0.5`.
    assert_eq!(value("y = 0.5 * 2;\n", "y"), "1.0");
    assert_eq!(value("y = 0.5;\n", "y"), "0.5");
    // Only a `/` of integer literals alone stays rejected.
    assert!(
        errors("y = 1 / 2;\n")
            .iter()
            .any(|e| e.starts_with("Nothing gives the integer literals a carrier")),
    );
}
