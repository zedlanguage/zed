//! A float literal is correctly rounded to the nearest f64, ties to even (DESIGN.md
//! sec:numeric). It is an error when it rounds to infinity, or to zero while its digits are
//! not all zero; a literal of zero digits is zero whatever its exponent.

use std::collections::HashMap;

use zed_kernel::num::{LiteralRounding, literal_f32, literal_f64};

use super::x;
use crate::l01_16_elaboration::{elab, errors};

#[test]
fn a_price_reads_as_the_nearest_f64() {
    assert_eq!(x("0.1"), "0.1");
    assert_eq!(x("0.1 == 0.1000000000000000055511151231257827"), "true");
    assert_eq!(literal_f64("0.1"), Ok(0.1));
    assert_eq!(literal_f64("19.99"), Ok(19.99));
    // Halfway between 2^53 and 2^53 + 2: the tie goes to the even significand.
    assert_eq!(literal_f64("9007199254740993.0"), Ok(9007199254740992.0));
    assert_eq!(literal_f64("9007199254740995.0"), Ok(9007199254740996.0));
}

#[test]
fn a_literal_beyond_the_largest_f64_is_an_error() {
    assert_eq!(
        errors("distance = 1e400;\n"),
        ["`1e400` rounds to infinity as an f64; the largest f64 is 1.7976931348623157e308 [1e400]"]
    );
    // The sign is not part of the literal: `-1e400` fails on `1e400`.
    assert_eq!(
        errors("debt = -1e400;\n"),
        ["`1e400` rounds to infinity as an f64; the largest f64 is 1.7976931348623157e308 [1e400]"]
    );
    // Just above the largest f64, but nearer it than to the next power of two: it rounds down.
    assert_eq!(x("1.7976931348623158e308"), "1.7976931348623157e308");
    assert_eq!(
        literal_f64("1.7976931348623159e308"),
        Err(LiteralRounding::Infinite)
    );
}

#[test]
fn a_nonzero_literal_below_the_least_subnormal_is_an_error() {
    assert_eq!(
        errors("tolerance = 1e-400;\n"),
        [
            "`1e-400` is not zero but rounds to zero as an f64; the least positive f64 is 5.0e-324 [1e-400]"
        ]
    );
    // Below half the least subnormal it rounds to zero; above half, up to it.
    assert_eq!(literal_f64("2e-324"), Err(LiteralRounding::Zero));
    assert_eq!(x("3e-324"), "5.0e-324");
}

#[test]
fn a_subnormal_literal_is_accepted() {
    assert_eq!(x("5e-324"), "5.0e-324");
    assert_eq!(x("2.2250738585072009e-308"), "2.225073858507201e-308");
    assert_eq!(x("1e-310"), "1.0e-310");
}

#[test]
fn zero_digits_are_zero_at_any_exponent() {
    assert_eq!(x("0.0"), "0.0");
    assert_eq!(x("0e999"), "0.0");
    assert_eq!(x("0.000e-99999"), "0.0");
    assert_eq!(x("-0.0"), "-0.0");
    assert_eq!(x("String(-0e400)"), "\"-0.0\"");
}

#[test]
fn a_long_digit_string_with_a_huge_exponent_rounds_by_its_value() {
    let ones = "1".repeat(500);
    let zeros = "0".repeat(500);
    // 1.11…e-200 with 500 digits before the point is about 1.1e299: finite.
    assert_eq!(x(&format!("{ones}.0e-200")), "1.1111111111111112e299");
    // The same digits at e-100 are about 1.1e399: infinite.
    assert_eq!(
        literal_f64(&format!("{ones}.0e-100")),
        Err(LiteralRounding::Infinite)
    );
    // 500 zeros after the point put the 1 at 1e-501, then e200 brings it to 1e-301.
    assert_eq!(x(&format!("0.{zeros}1e200")), "1.0e-301");
    assert_eq!(
        literal_f64(&format!("0.{zeros}1e-10")),
        Err(LiteralRounding::Zero)
    );
    // An exponent past any machine integer still rounds by value.
    assert_eq!(
        literal_f64("1e99999999999999999999999"),
        Err(LiteralRounding::Infinite)
    );
    assert_eq!(
        literal_f64("1e-99999999999999999999999"),
        Err(LiteralRounding::Zero)
    );
    assert_eq!(literal_f64("0e99999999999999999999999"), Ok(0.0));
}

#[test]
fn an_f32_literal_rounds_by_the_same_rule() {
    assert_eq!(literal_f32("0.1"), Ok(0.1f32));
    assert_eq!(literal_f32("1e39"), Err(LiteralRounding::Infinite));
    assert_eq!(literal_f32("1e-46"), Err(LiteralRounding::Zero));
    assert_eq!(literal_f32("1e-45"), Ok(f32::from_bits(1)));
    assert_eq!(literal_f32("3.4028235e38"), Ok(f32::MAX));
    assert_eq!(literal_f32("0e99"), Ok(0.0));
}

#[test]
fn every_out_of_range_literal_of_a_unit_is_reported() {
    let e = elab("a = 1e400;\nb = 1e-400;\nc = 2.5;\n").unwrap_err();
    assert_eq!(e.len(), 2, "{e:?}");
}

#[test]
fn rounding_a_literal_of_n_digits_scales() {
    // A literal of n digits and an exponent that brings it near 1, so every digit counts.
    let text = |n: usize| format!("v = {}1.0e-{n};\n", "3".repeat(n));
    let inputs: HashMap<usize, String> = [2000, 16000].into_iter().map(|n| (n, text(n))).collect();
    zed_tests::scaling::check_order("a float literal of n digits", 2000, 1, |n| {
        elab(&inputs[&n]).unwrap();
    });
    // The rounding alone: the rest of the pipeline did about 2.6 times its work at 2000
    // digits, enough to hide a quadratic added to it (COMPLEXITY.md F85).
    let digits: HashMap<usize, String> = inputs
        .iter()
        .map(|(&n, t)| (n, t["v = ".len()..t.len() - ";\n".len()].to_string()))
        .collect();
    zed_tests::scaling::check_order("rounding a float literal of n digits", 2000, 1, |n| {
        assert!(literal_f64(&digits[&n]).is_ok());
    });
    assert_eq!(x(&format!("0.{}1e3", "3".repeat(3))), "333.1");
}
