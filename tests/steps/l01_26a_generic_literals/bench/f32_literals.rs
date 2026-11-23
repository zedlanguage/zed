//! Literals at an `f32` use (rows LIT-formats-decimal-past-f32-param and
//! LIT-formats-rat-suffix-beside-f32): the benchmark of the range message.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

use super::super::f32_literals::long_past_f32;

/// A decimal literal of `n` digits past the range of `f32` at an `f32` parameter is read once at
/// `f32` for its range (`check::past_f32`), and the message quotes it once. Besides its ratio:
/// one rejection, the range message. Small instance:
/// `f32_literals::a_long_decimal_past_the_range_of_f32_is_rejected_for_its_range`.
#[test]
fn a_long_decimal_past_the_range_of_f32_is_rejected_in_linear_time() {
    let n = 2_000_000;
    let srcs = [long_past_f32(n), long_past_f32(scaling::FACTOR * n)];
    let errors = type_errors(&srcs[0]);
    assert_eq!(errors.len(), 1);
    assert!(errors[0].contains("is larger than the largest f32"));
    scaling::check(
        "rejecting one decimal literal of n digits past the range of f32",
        n,
        |m| {
            type_errors(&srcs[usize::from(m != n)]);
        },
    );
}
