//! The design's examples of step L1.25 written with a declared range (RANGE-L1): the range is
//! the parameter's cell, the forward transfer carries it into the result, and the preimage of
//! a test narrows it in the arm.

use zed_tests::step_helpers::l01_39_reduced_product::{arm, ranged_function};
use zedc::store::product::{arms, forward};

/// The ints of the body of `ok` in `src`, its parameters starting from their ranges.
fn result(src: &str) -> String {
    let (mut scope, body) = ranged_function(src);
    forward(&body, &mut scope).ints().to_string()
}

#[test]
fn a_range_carries_through_addition_and_a_square() {
    assert_eq!(result("ok(x: int[0..=9]) = x + 1;"), "[1..=10]");
    // `x * x` reads `x` twice: a square is never below 0, so `[-3..=4]` gives `[0..=16]`, not
    // the product of the intervals, `[-12..=16]`.
    assert_eq!(result("ok(x: int[-3..=4]) = x * x;"), "[0..=16]");
    // A range open above stays open, and one open below too.
    assert_eq!(result("ok(x: int[1..]) = x + 1;"), "[2..]");
    assert_eq!(result("ok(x: int[_..=10]) = x - 1;"), "[..=9]");
}

#[test]
fn a_test_narrows_a_range_open_above_in_its_arm() {
    let (scope, body) = ranged_function("ok(x: int[0..]) = if x + 1 <= 5 { x } else { 0 };");
    let a = arms(&body, &scope);
    let then = arm(&a, "<= 5", true).scope.get("x");
    assert_eq!(then.ints().to_string(), "[0..=4]");
    let other = arm(&a, "<= 5", false).scope.get("x");
    assert_eq!(other.ints().to_string(), "[5..]");
}
