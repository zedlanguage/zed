use zed_tests::scaling;

use super::super::exact_casts::{
    arms_of_casts, bounded_casts, bounded_comparisons, cast_of_a_power, casts_in_range,
    casts_of_literals,
};
use super::super::scaling::resolved;

#[test]
fn many_bounded_casts_scale() {
    // n functions, each casting its parameter under a test that bounds it.
    let units = resolved(800, bounded_casts);
    scaling::check("n functions, each a cast under a test", 800, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_chain_of_arms_each_a_bounded_cast_scales() {
    // One function of n arms, each arm a cast under the tests of the arms before it.
    let units = resolved(1000, arms_of_casts);
    scaling::check("a chain of n arms, each a cast", 1000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn many_bounded_comparisons_scale() {
    // n functions, each comparing an f64 with an int a test bounds: n rejections, each
    // offering `f64(n)`. The bound of each is proved from the tests above it alone.
    let units = resolved(200, bounded_comparisons);
    scaling::check("n rejected comparisons, each of a bounded int", 200, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), n);
    });
}

#[test]
fn many_casts_of_ints_in_range_scale() {
    // n functions, each casting its parameter under a test that bounds it beyond ±2^53 and
    // within the largest `f64`: the path that drops `#overflow` and keeps `#inexact`.
    let units = resolved(200, casts_in_range);
    scaling::check("n functions, each a cast of an int in range", 200, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn many_casts_of_literals_scale() {
    // n functions, each casting a `rat` literal that converts, so each result drops both atoms.
    let units = resolved(2000, casts_of_literals);
    scaling::check("n functions, each a cast of a rat literal", 2000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_cast_of_a_power_does_not_grow_with_its_exponent() {
    // `1e<k>r` holds 2^k * 5^k as two exponents, so its cast costs the same at k and 8k: a cast
    // that built the power would cost k^1.47 or more (COMPLEXITY.md K41).
    let units = resolved(1_000_000, cast_of_a_power);
    scaling::check_order("the cast of 1e<k>r", 1_000_000, 0, |k| {
        let info = units[&k].check();
        assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
    });
}
