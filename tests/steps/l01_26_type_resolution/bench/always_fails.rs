use zed_tests::scaling;

use super::super::always_fails::{cancelling, nested};
use super::super::scaling::resolved;
use super::super::type_errors;

#[test]
fn a_long_divisor_that_cancels_scales() {
    // One pass over the divisor's sums, with a count for each name, and one balanced sum of
    // the constants.
    assert_eq!(type_errors(&cancelling(3)).len(), 1);
    let units = resolved(2000, cancelling);
    scaling::check("a divisor of n terms that cancel", 2000, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
    });
}

#[test]
fn nested_divisions_scale() {
    // The sums of each divisor end at the division inside it, so no divisor is read twice.
    assert!(type_errors(&nested(3)).is_empty());
    let units = resolved(2000, nested);
    scaling::check("n divisions nested in their divisors", 2000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
