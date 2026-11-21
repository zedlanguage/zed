use zed_tests::scaling;

use super::super::always_fails::{bare_moduli, cancelling, guarded_moduli, nested};
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
fn moduli_scale() {
    // MOD-positive-modulus (QUESTIONS A174): each modulus is judged from the interval its
    // operand already has, O(1) for each `mod`, and a refusal writes its modulus once into the
    // headline and the repair, so n remainders, guarded or not, are O(n) in all.
    let n = 1000;
    let guarded = resolved(n, guarded_moduli);
    scaling::check("n remainders each under a test of its modulus", n, |k| {
        let info = guarded[&k].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
    let bare = resolved(n, bare_moduli);
    scaling::check("n remainders each refused with its repair", n, |k| {
        let info = bare[&k].check();
        assert_eq!(info.errors.len(), k);
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
