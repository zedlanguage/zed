//! The rounding words on wide rationals at the rule of low complexity. The rule at each
//! operand is checked in `rounding.rs` at small sizes.

use num_bigint::BigInt;
use zed_kernel::Rat;
use zed_kernel::num::Rounding;
use zed_tests::scaling::{check_order, inputs};

const RULES: [Rounding; 6] = [
    Rounding::TiesEven,
    Rounding::TiesAway,
    Rounding::Floor,
    Rounding::Ceil,
    Rounding::Trunc,
    Rounding::AwayFromZero,
];

/// `(3^m + 2) / 7` and its negative, with `3^m` written out as a plain integer of about
/// `1.58 m` bits; the denominator is one word, so the quotient and remainder are one pass.
fn operands(m: usize) -> [Rat; 2] {
    let n = BigInt::from(3).pow(m as u32) + BigInt::from(2);
    let r = Rat::new(n.clone(), BigInt::from(7)).expect("a nonzero denominator");
    let s = Rat::new(-n, BigInt::from(7)).expect("a nonzero denominator");
    [r, s]
}

#[test]
fn rounding_wide_rationals_scales() {
    // One Euclidean division by a one-word divisor, one remainder and one comparison: linear
    // in the numerator's width. About 40 µs a call at n (2026-11-17: 1.78M and 13.7M
    // instructions at n and 8n, 7.7 times; 8.0 times the bytes).
    let n = 1 << 17;
    let ops = inputs(n, operands);
    check_order(
        "the six rounding rules on a rational of about 1.58 n bits",
        n,
        1,
        |m| {
            for r in &ops[&m] {
                for rule in RULES {
                    r.round_whole(rule).unwrap();
                }
            }
        },
    );
}
