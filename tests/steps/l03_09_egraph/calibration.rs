//! The limit against the time taken (QUESTIONS A99): the laws whose decision times
//! `bench/calibration.rs` holds within 2x of the work they are charged. The two laws of the
//! refusal sightings of 2026-11-12 (wt/refusal-sightings.md), the product law at exponent 1000
//! and the split law `(x + y) ^ 72 - x`, are proved, and so is the split law near the limit;
//! past the limit it is refused, charged no more than the limit.

use zed_kernel::poly::{Carrier, Decision, LIMIT, Verdict};

use super::{decide_sides, sides_of};

/// The decision on `lhs == rhs` over `params`.
fn decided(params: &str, lhs: &str, rhs: &str) -> Decision {
    let s = sides_of(&format!("sides({params}) = ({lhs}, {rhs});\n"), &["sides"]).remove(0);
    decide_sides(&s, Carrier::Int)
}

#[test]
fn the_calibrated_laws_are_proved_and_the_split_law_past_the_limit_refused() {
    for (params, lhs, rhs) in [
        (
            "x: int",
            "(1 + x) ^ 1000 * (1 - x) ^ 1000",
            "(1 - x ^ 2) ^ 1000",
        ),
        (
            "x: int, y: int",
            "(x + y) ^ 72 - x",
            "(x + y) ^ 36 * (y + x) ^ 36 - x",
        ),
        (
            "x: int, y: int",
            "(x + y) ^ 4096 - x",
            "(x + y) ^ 2048 * (y + x) ^ 2048 - x",
        ),
    ] {
        assert_eq!(decided(params, lhs, rhs).verdict, Verdict::Proved, "{lhs}");
    }
    // Exponent 8192, about four times the work of 4096, is refused.
    let d = decided(
        "x: int, y: int",
        "(x + y) ^ 8192 - x",
        "(x + y) ^ 4096 * (y + x) ^ 4096 - x",
    );
    assert!(matches!(d.verdict, Verdict::Refused(_)), "{:?}", d.verdict);
    assert!(d.work <= LIMIT);
}
