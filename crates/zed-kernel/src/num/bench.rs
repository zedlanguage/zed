//! The benchmark of `num`, run by `tools/run_tests.sh --bench` and left out of its default run
//! (TEST-bench-move-crates, author P178: a test that needs an unusual size is a benchmark).
//! The bounds it checks are checked on numbers of up to 30,103 digits by
//! `the_least_text_is_at_most_the_digits_written` in the tests of `num.rs`.

use super::tests::{power, text_bounds_hold};
use super::*;

/// CONST-too-large-kept-powers: `5^1300000` has 908,660 digits, and `text_size` put it above
/// 1 MiB; `text_least` must not pass the digits written nor `text_size` fall below them.
#[test]
fn five_to_the_1300000_has_text_bounds_around_its_digits() {
    let five = power(5, 1_300_000);
    assert!(five.text_least() > BigUint::from(908_600u32));
    assert!(five.text_size().1 > BigUint::from(1u32 << 20));
    text_bounds_hold(&five);
}
