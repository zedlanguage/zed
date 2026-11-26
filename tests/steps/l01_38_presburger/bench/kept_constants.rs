//! The benchmarks of `kept_constants.rs` (row PRES-kept-constants), run by
//! `tools/run_tests.sh --bench`.

use crate::kept_constants::*;
use num_bigint::BigUint;
use zed_tests::scaling;
use zedc::store::presburger::decide_at;

/// `0 <= x <= 2^40 - 1 && 3 * x == #k0 + 1` ([`first`]) decided at `3^e`, and
/// `x == #k0 && x == 2 * t` ([`second`]) too, for exponents `e` of 1,048,576 and 8,388,608
/// (values of 1.7 and 13.3 million bits written out): of order 1 in `e` (power 0), since the
/// value is compared with the projection's finite ends by its sign, never by building it, and
/// in the second, whose projection repeats without end, its residue modulo the period of the
/// projection's tail, 2, is found by modular powering (row CLASSED-periodic-tail; refused for
/// `Refusal::Repeats` before it). Building `3^e` instead would be of order `e log e` at
/// least. Each call took under 1 ms at both sizes in the probe of job 34 (b22-kept5, hm5,
/// 2026-11-26), and `three_to` under 20 µs.
#[test]
fn a_kept_constant_is_decided_in_time_independent_of_its_digits() {
    scaling::check_order(
        "a question decided at a kept power of 3, by its exponent",
        1 << 20,
        0,
        |e| {
            let v = three_to(&BigUint::from(e));
            assert_eq!(
                decide_at(&first(), &k(), &v),
                Ok(false),
                "3 * x == 3^{e} + 1"
            );
            assert_eq!(
                decide_at(&second(), &k(), &v),
                Ok(false),
                "3^{e} is odd, so not even"
            );
        },
    );
}
