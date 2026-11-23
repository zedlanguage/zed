//! The benchmarks of DESIGN step L1.17b (sec:domains, "Kept powers"). The bodies timed are
//! checked at small sizes in `kept_powers.rs`, by `close_products_order_as_the_built_numbers`
//! and `a_wide_prime_times_a_power_prints_one_text_however_held`.

use num_bigint::{BigInt, BigUint};
use zed_kernel::Rat;
use zed_tests::scaling::{check_order, inputs};

use super::super::kept_powers::close_pair;

/// The order of `c * 3^(2^20)` and `(c + 1) * 3^(2^20)` against `2^f` ([`close_pair`]), which
/// agree in about `k` leading bits, at `k` and `8k` for `k` = 2^6, 2^15 and 2^17, so from 2^6 to
/// 2^20 bits of precision (DESIGN step L1.17b). Each round of bounds at precision `k` costs
/// about `2 log2 e` products of `k` bits, and the rounds double, so the order costs
/// O(M(k) log e) for the last precision `k`: below the limit of 10.5 from `k` to `8k`. The two
/// sides are never built (their bits, 1.66 million and more, stay above every precision tried).
///
/// The sizes, by the precedent of DECISION-roots-bench-regime: `k` and `8k` both on one
/// product method, long multiplication at 1 to 8 words, the kernel's transform (`MUL_LEAF`, 400
/// words, num/fast.rs) from 2^15 bits up. From 2^10 bits (16 words) to 2^13 (128 words) the
/// products leave long multiplication for num-bigint's Karatsuba, whose bytes allocated grow
/// about 27 times per factor of 8 (`(3/2)^3 8`, one scratch buffer per level of its recursion):
/// at `k` = 2^10 the first runs allocated 48,880 and 860,976 bytes, 17.6 times (2026-11-23,
/// Colab), work 4.6 times. No exact method with num-bigint's products meets 10.5 there
/// (ROOTS-cubic-bits-bytes, XR-ROOTS-REF META1).
#[test]
fn the_order_of_close_products_scales_with_its_precision() {
    let e = 1u64 << 20;
    let three = BigInt::from(zed_kernel::num::pow_uint(&BigUint::from(3u32), e));
    for n in [1usize << 6, 1 << 15, 1 << 17] {
        let pairs = inputs(n, |k| close_pair(&three, e, k as u64));
        let what = format!("the order of c * 3^(2^20) against 2^f at {n} and 8 times {n} bits");
        check_order(&what, n, 1, |k| {
            let (lo, hi, two) = &pairs[&k];
            assert!(lo < two && hi > two, "k {k}");
        });
    }
}

/// The text of `q * 3^e`, `q = 2^61 - 1`, held as digits, at `e = n` and `8n`: `Rat::integer_text`
/// takes the primes below 2^8 out of the value (one remainder by a word for each of 6 groups,
/// then the valuation of 3, O(n log^2 n) at most), finds the least root of what is left, `q`,
/// and prints `q*3^e`, as it does for the value held with `3^e` kept (plan row
/// KEPT-print-value-canonical). The work is O(n log^2 n) at most, held under the limit of 10.5.
#[test]
fn the_text_of_a_prime_word_times_a_power_held_as_digits_scales() {
    let n = 1usize << 15;
    let q = BigInt::from((1u64 << 61) - 1);
    let numbers = inputs(n, |m| {
        Rat::int(&q * BigInt::from(3).pow(u32::try_from(m).expect("a small exponent")))
    });
    check_order("the text of q * 3^n held as digits", n, 1, |m| {
        let text = numbers[&m].integer_text();
        assert_eq!(text, format!("2305843009213693951*3^{m}"));
    });
}
