//! The benchmarks of zed-bignum whose sizes are set for the unit build's small leaves
//! (`fast::MUL_LEAF` 48 and the others under `fast::SMALL_LEAVES`), moved from zed-kernel's
//! `num/bench.rs` with the module (DRY-bignum-crate-2026-11-26). With the measured leaves
//! `square_roots_scale` took 10.92 times the instructions from 8192 to 65536 words (hm1,
//! 2026-11-26), past the limit of 10.5, where it passed with the small leaves; plan row
//! PERF-sqrt-production-leaves-ratio. zed-kernel's unit tests take the small leaves again
//! (zed-bignum-small, TEST-kernel-small-leaves-after-bignum-move), but the benchmark stays
//! here, by the function it measures.

use num_bigint::BigUint;
use num_traits::Zero;

use crate::least_root::sqrt_rem_uint;

/// A number of `words` words from a fixed linear congruential sequence (Knuth's MMIX
/// constants), its top word not zero: the benches need the same inputs on every run. The same
/// as zed-kernel `num/bench.rs` `bench_number`, which feeds 11 other benches there.
fn bench_number(words: usize, seed: u64) -> BigUint {
    let mut x = seed;
    let mut ds: Vec<u32> = Vec::with_capacity(2 * words);
    for _ in 0..words {
        x = (x.wrapping_mul(6364136223846793005)).wrapping_add(1442695040888963407);
        ds.extend([x as u32, (x >> 32) as u32]);
    }
    if let Some(top) = ds.last_mut() {
        *top |= 1 << 31;
    }
    BigUint::from_slice(&ds)
}

/// Item PERF-wide-odd-base-ratio-9: [`sqrt_rem_uint`] of a number of n words, O(M(n)) (proof
/// at the function), against num-bigint's `sqrt`, 34.5 times from 1.66M to 13.3M bits.
/// 8192 words puts every level from the top down to about 512 words on the transforms.
#[test]
fn square_roots_scale() {
    let n = 1 << 13;
    let numbers = crate::scaling::inputs(n, |m| bench_number(m, 11));
    crate::scaling::check_order("the square root of a number of n words", n, 1, |m| {
        let (s, r) = sqrt_rem_uint(&numbers[&m]);
        assert!(!s.is_zero() && r <= &s << 1u32);
    });
}

/// LIB-rat-round-scale: [`crate::round::div_round`] of a number of 2n words by one of n words,
/// each rule, a negative numerator; one division by [`crate::fast::div_rem`], O(M(n)) (the
/// tradeoff at the function).
#[test]
fn rounded_quotients_scale() {
    use crate::round::{Rounding, div_round};
    use num_bigint::BigInt;
    let n = 1 << 12;
    let pairs = crate::scaling::inputs(n, |m| {
        (-BigInt::from(bench_number(2 * m, 13)), bench_number(m, 17))
    });
    crate::scaling::check_order(
        "a 2n-word number divided by an n-word one and rounded",
        n,
        1,
        |m| {
            let (a, b) = &pairs[&m];
            for rule in [Rounding::TiesEven, Rounding::Floor, Rounding::AwayFromZero] {
                assert!(!div_round(a, b, rule).is_zero());
            }
        },
    );
}

/// LIB-rat-round-scale: [`crate::round::allocate`] of a total of 64 words over n weights of one
/// word each; n products and divisions of fixed size and a sort of the indices, O(n log n)
/// comparisons (the tradeoff at the function), held to n log n.
#[test]
fn allocations_scale() {
    use crate::round::allocate;
    use num_bigint::BigInt;
    let n = 1 << 12;
    let total = BigInt::from(bench_number(64, 19));
    let weights = crate::scaling::inputs(n, |m| {
        (0..m as u64)
            .map(|i| BigUint::from(i.wrapping_mul(6364136223846793005) >> 3))
            .collect::<Vec<_>>()
    });
    crate::scaling::check_n_log_n("a split of a 64-word total over n weights", n, |m| {
        let parts = allocate(&total, &weights[&m]).expect("weights");
        assert_eq!(parts.len(), m);
    });
}
