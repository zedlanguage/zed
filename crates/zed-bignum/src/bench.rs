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
