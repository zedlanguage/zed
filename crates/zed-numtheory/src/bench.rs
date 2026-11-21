//! The scaling benchmarks of the routines whose cost this crate states (TEST-dry-shared-units),
//! run by `tools/run_tests.sh --bench` and left out of its default run. Each runs at n and 8n
//! and holds the ratio of the work to 10.5 (`scaling::LIMIT`). The inputs are built before any
//! run is measured (`scaling::inputs`). A routine that allocates nothing is held by
//! `check_instructions_only`, which skips the check that a run allocates. The small instances
//! of each are the correctness tests in `tests.rs`.
//!
//! Not here, since their cost does not grow with an input size: the word routines (`gcd_u64`,
//! `gcd_u128`, `mul_mod`, `pow_mod`, `pow_mod_2_64`, `inverse_mod_2_64`, `odd_root_mod_2_64`,
//! `bezout_i128`, the `m61` word arithmetic), whose operands are at most 128 bits, and
//! `is_prime`, `factor` and `next_prime`, whose input is one 64-bit word.

use std::hint::black_box;

use num_bigint::BigUint;

use crate::scaling;
use crate::{
    first_primes, gcd_big_u64, least_prime_factors, m61, odd_primes_below, pow_mod_big,
    rem_big_u64, shares_a_factor_by_table,
};

/// The `i`th of a sequence of numbers spread over `u64` (Fibonacci hashing: multiplication by
/// 2^64 / φ), so the inputs are the same on each run.
fn spread(i: usize) -> u64 {
    (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

/// A big integer of `m` words, each from [`spread`], with the top word above 0.
fn words(m: usize) -> BigUint {
    let mut digits: Vec<u64> = (0..m).map(|i| spread(i + 1)).collect();
    if let Some(top) = digits.last_mut() {
        *top |= 1;
    }
    BigUint::from_slice(
        &digits
            .iter()
            .flat_map(|&d| [d as u32, (d >> 32) as u32])
            .collect::<Vec<u32>>(),
    )
}

/// The size of the benchmarks over the words of a big integer.
const WORDS: usize = 100_000;

/// O(n) for n words, nothing allocated. Small instances:
/// `tests::the_big_remainder_and_gcd_by_a_word_agree_with_num_bigint`.
#[test]
fn the_remainder_and_gcd_by_a_word_take_n() {
    let xs = scaling::inputs(WORDS, words);
    scaling::check_instructions_only("rem_big_u64 of n words", WORDS, 1, |m| {
        black_box(rem_big_u64(black_box(&xs[&m]), 1_000_003));
    });
    scaling::check_instructions_only("gcd_big_u64 of n words", WORDS, 1, |m| {
        black_box(gcd_big_u64(black_box(&xs[&m]), 7 * 1_000_003));
    });
    // Reduced modulo `P - 1` by `rem_big_u64` first, then at most 61 squarings.
    scaling::check_instructions_only("m61::pow by an exponent of n words", WORDS, 1, |m| {
        black_box(m61::pow(3, black_box(&xs[&m])));
    });
}

/// O(n) products for an exponent of n bits, nothing allocated. 2,000 words is 128,000 bits;
/// each bit costs one or two 128-bit divisions (`mul_mod`). Small instances:
/// `tests::products_and_powers_modulo_a_word_agree_with_num_bigint`.
#[test]
fn a_power_modulo_a_word_takes_the_bits_of_its_exponent() {
    const N: usize = 2_000;
    let es = scaling::inputs(N, words);
    scaling::check_instructions_only("pow_mod_big by an exponent of n words", N, 1, |m| {
        black_box(pow_mod_big(3, black_box(&es[&m]), u64::MAX - 58));
    });
}

/// O(n) for n bytes, nothing allocated (the tables are made once, before the runs). Small
/// instances: `tests::the_eight_byte_hash_is_horners_rule`.
#[test]
fn the_byte_hash_takes_n() {
    const N: usize = 1_000_000;
    let poly = m61::PolyBytes::new(0x0f3d_5b79_a2c4_e681);
    let texts = scaling::inputs(N, |m| (0..m).map(|i| spread(i) as u8).collect::<Vec<u8>>());
    scaling::check_instructions_only("PolyBytes::hash of n bytes", N, 1, |m| {
        black_box(poly.hash(black_box(&texts[&m])));
    });
}

/// The sieves: O(n log log n) writes, which over 2^20 to 2^23 is within a few percent of
/// linear; each allocates its table. Small instances:
/// `tests::the_least_prime_table_agrees_with_trial_division`,
/// `tests::the_odd_sieve_agrees_with_trial_division` and
/// `tests::the_first_primes_are_the_primes_in_order`.
#[test]
fn the_sieves_take_n_log_log_n() {
    const TOP: usize = 1 << 20;
    scaling::check("least_prime_factors up to n", TOP, |m| {
        let table = least_prime_factors(black_box(m as u32));
        assert_eq!(table.len(), m + 1);
    });
    scaling::check("odd_primes_below n", TOP, |m| {
        let table = odd_primes_below(black_box(m as u64));
        assert_eq!(table.len(), m / 2);
    });
    // The bound doubles from 64 until it holds n primes, so the sieves cost O(t log log t) for
    // the last bound t, the earlier ones less than as much again. The bound is a power of two:
    // p_n = 1,299,709 puts it at 2^21 for n = 100,000, and p_8n lies between 2^23 and 2^24, so
    // 2^24 at 8n (both in `tests::the_first_primes_are_the_primes_in_order`). The ratio is 8
    // times ln ln 2^24 / ln ln 2^21 = 1.05, about 8.4, plus the O(n) collect.
    scaling::check("first_primes(n)", 100_000, |m| {
        assert_eq!(first_primes(black_box(m)).len(), m);
    });
}

/// O(top + B) for values of B bits up to `top`, and 2 top bytes. Small instances:
/// `tests::the_shared_factor_table_agrees_with_the_pairs`.
#[test]
fn the_shared_factor_table_takes_top_and_the_values() {
    const TOP: usize = 1 << 20;
    let vals = scaling::inputs(TOP, |m| {
        (0..m / 4)
            .map(|i| (spread(i) % m as u64) as u32 + 1)
            .collect::<Vec<u32>>()
    });
    scaling::check("shares_a_factor_by_table, n / 4 values up to n", TOP, |m| {
        let shared = shares_a_factor_by_table(black_box(&vals[&m]), m as u32);
        assert!(shared.iter().any(|&s| s));
    });
}
