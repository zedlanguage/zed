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
//! `is_prime`, `factor` and `next_prime`, whose input is one 64-bit word. `is_prime_u128`,
//! `factor_u128` and Pratt certificates, whose input is one 128-bit word, are held here per count
//! of inputs (a cost that drifts with the count would show), and timed per bit size in
//! `the_wide_routines_by_bit_size_print_their_times` (COMPLEXITY.md rows FACTOR-u128, PRIME-u128).

use std::hint::black_box;

use num_bigint::{BigInt, BigUint};

use crate::scaling;
use crate::{
    PrattCertificate, factor_u128, first_primes, floor_sum, floor_sum_i128, gcd_big_u64,
    is_prime_u128, least_prime_factors, m61, next_prime, odd_primes_below, pow_mod_big,
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

/// The `(n, m, a, b)` of the floor sum's benchmark: four numbers of `k` words each, from
/// [`spread`] at four starts, the top word of each above 0.
fn floor_sum_input(k: usize) -> [BigInt; 4] {
    let one = |from: usize| {
        let mut digits: Vec<u64> = (0..k).map(|i| spread(from + i + 1)).collect();
        if let Some(top) = digits.last_mut() {
            *top |= 1;
        }
        let halves: Vec<u32> = digits
            .iter()
            .flat_map(|&d| [d as u32, (d >> 32) as u32])
            .collect();
        BigInt::from(BigUint::from_slice(&halves))
    };
    [one(0), one(k), one(2 * k), one(3 * k)]
}

/// The size of the floor sum's benchmark: 65 words, about 1,252 decimal digits, and at 8n 520
/// words, about 10,018 digits, the 10,000-digit modulus of plan row MOD-pre-width.
const FLOOR_SUM_WORDS: usize = 65;

/// O(d²) bit operations for numbers of `d` digits, power 2 (floorsum.rs, `floor_sum`). Small
/// instances: `tests::floor_sums`.
#[test]
fn the_floor_sum_takes_d_squared() {
    scaling::check_order_inputs(
        "floor_sum of four numbers of n words",
        FLOOR_SUM_WORDS,
        2,
        floor_sum_input,
        |[n, m, a, b]: &[BigInt; 4]| {
            black_box(floor_sum(black_box(n), m, a, b));
        },
    );
}

/// The reason for the word form `floor_sum_i128` beside `floor_sum`: on the small numbers of
/// program text, the common case of zedc-affine's `lines::floor_sum`, it takes less time than
/// `floor_sum`, which allocates each number it makes. Both run on the same 10,000 cases with
/// `n` and `m` below 2^20 and `a` and `b` below 2^20 in magnitude; the least of 3 runs each is
/// printed, and the word form must take less.
#[test]
fn the_word_floor_sum_takes_less_time_than_the_big_one_on_small_numbers() {
    let cases: Vec<[i128; 4]> = (0..10_000)
        .map(|i| {
            let w = |k: usize| i128::from(spread(4 * i + k) >> 44);
            [w(0), w(1) + 1, w(2) - (1 << 19), w(3) - (1 << 19)]
        })
        .collect();
    let big: Vec<[BigInt; 4]> = cases.iter().map(|c| c.map(BigInt::from)).collect();
    let (word_ns, word) = scaling::least_cpu_ns(3, || {
        cases
            .iter()
            .map(|&[n, m, a, b]| floor_sum_i128(n, m, a, b).expect("fits"))
            .sum::<i128>()
    });
    let (big_ns, sum) = scaling::least_cpu_ns(3, || {
        big.iter()
            .map(|[n, m, a, b]| floor_sum(n, m, a, b))
            .sum::<BigInt>()
    });
    assert_eq!(BigInt::from(word), sum);
    eprintln!(
        "floor sums of 10,000 small cases: floor_sum_i128 {:.3} ms, floor_sum {:.3} ms",
        word_ns as f64 / 1e6,
        big_ns as f64 / 1e6
    );
    assert!(
        word_ns < big_ns,
        "the word form took {word_ns} ns, the big one {big_ns} ns"
    );
}

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

/// O(n) for n odd numbers from `2^64 + 1` up, each decided by the strong test to 13 bases (or
/// the first base it fails), nothing allocated. Small instances: `wide::tests`.
#[test]
fn the_wide_prime_test_takes_the_count_of_its_inputs() {
    const N: usize = 4_000;
    scaling::check_instructions_only("is_prime_u128 on n odd numbers above 2^64", N, 1, |m| {
        for i in 0..m as u128 {
            black_box(is_prime_u128(black_box((1 << 64) + 2 * i + 1)));
        }
    });
}

/// O(n) for the certificates of n primes from `PSI_13` up (odd, as `PSI_13` is), built before the
/// runs; checking allocates nothing. Small
/// instances: `wide::tests::the_mersenne_primes_89_107_127_have_checked_certificates`.
#[test]
fn checking_certificates_takes_their_count() {
    const N: usize = 4;
    let make = |m: usize| -> Vec<PrattCertificate> {
        (crate::PSI_13..)
            .step_by(2)
            .filter_map(PrattCertificate::build)
            .take(m)
            .collect()
    };
    let certs = scaling::inputs(N, make);
    scaling::check_instructions_only("PrattCertificate::check of n certificates", N, 1, |m| {
        for c in &certs[&m] {
            assert_eq!(black_box(c).check(), Ok(()));
        }
    });
}

/// O(n) for n products of two 36-bit primes (fixed seeds, built before the runs), factored:
/// each takes rho past its cut-off and then curves of the elliptic curve method. Products of one
/// size, not consecutive numbers: the cost of a random number is mostly trial division with a
/// rare product of two large primes, so the first 128 numbers above `2^80` cost 13.2 times less
/// than the first 1024 per number (measured 2026-11-22), a sample spread and not a growth. Small
/// instances: `wide::tests`.
#[test]
fn factoring_72_bit_products_takes_their_count() {
    const N: usize = 96;
    let make = |m: usize| -> Vec<u128> {
        let mut rng = zed_hash::Xorshift64::new(0x7a_2026_1122);
        let mut prime = move || loop {
            let x = rng.next_u64();
            if let Some(p) = next_prime(x >> 28 | 1 << 35).filter(|p| p >> 36 == 0) {
                return u128::from(p);
            }
        };
        (0..m).map(|_| prime() * prime()).collect()
    };
    let ns = scaling::inputs(N, make);
    scaling::check_order(
        "factor_u128 on n products of two 36-bit primes",
        N,
        1,
        |m| {
            for &n in &ns[&m] {
                black_box(factor_u128(black_box(n)));
            }
        },
    );
}

/// Prints the least time of three runs of `is_prime_u128` on the largest prime below `2^b` and
/// the most over 6 products of two primes of `b / 2` bits (fixed seeds) of `factor_u128`, for the
/// bit sizes of the plan (65, 80, 82, 96, 112, 128): the worst cases of COMPLEXITY.md rows
/// FACTOR-u128 and PRIME-u128. Only the answers are checked; the times are a record.
#[test]
fn the_wide_routines_by_bit_size_print_their_times() {
    let mut rng = zed_hash::Xorshift64::new(0x2026_1122);
    let mut next = move || rng.next_u64();
    for bits in [65u32, 80, 82, 96, 112, 128] {
        let top = if bits == 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        let p = (0..=top)
            .rev()
            .step_by(2)
            .find(|&p| is_prime_u128(p))
            .expect("a prime");
        let (prime_ns, ok) = scaling::least_cpu_ns(3, || is_prime_u128(black_box(p)));
        assert!(ok);
        let half = bits / 2;
        let mut most = 0u128;
        for _ in 0..6 {
            let pick = |r: u64, b: u32| -> u64 {
                let r = r >> (64 - b) | 1 << (b - 1);
                next_prime(r)
                    .filter(|&q| u128::from(q) >> b == 0)
                    .unwrap_or_else(|| (0..r).rev().find(|&q| crate::is_prime(q)).expect("a prime"))
            };
            let a = pick(next(), half);
            let b = pick(next(), bits - half);
            let n = u128::from(a) * u128::from(b);
            let (ns, f) = scaling::least_cpu_ns(1, || factor_u128(black_box(n)));
            assert_eq!(f.iter().map(|&(q, e)| q.pow(e as u32)).product::<u128>(), n);
            most = most.max(ns);
        }
        eprintln!(
            "{bits} bits: is_prime_u128(largest prime) {:.3} ms; factor_u128(two {half}-bit primes) most {:.1} ms",
            prime_ns as f64 / 1e6,
            most as f64 / 1e6
        );
    }
}
