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

/// DRY-coprime-bases-one: the first `n` primes, each its own element. They are on the table
/// side of `coprime::shares_a_factor` at both sizes (asserted on the inputs: the `n`-th prime
/// is about `n ln n`, below the `n log2(n ln n)` bits of all of them), so the coprime base
/// costs O(B) word operations for `B` bits in all; factor refinement (the old zedc-int
/// `coprime_base`) tried each against every element before it, `n^2 / 2` gcds. The tree side
/// (primes past 2^20, and chains of shared primes) is over the limit at every size that fits in
/// 60 s; its benches are deferred to plan row PERF-negated-chain-unsolved in
/// wt/scratch/deferred-tests/PERF-negated-chain-unsolved.rs.
#[test]
fn the_coprime_base_of_the_first_primes_scales() {
    let inputs = crate::scaling::inputs(32768, |n| {
        let ps: Vec<BigUint> = (zed_numtheory::first_primes(n).into_iter())
            .map(BigUint::from)
            .collect();
        assert!(coprime::dense_values(&ps).is_some());
        ps
    });
    crate::scaling::check_order("the coprime base of the first n primes", 32768, 1, |n| {
        let cb = coprime::coprime_base(&inputs[&n]);
        assert_eq!(cb.elements.len(), n);
    });
}

/// Both methods of `coprime::shares_a_factor` on both sides of the table method's condition
/// (author decision A96): k values `1 + i * stride`, the largest about `k * stride`, so the
/// condition (largest value at most the bits of all the values) holds only for the small
/// strides. Prints the instructions and bytes of each method and holds their answers equal.
/// The switch is set by the proved bound, not by these numbers; they show the table is also
/// the cheaper method on its own side, and for how far beyond it. Run again for each target
/// platform and after a change to code generation. (Moved from zedc-presburger
/// `pncx_shared_factor_crossover_axis` by DRY-coprime-bases-one.)
#[test]
fn the_shared_factor_crossover_axis() {
    let mut meter = crate::scaling::Meter::new();
    for k in [16u32, 128, 1024, 4096] {
        for stride in [1u32, 4, 16, 64, 256, 1024] {
            let small: Vec<u32> = (0..k).map(|i| 1 + i * stride).collect();
            let xs: Vec<BigUint> = small.iter().map(|&v| BigUint::from(v)).collect();
            let top = 1 + (k - 1) * stride;
            let bits: u64 = xs.iter().map(BigUint::bits).sum();
            let (mut by_table, mut by_tree) = (Vec::new(), Vec::new());
            let table = meter.work(|| {
                by_table = zed_numtheory::shares_a_factor_by_table(&small, top);
            });
            let tree = meter.work(|| by_tree = coprime::shares_a_factor_by_tree(&xs));
            assert_eq!(by_table, by_tree);
            println!(
                "bench SHARED_FACTOR k={k} stride={stride} largest={top} bits={bits} table_side={} table={}/{} tree={}/{}",
                coprime::dense_values(&xs).is_some(),
                table.units,
                table.bytes,
                tree.units,
                tree.bytes
            );
        }
    }
}

/// A number of `words` words from a fixed linear congruential sequence (Knuth's MMIX
/// constants), its top word not zero: the benches need the same inputs on every run.
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

/// TEST-dry-shared-units: [`rem_uint`] and [`div_floor_int`] of a number of n words by a fixed
/// one of 1024 words. The quotient is wider than the divisor, so `fast::rem` reads the
/// dividend in blocks through one `Divisor` and `fast::div_rem` takes `div_rem_blocks`: n /
/// 1024 blocks of O(M(1024)) each, linear in n for this divisor. 1024 words is past every
/// measured crossover of `rem_takes_blocks` (227 to 1878 words for quotients 256 to 2 times
/// the divisor, `fast.rs`), so both sizes take the blocks.
#[test]
fn remainders_by_a_fixed_wide_divisor_scale() {
    let n = 1 << 14;
    let d = bench_number(1024, 7);
    let di = BigInt::from(d.clone());
    let numbers = crate::scaling::inputs(n, |m| BigInt::from(bench_number(m, 3)));
    crate::scaling::check_order(
        "a number of n words mod and div one of 1024 words",
        n,
        1,
        |m| {
            let a = &numbers[&m];
            assert!(!rem_uint(a.magnitude(), &d).is_zero());
            assert!(!div_floor_int(a, &di).is_zero());
        },
    );
}

/// TEST-dry-shared-units: [`rem_uint`] and [`div_rem_uint`] of a number of n words by one odd
/// word, at or below `DIV_LEAF`, so num-bigint's long division, O(n); and [`gcd_uint`] of the
/// same pair, whose odd part of 64 bits sends it to `gcd_big_u64`, one pass over the words
/// with no allocation, O(n). The half gcd itself, O(M(n) log n), and `inverse_mod_uint` and
/// the product and remainder trees, of the same order, are over the limit at every size that
/// fits in 60 s; their scaling test is deferred to plan row RADIX-nlog2-10_5
/// (`a_gcd_of_wide_numbers_scales` in wt/scratch/deferred-tests/RADIX-nlog2-10_5.rs).
#[test]
fn divisions_and_gcds_by_one_word_scale() {
    let n = 1 << 16;
    // 2^64 - 59, the largest prime below 2^64.
    let p = BigUint::from(0xFFFF_FFFF_FFFF_FFC5u64);
    let numbers = crate::scaling::inputs(n, |m| bench_number(m, 5) << 3u32);
    crate::scaling::check_order(
        "a number of n words mod, div and gcd one odd word",
        n,
        1,
        |m| {
            let a = &numbers[&m];
            let r = rem_uint(a, &p);
            assert_eq!(div_rem_uint(a, &p).1, r);
            assert!(!gcd_uint(a, &p).is_zero());
        },
    );
}
