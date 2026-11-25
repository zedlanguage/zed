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
/// (primes past 2^24, 12.815 on 2026-11-20; past 2^20, 262144 primes are on the table side,
/// so a bench there does not measure the tree at 8 n; and chains of shared primes, 16.277) is
/// over the limit at every size that fits in 60 s; its benches are deferred to plan row
/// PERF-negated-chain-unsolved in wt/scratch/deferred-tests/PERF-negated-chain-unsolved.rs.
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

/// PERF-coprime-base-wide-few: both paths of `coprime::coprime_base` on both sides of the
/// condition at `coprime::one_wide` (author decision A96). One input `x` of about `n` bits, the
/// first `k` primes to random exponents (each about `n / 2k` bits) times random odd words, and
/// the `k` primes as the other inputs, `m` bits together; the condition `m <= floor(log2 n)`
/// holds for the smaller `k`. `with_one_wide` is correct for any wide input (its proof does not
/// use the condition), so both paths run on every case, their bases are held equal, and the
/// instructions and bytes of each are printed. The switch is set by the proved bound, not by
/// these numbers. Run again for each target platform and after a change to code generation.
#[test]
fn the_one_wide_crossover_axis() {
    let mut meter = crate::scaling::Meter::new();
    let mut rng = crate::seed::Rng::new(0x5eed_c0b1);
    let primes = zed_numtheory::first_primes(10);
    for n in [1u64 << 12, 1 << 15] {
        for k in 1..=primes.len() {
            let ps = &primes[..k];
            let mut x = BigUint::one();
            for &p in ps {
                let e = n / (2 * k as u64 * BigUint::from(p).bits());
                x *= pow_uint(&BigUint::from(p), e + rng.below_u64(e / 4 + 1));
            }
            while x.bits() < n {
                x *= rng.next_u64() | 1;
            }
            let mut xs = vec![x];
            xs.extend(ps.iter().map(|&p| BigUint::from(p)));
            let m: u64 = xs[1..].iter().map(BigUint::bits).sum();
            let (mut one, mut halves) = (None, None);
            let fast = meter.work(|| one = Some(coprime::with_one_wide(&xs, 0)));
            let general = meter.work(|| halves = Some(coprime::by_halves(&xs)));
            let (mut one, _) = one.expect("run by the meter");
            let mut halves = halves.expect("run by the meter");
            one.elements.sort();
            halves.elements.sort();
            assert_eq!(one.elements, halves.elements, "n {n}, k {k}");
            println!(
                "bench ONE_WIDE n={n} k={k} m={m} one_wide_side={} one_wide={}/{} halves={}/{}",
                coprime::one_wide(&xs).is_some(),
                fast.units,
                fast.bytes,
                general.units,
                general.bytes
            );
        }
    }
}

/// PERF-coprime-base-wide-few: the word path of `coprime::coprime_base_exponents`
/// (`zed_numtheory::coprime_base_u64`, factor refinement, O(k^2) word gcds) against the general
/// path (`coprime::by_halves`) on `k` word inputs, on both sides of the measured switchover
/// `coprime::WORD_INPUTS` (author decision A96). Three families: the first `k` primes (no prime
/// shared, refinement's worst case, each tried against every element before it); products of
/// three primes drawn from the first `k` (many shared); and random words at the top bit, which
/// share little. Prints the instructions and bytes of each method and holds their bases equal.
/// The switchover is the largest `k` at which the word path is the cheaper on every family;
/// the measurements on both sides of it are at `coprime::WORD_INPUTS`. Run
/// again for each target platform and after a change to code generation.
#[test]
fn the_word_crossover_axis() {
    let mut meter = crate::scaling::Meter::new();
    let mut rng = crate::seed::Rng::new(0x5eed_c0b2);
    let primes = zed_numtheory::first_primes(512);
    // Every `k` up to 16, where the families cross, then the sizes beyond; `WORD_INPUTS` and the
    // one past it are always on the axis, so a change to the constant keeps both sides measured.
    let mut ks: Vec<usize> = (1..=16)
        .chain([24, 32, 48, 64, 96, 128, 192, 256, 384, 512])
        .collect();
    ks.extend([coprime::WORD_INPUTS, coprime::WORD_INPUTS + 1]);
    ks.sort_unstable();
    ks.dedup();
    for k in ks {
        let distinct: Vec<u64> = primes[..k].to_vec();
        let shared: Vec<u64> = (0..k)
            .map(|_| {
                (0..3)
                    .map(|_| primes[rng.below_u64(k as u64) as usize])
                    .product()
            })
            .collect();
        let wide: Vec<u64> = (0..k).map(|_| rng.next_u64() | 1 << 63).collect();
        for (family, ws) in [("distinct", distinct), ("shared", shared), ("random", wide)] {
            let xs: Vec<BigUint> = ws.iter().map(|&w| BigUint::from(w)).collect();
            let (mut by_words, mut halves) = (None, None);
            let word = meter.work(|| by_words = Some(zed_numtheory::coprime_base_u64(&ws)));
            let general = meter.work(|| halves = Some(coprime::by_halves(&xs)));
            let (mut by_words, _) = by_words.expect("run by the meter");
            let mut halves = halves.expect("run by the meter").elements;
            by_words.sort_unstable();
            halves.sort();
            let by_words: Vec<BigUint> = by_words.into_iter().map(BigUint::from).collect();
            assert_eq!(by_words, halves, "{family} k {k}");
            println!(
                "bench WORDS family={family} k={k} word_side={} words={}/{} halves={}/{}",
                k <= coprime::WORD_INPUTS,
                word.units,
                word.bytes,
                general.units,
                general.bytes
            );
        }
    }
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

/// The first `n` primes above 2^shift, by a sieve of the segment
/// `[2^shift, 2^shift + 40 n + 4096)`, which holds more than `n` of them (the density is about
/// 1 / 13.9 near 2^20 and 1 / 16.6 near 2^24). Each input has `shift + 1` or more bits, so
/// products and gcds are of many words.
fn primes_above(shift: u32, n: usize) -> Vec<BigUint> {
    let (lo, len) = (1usize << shift, 40 * n + 4096);
    let mut composite = vec![false; len];
    let mut p = 2;
    while p * p < lo + len {
        let first = lo.div_ceil(p) * p;
        for m in (first..lo + len).step_by(p) {
            composite[m - lo] = true;
        }
        p += 1;
    }
    let out: Vec<BigUint> = (0..len)
        .filter(|&i| !composite[i])
        .map(|i| BigUint::from(lo + i))
        .take(n)
        .collect();
    assert_eq!(out.len(), n);
    out
}

/// DRY-coprime-bases-one: `n` distinct primes past 2^24, each its own element. Until
/// PERF-negated-chain-unsolved (negchain1, 2026-11-20) Bernstein's trees (`by_halves`) answered
/// these, 12.815 (load 41 to 43). The inputs have 25 bits, at most `coprime::FACTOR_BITS`,
/// and both sizes have at least `coprime::FACTOR_INPUTS`, so `coprime_base` now factors each
/// into primes (`zed_numtheory::coprime_base_by_factoring`): a primality test each, linear in
/// `n` at a fixed width (proof in that function's comment). Measured 2026-11-20 (load 42):
/// 184,147,662 / 1,484,543,186 instructions, 8.062, bytes 8.0.
#[test]
fn the_coprime_base_of_distinct_primes_scales() {
    let inputs = crate::scaling::inputs(32768, |n| {
        let ps = primes_above(24, n);
        assert!(coprime::dense_values(&ps).is_none());
        ps
    });
    crate::scaling::check("the coprime base of n distinct primes", 32768, |n| {
        let cb = coprime::coprime_base(&inputs[&n]);
        assert_eq!(cb.elements.len(), n);
    });
}

/// DRY-coprime-bases-one: `q_i q_(i+1)` for `n + 1` primes `q_i` past 2^20, each shared by two
/// inputs. Until PERF-negated-chain-unsolved (negchain1, 2026-11-20) Bernstein's trees
/// answered these, 16.277 (primes in a row, load 41 to 43). The primes are below 2^21, so the
/// products have 41 or 42 bits, on the factoring side of `coprime::FACTOR_BITS` at both sizes
/// (with at least `coprime::FACTOR_INPUTS` inputs), linear in `n` at a fixed width (proof at
/// `zed_numtheory::coprime_base_by_factoring`); each input costs a primality test and one rho
/// split; rho takes about
/// `p^(1/4)` steps for the least prime `p`, and Brent's doubling of its batches makes that a step
/// function of `p`. Primes in a row would widen with `n` (65,537 of them past 2^20 reach about
/// 2^21), and the cost of each input with them: at 8192 and 65536 inputs that gave 9.071, with
/// the bytes at 8.0 and the instructions an input 1.134 times as many (2026-11-20, load 42), the
/// input's doing, not the method's. So both sizes take their primes from the same 65,537 primes
/// past 2^20, size `n` every `65536 / n`-th of them: the widths are spread alike at both sizes,
/// and only the count changes. Measured 2026-11-20 (load 56): 500,655,760 / 3,996,718,440
/// instructions, 7.983, bytes 8.0.
#[test]
fn the_coprime_base_of_a_chain_of_shared_primes_scales() {
    let inputs = crate::scaling::inputs(8192, |n| {
        let ps = primes_above(20, 65537);
        let step = 65536 / n;
        (0..n)
            .map(|i| &ps[i * step] * &ps[(i + 1) * step])
            .collect::<Vec<BigUint>>()
    });
    crate::scaling::check("the coprime base of n products p_i p_(i+1)", 8192, |n| {
        let cb = coprime::coprime_base(&inputs[&n]);
        assert_eq!(cb.elements.len(), n + 1);
    });
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

/// TEST-kernel-num-rat-units: [`Rat::rem_euclid`] and [`Rat::div_euclid`] of a negative plain
/// integer of n words by the fixed one of 1024 words of the bench above. `rem_euclid` takes
/// `rem` (one `fast::Divisor`, blocks of the dividend, O(n) for this divisor) and `euclid`
/// (`|m| - r`, O(1024) words); `div_euclid` takes `fast::div_euclid`, whose quotient is wider
/// than the divisor, so `div_rem_blocks`, O(n) for this divisor, and its memory is asked as the
/// divisor's transforms and twice the dividend's width (the arm of `div_euclid` that the unit
/// tests do not reach, at `num.rs` "`k > n`").
#[test]
fn euclidean_remainders_and_quotients_of_negative_integers_scale() {
    let n = 1 << 14;
    let m = Rat::int(BigInt::from(bench_number(1024, 7)));
    let numbers = crate::scaling::inputs(n, |w| Rat::int(-BigInt::from(bench_number(w, 3))));
    crate::scaling::check_order(
        "a negative number of n words rem_euclid and div_euclid one of 1024 words",
        n,
        1,
        |w| {
            let a = &numbers[&w];
            let r = a.rem_euclid(&m).unwrap();
            assert!(!r.is_negative() && !r.is_zero() && r < m);
            assert!(a.div_euclid(&m).unwrap().is_negative());
        },
    );
}

/// TEST-kernel-num-rat-units: the kept path of `Rat::sum`, two integers of n words times the
/// same kept power `3^(2^20)`. The common power factors out unbuilt, so the sum is the sum of
/// the two coefficients (a product by the empty power, 1, and a sum, O(n)) and `Rat::build`'s
/// test of whether 3 divides the result (one pass over its words, O(n)); nothing of
/// `3^(2^20)`, 1.66 million bits, is built.
#[test]
fn a_sum_sharing_a_kept_power_scales_with_its_coefficients() {
    let n = 1 << 14;
    let three = power(3, 1 << 20);
    let terms = crate::scaling::inputs(n, |w| {
        let [a, b] = [3u64, 5].map(|s| {
            let r = three
                .mul(&Rat::int(BigInt::from(bench_number(w, s))))
                .unwrap();
            assert!(!r.is_plain());
            r
        });
        (a, b)
    });
    crate::scaling::check_order(
        "a sum of two numbers of n words times one kept power",
        n,
        1,
        |w| {
            let (a, b) = &terms[&w];
            assert!(!a.add(b).unwrap().is_plain());
        },
    );
}

/// Item PERF-wide-odd-base-ratio-9: [`nth_root_rem_uint`] of a number of n words for `k = 3`
/// and `k = 64`, O(M(n)) for a fixed `k` (proof at `nth_root_near`), against num-bigint's
/// `nth_root`, 19.3 and 36.3 times from 4,096 to 32,768 words. The levels of the recursion
/// halve, so the work is a sum over sizes `n / 2^i`, and the levels below the kernel product's
/// transforms (num-bigint's Toom-3, about 2.76 times a doubling) grow faster than the top:
/// `T(8n) / T(n)` measured 10.09 and 10.23 at 2,048 words, 9.64 and 10.02 at 4,096, 9.30 and
/// 9.70 at 8,192, 9.26 and 9.40 at 16,384, and 9.10 and 9.17 at 32,768, where the squaring of
/// the same numbers measured 9.18 (2026-11-20, load 23 to 85). 32,768 words is the first size
/// where both meet the product's own ratio, as `O(M(n))` predicts.
#[test]
fn kth_roots_scale() {
    let n = 1 << 15;
    let numbers = crate::scaling::inputs(n, |m| bench_number(m, 13));
    for k in [3u32, 64] {
        let what = format!("the root of index {k} of a number of n words");
        crate::scaling::check_order(&what, n, 1, |m| {
            let (r, rem) = nth_root_rem_uint(&numbers[&m], k);
            assert!(!r.is_zero() && rem < numbers[&m]);
        });
    }
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

/// Plan row KERNEL-bz-short-quotient: [`div_rem_uint`] of a number of `n + 32` words by one of
/// `n` words, a quotient of at most 33 words, under `DIV_LEAF`, by `fast::div_rem_short_quotient`.
/// It went to num-bigint's division, which past 128 words in the dividend and 64 in the
/// divisor takes Burnikel and Ziegler's recursive division by those counts alone, whatever the
/// quotient's width (num-bigint 0.4.8, `div_rem_core`, src/biguint/division.rs:343-346), and
/// whose recursion copies the halves of the divisor at each level (:274-287): at 4,096 and
/// 32,768 words it allocated 1,167,976 and 12,481,320 bytes, 10.7 times, over the limit, in
/// 2,633,137 and 23,655,300 instructions, 8.98 times (2026-11-22, run h5-req15). By
/// `div_rem_short_quotient`: 152,664 and 1,206,360 bytes, 7.90 times, in 1,771,613 and
/// 14,166,260 instructions, 8.00 times (2026-11-22, run h5-req21).
#[test]
fn a_short_quotient_of_a_wide_number_scales() {
    let n = 1 << 12;
    let numbers = crate::scaling::inputs(n, |m| (bench_number(m + 32, 17), bench_number(m, 19)));
    crate::scaling::check_order(
        "a number of n + 32 words div and mod one of n words",
        n,
        1,
        |m| {
            let (a, b) = &numbers[&m];
            let (q, r) = div_rem_uint(a, b);
            assert!(q.bits() > 64 * 31 && &r < b);
        },
    );
}

/// PERF-fingerprint-montgomery: the instructions of one fingerprint of an integer of `w` words,
/// `w` in 2, 4, 8, 16 and 64, in the three forms [`Rat::fingerprint`] was measured in: the
/// residues modulo `2^61 - 1` (`M61`, what the priorities of big values read before the drawn
/// primes, one modulus), the residues modulo the two drawn primes by 128-bit division
/// (`ByDivision`), and the same in Montgomery form (`Drawn`, what `fingerprint` uses). Each
/// count is of 64 numbers of a size, made before the count, and of fresh calls, not the cached
/// value. Two numbers have one fingerprint in Montgomery form exactly when they have one by
/// division (the held residue is `x R mod p`, `R` a unit), which is asserted. The counts are
/// printed (`bench FINGERPRINT`) and written at `Rat::fingerprint`; run again for each target
/// platform and after a change to code generation.
#[test]
fn fingerprint_instructions() {
    let mut meter = crate::scaling::Meter::new();
    let [p1, p2] = crate::priority::fingerprint_primes();
    let (d1, d2) = (ByDivision(p1), ByDivision(p2));
    let (m1, m2) = (
        Drawn(Montgomery64::new(p1), p1),
        Drawn(Montgomery64::new(p2), p2),
    );
    for w in [2usize, 4, 8, 16, 64] {
        let xs: Vec<Rat> = (0..64u64)
            .map(|k| Rat::int(BigInt::from(bench_number(w, 0x5eed + k))))
            .collect();
        let (mut a, mut b, mut c) = (Vec::new(), Vec::new(), Vec::new());
        let old = meter.work(|| a = xs.iter().map(|x| x.residues_in(&M61)).collect());
        let div = meter.work(|| b = xs.iter().map(|x| x.fingerprint_in(&d1, &d2)).collect());
        let mont = meter.work(|| c = xs.iter().map(|x| x.fingerprint_in(&m1, &m2)).collect());
        for i in 0..xs.len() {
            for j in 0..xs.len() {
                assert_eq!(b[i] == b[j], c[i] == c[j], "w {w}, {i} and {j}");
            }
        }
        assert_eq!(a.len(), xs.len());
        // Time as well: a 128-bit division is one instruction of tens of cycles, so the counts
        // alone favor `ByDivision`. The least of 5 trials of 100 passes over the 64 numbers, in
        // nanoseconds a fingerprint.
        let time = |f: &dyn Fn(&Rat) -> [u64; 4]| {
            (0..5)
                .map(|_| {
                    let start = std::time::Instant::now();
                    for _ in 0..100 {
                        for x in &xs {
                            std::hint::black_box(f(std::hint::black_box(x)));
                        }
                    }
                    start.elapsed().as_nanos() as f64 / 6400.0
                })
                .fold(f64::INFINITY, f64::min)
        };
        let ns = [
            time(&|x| {
                let (neg, n, d) = x.residues_in(&M61);
                [n | u64::from(neg) << 63, d, 0, 0]
            }),
            time(&|x| x.fingerprint_in(&d1, &d2)),
            time(&|x| x.fingerprint_in(&m1, &m2)),
        ];
        println!(
            "bench FINGERPRINT words={w} m61={} division={} montgomery={} (instructions for 64) \
             ns_each m61={:.1} division={:.1} montgomery={:.1}",
            old.units, div.units, mont.units, ns[0], ns[1], ns[2]
        );
    }
}
