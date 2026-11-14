//! The benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `scaling.rs`.

use super::*;

/// `scaling.rs`'s sweep of the six operators at its old count, 600 pairs, moved here
/// (TEST-bench-move-l0123, author P178: many cases are a benchmark); 60 pairs stay there as
/// `an_image_holds_every_result_and_keeps_to_the_most_pieces_of_a_region`.
#[test]
fn an_image_holds_every_result_and_keeps_to_the_most_pieces_of_a_region() {
    image_holds(600, 100_000);
}

#[test]
fn a_chain_of_operators_keeps_to_its_operands_pieces() {
    // Each step's image contains every sum of members, so the members are kept.
    let a = IntervalSet::from_pieces(vec![(End::of(0), End::of(0)), (End::of(10), End::of(10))]);
    let mut acc = a.clone();
    for _ in 0..6 {
        acc = revision::forward(&Op::Add, &acc, &a);
    }
    for v in (0..=70).step_by(10) {
        assert!(acc.contains(v), "{acc} has {v}");
    }
    assert!(acc.len() <= 2, "{acc}");
    // TEST-bench-move-l0123, author P169: n was 200, now 120_000; 1x 0.45 s at load 37.
    scaling::check("a chain of `+` over eight-piece operands", 120_000, |k| {
        sum_chain(k);
    });
}

/// An open and a closed set of `n` pieces, built inside the timed run as before the split.
fn sets(n: usize) -> (IntervalSet, IntervalSet) {
    let mut rng = Rng::new(n as u64);
    (pieces(&mut rng, n, true), pieces(&mut rng, n, false))
}

// The six checks below were one test, `the_interval_operations_scale`, all at n = 4000; each
// is now a test of its own, sized to 1x of about 0.5 s (TEST-bench-move-l0123, author P169).

/// TEST-bench-move-l0123, author P169: n was 4000, now 280_000; 1x 0.31 s at load 51.
#[test]
fn capping_n_pieces_scales() {
    scaling::check("capping n pieces to 8", 280_000, |n| {
        let (a, _) = sets(n);
        assert_eq!(a.cap(8).len(), 8.min(n));
    });
}

/// TEST-bench-move-l0123, author P169: n was 4000, now 170_000; 1x 0.31 s at load 43.
#[test]
fn the_forward_product_of_two_sets_scales() {
    scaling::check("the forward `*` of two sets of n pieces", 170_000, |n| {
        let (a, b) = sets(n);
        let z = revision::forward(&Op::Mul, &a, &b.neg());
        assert!(!z.is_empty());
    });
}

/// The sign parts are one walk over the pieces and the `/` reads the divisor's sign parts
/// without 0, with no set built for either (PERF-refused-assume).
/// TEST-bench-move-l0123, author P169: n was 4000, now 760_000; 1x 0.51 s at load 42.
#[test]
fn the_sign_parts_scale() {
    scaling::check("the sign parts of n pieces", 760_000, |n| {
        let (a, _) = sets(n);
        assert!(a.sign_parts().len() >= n);
    });
}

/// TEST-bench-move-l0123, author P169: n was 4000, now 170_000; 1x 0.40 s at load 42.
#[test]
fn the_forward_quotient_of_two_sets_scales() {
    scaling::check("the forward `/` of two sets of n pieces", 170_000, |n| {
        let (a, b) = sets(n);
        let z = revision::forward(&Op::Div, &a, &b.neg());
        assert!(!z.is_empty());
    });
}

/// TEST-bench-move-l0123, author P169: n was 4000, now 330_000; 1x 0.46 s at load 32.
#[test]
fn joining_two_sets_scales() {
    scaling::check("joining two sets of n pieces", 330_000, |n| {
        let (a, b) = sets(n);
        assert!(!a.join(&b).is_empty());
    });
}

/// TEST-bench-move-l0123, author P169: n was 4000, now 680_000; 1x 0.86 s at load 32.
#[test]
fn membership_tests_in_a_set_scale() {
    scaling::check("n membership tests in a set of n pieces", 680_000, |n| {
        let (_, b) = sets(n);
        let hits = (0..n as i64).filter(|&v| b.contains(v * 7)).count();
        assert!(hits <= n);
    });
}

/// One-piece updates and queries on a set of p pieces, and a set built by p one-point joins:
/// each `O(log p)` on the persistent tree, which shares all but one path with its operand, so p
/// of them cost `O(p log p)`. With the pieces in a Vec each copied or scanned all p pieces, and
/// the test allocated 63.8 times the bytes for 8 times the size, against a limit of 11.4; it
/// now takes about 10.4 times the work and 10.4 times the bytes (COMPLEXITY.md
/// INTERVAL-persistent). Those ratios were measured at p = 1000.
/// TEST-bench-move-l0123, author P169: p was 1000, now 40_000; 1x 0.58 s at load 34.
#[test]
fn interval_set_operations_scale() {
    let p = 40_000;
    let sets = scaling::inputs(p, |n| pieces(&mut Rng::new(n as u64), n, false));
    scaling::check_order(
        "p one-piece updates and queries on a set of p pieces",
        p,
        1,
        |n| {
            let b = &sets[&n];
            let mut grown = IntervalSet::empty();
            let mut hits = 0usize;
            for i in 0..n as i64 {
                let v = 7 * i;
                let one = IntervalSet::of(v, v + 3);
                hits += usize::from(!b.join(&one).is_empty());
                hits += usize::from(!b.meet(&one).is_empty());
                hits += usize::from(!one.complement_in(b).is_empty());
                hits += usize::from(one.is_subset(b));
                // A join with a member gives the set back, so the two compare equal.
                if b.contains(v) {
                    hits += usize::from(b.join(&IntervalSet::single(v)) == *b);
                }
                grown = grown.join(&IntervalSet::single(3 * v));
            }
            assert!(hits >= 2 * n);
            assert_eq!(
                grown.bounds().map(|(_, hi)| hi.clone()),
                Some(End::of(21 * (n as i64 - 1)))
            );
        },
    );
}

#[test]
fn bounds_on_many_symbols_scale() {
    use zedc::store::lattice::Lattice;
    // TEST-bench-move-l0123, author P169: n was 1600, now 5000; 1x 0.46 s at load 51.
    scaling::check("symbolic bounds on distinct symbols", 5000, |k| {
        let (a, b) = (many(k, 0), many(k, 1));
        let j = a.join(&b);
        assert_eq!(j.bounds(zedc::store::affine::Side::Lower).len(), k);
        a.meet(&b);
    });
}

/// TEST-bench-move-l0123, author P169: n was 200, now 160_000; 1x 0.36 s at load 49.
#[test]
fn ends_in_one_word_scale_linearly() {
    check_ends("ends in i64", num_bigint::BigInt::from(0), 160_000);
}

/// TEST-bench-move-l0123, author P169: n was 200, now 95_000; 1x 0.29 s at load 47.
#[test]
fn ends_of_2_to_the_200_scale_linearly() {
    check_ends(
        "ends near 2^200",
        num_bigint::BigInt::from(1) << 200,
        95_000,
    );
}

/// Left at k = 10^6 by TEST-bench-move-l0123 (author P169): the work grows with the bits of
/// `k`, a `u32`, so no `k` that fits brings 1x near 0.5 s (69 µs at 10^6).
#[test]
fn power_bounds_scale_with_the_bits_of_the_exponent() {
    let n = 1_000_000;
    scaling::compare(
        "the bound of x^k: k = 10^6 and 8 * 10^6",
        0,
        || power_bounds(n),
        || power_bounds(scaling::FACTOR * n),
    );
}

/// TEST-bench-move-l0123, author P169: n was 200, now 500; 1x 0.53 s at load 44.
#[test]
fn kept_ends_scale_linearly() {
    let n = 500;
    let (small, large) = (kept_ends(n), kept_ends(scaling::FACTOR * n));
    for (w, m) in [(&small, n), (&large, scaling::FACTOR * n)] {
        let moved = revision::forward(&Op::Add, &w.0, &IntervalSet::single(3));
        assert_eq!(moved.meet(&w.1), w.1, "ends past 2^(10^8) at {m}");
    }
    scaling::check_order("ends past 2^(10^8)", n, 1, |m| {
        run_kept_ends(if m == n { &small } else { &large })
    });
}

/// Left at k = 10^6 + 1 by TEST-bench-move-l0123 (author P169): the work grows with the bits
/// of `k`, a `u32` (and `3k` must fit one), so no `k` brings 1x near 0.5 s (1.3 ms at 10^6).
#[test]
fn kept_arithmetic_scales_with_the_bits_of_the_exponent() {
    let n = 1_000_000;
    // k and 8k must both be 1 or 2 mod 3, so both cube roots are irrational.
    let n = n + 1;
    scaling::compare(
        "x^k + 1, k * x^k - 1, the cube root of 2^k, 3^k + 5^k, 3^(k + 1) - 3^k and \
         (2^k + 1)^3: k = 10^6 + 1 and 8 times it",
        0,
        || kept_arithmetic(n),
        || kept_arithmetic(scaling::FACTOR * n),
    );
}

/// Left at e = 10^6 by TEST-bench-move-l0123 (author P169): the work grows with the bits of
/// `e`, a `u32` (and `3e + 2` must fit one), so no `e` brings 1x near 0.5 s (0.16 ms at 10^6).
#[test]
fn equal_cores_scale_with_the_bits_of_the_exponent() {
    let n = 1_000_000;
    scaling::compare(
        "3^e * 9^(e + 1) - 3^(3e + 2) and 6^e * 5^(e + 1) - 2^e * 3^e * \
         5^(e + 1): e = 10^6 and 8 * 10^6",
        0,
        || equal_cores(n),
        || equal_cores(scaling::FACTOR * n),
    );
}

/// At 4,096 and 32,768 bits, and at 131,072 and 1,048,576. From 32,768 bits on, the indices
/// above 511, which no prime below 1,024 is 1 modulo, have roots wider than a word. Before the
/// remainder tree each of those indices took a 2-adic root: 11.0 and 12.2 times (bytes)
/// against 11.00 and 10.6 from 4,096 and from 32,768 bits (CUBE-root-alloc, COMPLEXITY.md S46).
/// The tree's first division, of the end by the product of the primes, is by 24 and 37 words
/// in the first pair, within `DIV_LEAF` (64 words), where num-bigint divides by long division,
/// and by 80 and 477 words in the second, past it. A pair from 32,768 bits (37 words, then past
/// 64) straddles the leaf: past it num-bigint divides by Burnikel and Ziegler's method where
/// `DIV_COST` says it does the least work (CROSSOVER-bench, 2026-11-12), at 262,144 bits 12%
/// less work than the reciprocal but 1.69 times the bytes, so the bytes grew 14.6 times. Past
/// the leaf no pair can keep that division on one side of `DIV_COST`'s crossover, since the
/// product grows about 6 times for 8 times the bits; the work of the two methods is equal at
/// the crossover, so crossing it changes the ratio little (8.5 times the work, 7.7 the bytes).
/// The figures above were measured at the old sizes.
/// TEST-bench-move-l0123, author P169: both pairs keep their sizes (4,096 and 131,072 bits;
/// 1x 0.39 ms and 12.3 ms). The pair from 4,096 bits is the pair whose division stays within
/// `DIV_LEAF`. The pair past the leaf, moved up to reach 1x of 0.5 s, fails its limit there (a
/// finding of TEST-bench-move-l0123, measured at load 44–59 on 2026-11-14): from 2^22 bits it
/// passes, 1x 0.24 s, 8.4 times the work and 9.5 times the bytes; from 2^23 bits, 1x 0.51 s, it
/// does 9.0 times the work but its first runs allocate 10.6 times the bytes, over 10.5.
#[test]
fn the_cube_of_a_wide_end_scales_with_its_bits() {
    for n in [4096, 131_072] {
        let (small, large) = (
            (num_bigint::BigInt::from(1) << n) + 3,
            (num_bigint::BigInt::from(1) << (scaling::FACTOR * n)) + 3,
        );
        scaling::check(
            "the cube of an end of 2^n + 3 and the image of x^3 up to it: n bits",
            n,
            |m| cube_of_a_wide_end(if m == n { &small } else { &large }),
        );
    }
}

#[test]
fn equality_over_a_wide_base_scales_with_its_bits() {
    use zedc::store::interval::Num;
    let pair = |n: usize| {
        let n32 = u32::try_from(n).unwrap();
        let wide = Num::from((num_bigint::BigInt::from(1) << n) * num_bigint::BigInt::from(3));
        (
            wide.pow(1000),
            &Num::from(2).pow(1000 * n32) * &Num::from(3).pow(1000),
        )
    };
    // Both sizes lie past the size at which num-bigint divides by Burnikel and Ziegler's method
    // in place of long division, so that its change of method is not read as the growth of
    // `strip` (from 8192 to 65536 bits the bytes allocated grow 26.3 times; from 65536 to
    // 524288, 17.2 times).
    // TEST-bench-move-l0123, author P169: n was 65536, now 2^19, the largest power of 2 for
    // which `1000 * 8n` fits the `u32` exponent of `pow`; 1x 5.3 ms at load 35.
    let n = 1 << 19;
    let (small, large) = (pair(n), pair(scaling::FACTOR * n));
    scaling::check(
        "(2^n * 3)^1000 against 2^(1000 n) * 3^1000: n bits",
        n,
        |m| equal_over_a_wide_base(if m == n { &small } else { &large }),
    );
}

/// `(3^n * 2) ** 1000` against `3 ** (1000 n) * 2 ** 1000`: the shared factor 3 is odd, so
/// `strip` takes its powers out by division, not by a shift (item SCALE-fix-strip-odd).
/// Before the fix (num-bigint's gcd in `coprime_base`, one division per factor in `strip`)
/// it took 38.5 and 55.4 times the instructions at n = 2^13 and 2^16. After it, 14.4 at 2^18,
/// 11.1 at 2^19 and 11.4 at 2^20 against limits of about 10.2 (2026-11-07, load 20 to 30):
/// `strip` is a few divisions of `2w` by `w` words, and the kernel's division of `2w` by `w`
/// costs 6.5, 9.0, 11.5 and 12.4 squarings of `w` words at `w` = 4096, 16384, 32768 and
/// 131072, so it grows faster than n log n over these sizes. With `MUL_LEAF` at 1024 it took
/// 10.7 at 2^20, and with `fast::mul`'s cost model 10.9 at 2^19 against 10.2 (2026-11-09).
/// Division by a Newton reciprocal that keeps the divisor's transforms (KERNEL-div-newton)
/// costs about 4.1 squarings at every `w` from 16384 to 131072 words, and this test took 9.3
/// times the work at 2^19 (2026-11-09, load 17), in 7 s.
#[test]
fn equality_over_a_wide_odd_base_scales_with_its_bits() {
    use zedc::store::interval::Num;
    // The set-up writes `3^n` out by the kernel's `pow_uint`, which squares by transforms:
    // num-bigint's `pow`, by Karatsuba and Toom-3, took 15 s of the test's 20 s at 8n = 2^23
    // (TEST-bench-timeout-recheck, load 36), against the 30 s limit. Same value, untimed.
    let pair = |n: usize| {
        let three_n = zed_kernel::num::pow_uint(&num_bigint::BigUint::from(3u32), n as u64);
        let wide = Num::from(num_bigint::BigInt::from(three_n) * num_bigint::BigInt::from(2));
        (
            wide.pow(1000),
            &Num::from(3).pow_by(&Num::from(1000 * n as u64)).unwrap() * &Num::from(2).pow(1000),
        )
    };
    // TEST-bench-move-l0123, author P169: n was 2^19, now 2^20; 1x 0.28 s at load 47.
    let n = 1 << 20;
    let (small, large) = (pair(n), pair(scaling::FACTOR * n));
    scaling::check(
        "(3^n * 2) ** 1000 against 3 ** (1000 n) * 2 ** 1000: n digits base 3",
        n,
        |m| equal_over_a_wide_base(if m == n { &small } else { &large }),
    );
}
