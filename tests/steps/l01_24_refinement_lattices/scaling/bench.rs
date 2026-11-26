//! The benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `scaling.rs`.

use super::*;

/// TEST-dry-shared-units: `affine::write_sum` of n terms with coefficients of both signs:
/// O(the length written), its documented cost. Its output is checked in
/// zedc-lattice affine.rs's tests. The sum is written to a counter of its bytes, not a
/// `String`: a growing `String` doubles its buffer, so the bytes it allocates depend on where
/// the length falls between two powers of two, 16 times at 8n in one run, though the text is
/// 8 times as long. The counter allocates nothing, and neither does `write_sum` for words that
/// fit a machine word, so only the work is measured.
#[test]
fn a_sum_of_n_terms_is_written_in_its_length() {
    use std::fmt::Write;
    use zedc::store::int::Int;
    /// Counts the bytes written to it.
    struct Count(usize);
    impl Write for Count {
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            self.0 += s.len();
            Ok(())
        }
    }
    let sums = scaling::inputs(1 << 14, |n| {
        (0..n)
            .map(|i| (format!("x{i}"), Int::from(i as i128 - n as i128 / 2)))
            .collect::<Vec<_>>()
    });
    scaling::check_instructions_only("writing a sum of n terms", 1 << 14, 1, |n| {
        let mut s = Count(0);
        let terms = sums[&n].iter().map(|(x, c)| (x.as_str(), c));
        zedc::store::affine::write_sum(&mut s, terms, &Int::from(7), |o, x| o.write_str(x))
            .unwrap();
        assert!(s.0 > n);
    });
}

/// `scaling.rs`'s sweep of the six operators at its old count, 600 pairs, moved here
/// (TEST-bench-move-l0123, author P178: many cases are a benchmark); 60 pairs stay there as
/// `an_image_holds_every_result_and_keeps_to_the_most_pieces_of_a_region`.
#[test]
fn an_image_holds_every_result_and_keeps_to_the_most_pieces_of_a_region() {
    image_holds(600);
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
    // A new seed each run, printed; each size draws its operands from it anew, so the runs the
    // check repeats at one size do the same work.
    let (_, seed) = Rng::fresh("a chain of `+` over eight-piece operands");
    scaling::check("a chain of `+` over eight-piece operands", 120_000, |k| {
        sum_chain(&mut Rng::new(seed), k);
    });
}

/// Row RANGE-result-hull: each of `n` functions of a ranged parameter calls the one before it,
/// so each call reads the hull of a signature (`call_hull`, one lookup) and each function takes
/// one hull of its body (`hull_into`, COMPLEXITY.md C65): the check is linear in `n`. The text
/// is read and resolved before the run is timed, so the run times the checker alone.
#[test]
fn a_chain_of_ranged_functions_prints_each_hull_in_linear_time() {
    use super::super::written::{hull_chain, hull_chain_sig};
    use zed_tests::step_helpers::l01_26_type_resolution::Resolved;
    let n = 2000;
    let units = scaling::inputs(n, |m| Resolved::new(&hull_chain(m)));
    scaling::check("a chain of n functions of a ranged parameter", n, |m| {
        let info = units[&m].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        let last = hull_chain_sig(m - 1);
        assert!(
            info.sigs.values().any(|s| s.to_string() == last),
            "no signature {last}"
        );
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
/// the test allocated 63.8 times the bytes for 8 times the size, against the limit of 11.4 of
/// 2026-11-10; it now takes about 10.4 times the work and 10.4 times the bytes (COMPLEXITY.md
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

/// p one-point joins, each followed by the reduction against a class: the set of points `3i +
/// 1` grows by one at its top, and each reduction against every integer narrows the class to
/// the least one holding the points, `1 mod 3` from two points on (FAIL-lazy-join-random-seed).
/// The gcd of their differences is kept at each node (zedc-lattice
/// `IntervalSet::point_spacing`), so a reduction after a join reads all but the join's path
/// from the nodes and costs `O(log p)`, and the p of them `O(p log p)`; the points walked at
/// each would cost `Θ(p²)`, the case of CHECK-literal-union-spaced. Its small instance is
/// zedc-lattice revision.rs `a_set_grown_one_point_at_a_time_has_its_least_class_after_each_join`.
///
/// Cost against the code before the fix (Colab v5e2, zed_icount): 967.8M instructions at p =
/// 40,000, was 519.0M (+86%; ratio 9.50, was 9.43). The code before gave a wrong class here,
/// every integer for every set of two points or more, which the small instance shows by
/// failing on it; the cost over it is the cost of the least class `1 mod 3`. Where it goes
/// (callgrind, debug, 4,000 joins): about 33M over the code before, the gcd fold of
/// zedc-lattice `Spacing` (`point` 5.5M, `join_word` 5.4M, `gcd_u64` 3.5M, `node` 3.4M,
/// `subtree` 3.3M, the `OnceLock` of each new node 3.0M, comparisons of `Num` 2.6M, the rest
/// under 2M each). Why it cannot be much cheaper: a join replaces the nodes of one path,
/// `O(log p)` of them, and each new node of height `SPACING_KEPT_FROM` or more has no gcd
/// until one is computed from its children, so the least class after each join takes
/// `Θ(log p)` gcds; the walk below the kept height and the height itself are the measured
/// minimum (the table at zedc-lattice `SPACING_KEPT_FROM`), and each gcd is of machine words.
#[test]
fn reductions_of_a_growing_set_of_points_scale() {
    use zedc::store::lattice::Congruence;
    scaling::check_order(
        "p one-point joins each reduced against a class",
        40_000,
        1,
        |n| {
            // Every integer: the class the reduction gives is the points' own.
            let class = Congruence::new(1, 0);
            let mut grown = IntervalSet::empty();
            let mut last = class.clone();
            for i in 0..n as i64 {
                grown = grown.join(&IntervalSet::single(3 * i + 1));
                let (x, c) = revision::reduce_congruence(&grown, &class);
                assert_eq!(x.len(), i as usize + 1);
                last = c;
            }
            assert_eq!(last, Congruence::new(3, 1));
        },
    );
}

/// A set grown at its front by p joins of a one-piece set wholly below it, every other one
/// touching its first piece (PERF-ref-abs-gap-under-9, zedc-lattice `below_then`): each join
/// is one `O(log p)` path, so the p of them cost `O(p log p)` (`union` has the same bound with
/// four splits a level). Measured on hm2 (2026-11-23): 9.782 in instructions (809,655,109 at
/// 40,000 joins, 7,919,672,499 at 320,000), the same before and after the merge of 27f390c2f.
///
/// The prediction for c·n·ln n work, 8 ln(8n) / ln n = 8 · 12.676 / 10.597 = 9.570 at
/// n = 40,000, is below that, because the work here is not c·n·ln n: join i is made on a set
/// of p_i = i / 2 pieces, so it costs c·ln(i / 2) + b, and the n joins cost
/// c·ln(n! / 2^n) + b·n = c·n·(ln n − 1 − ln 2) + b·n by Stirling's formula (up to O(ln n)).
/// The `− n(1 + ln 2)` term, absent from the plain prediction, raises the ratio at 8n: with
/// b = 0 it is 8 (ln 8n − 1 − ln 2) / (ln n − 1 − ln 2) = 8 · 10.983 / 8.904 = 9.868, and any
/// b > 0 lowers it toward 8. The measured 9.782 lies between, and the two sizes give
/// c = (24,749 − 20,241) / (10.983 − 8.904) = 2,168 and b = 20,241 − 2,168 · 8.904 = 941
/// instructions per join, both positive (inferred from two sizes, so a fit, not a check).
/// A ratio under 9 at these sizes needs joins at the front in O(1), not O(log p): a structure
/// with worst-case O(1) end operations under persistence, the open question of
/// PERF-ref-abs-gap-under-9. Under the limit 10.5 (COMPLEXITY.md, row INTERVAL-joins-below).
#[test]
fn joins_below_a_set_scale() {
    scaling::check_order(
        "p joins of a piece below a set of p pieces",
        40_000,
        1,
        |n| {
            let grown = joins_below(n);
            assert_eq!(grown.len(), n.div_ceil(2) + 1);
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
///
/// The inputs are built by `check_inputs`, only at the sizes each process runs, where both
/// sizes were built, and each moved and met, before the first run. With only that, the piece
/// still stopped at 20 s on a VM: the new process for 8n built its 4000 pieces and moved and
/// met them once more to check them, under DynamoRIO, for over 20 s before its run (b22-tests8
/// job f16 on v5e1). The answer is now checked in the run measured (`run_kept_ends`), and the
/// piece passes, 7.991 times the instructions at 8n, 43.0 s in all on hm5 (job f32;
/// FAIL-bench-kept-ends-past-limit).
#[test]
fn kept_ends_scale_linearly() {
    let n = 500;
    scaling::check_inputs("ends past 2^(10^8)", n, kept_ends, run_kept_ends);
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

/// At 4,096 and 32,768 bits, at 262,144 and 2,097,152, and at 2^23 and 2^26. From 32,768 bits
/// on, the indices above 511, which no prime below 1,024 is 1 modulo, have roots wider than a
/// word. Before the
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
/// TEST-bench-move-l0123, author P169: the pair from 4,096 bits is the pair whose division stays
/// within `DIV_LEAF`. On 2026-11-14 the pair from 2^23 bits allocated 10.6 times the bytes, and
/// on 2026-11-17 the pair from 262,144 bits 10.71 times; neither repeats. Remeasured on
/// 2026-11-22 at load 66 to 91 (PERF-l0124-cube-bytes, CUBE-remtree-crossover), work and bytes:
/// from 4,096 bits 6.43 and 3.36; from 262,144 bits, the pair that crosses `DIV_COST`'s
/// crossover, 8.80 and 4.38; from 2^20 bits 8.46 and 8.34; from 2^23 bits, 1x 0.6 to 0.7 s,
/// 8.52 and 8.63. So the three pairs below are the leaf, the crossover and the 1 s size.
#[test]
fn the_cube_of_a_wide_end_scales_with_its_bits() {
    for n in [4096, 262_144, 1 << 23] {
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
/// times the work at 2^19 (2026-11-09, load 17), in 7 s. At 2^20 it took 9.22 (load 29),
/// above the goal 9; `strip` skipping its last division when the steps down already leave
/// the quotient made it 9.25 on 23% fewer instructions (2026-11-20, load 61), and its cost is
/// O(N log N) in the transform points `N`, `2^15` here, whose predicted ratio is at most 9.6
/// (proof at `zed_kernel::num::coprime::strip`, item PERF-wide-odd-base-ratio-9).
#[test]
fn equality_over_a_wide_odd_base_scales_with_its_bits() {
    use zedc::store::interval::Num;
    // The set-up writes `3^n` out by the kernel's `pow_uint`, which squares by transforms:
    // num-bigint's `pow`, by Karatsuba and Toom-3, took 15 s of the test's 20 s at 8n = 2^23
    // (TEST-bench-timeout-recheck, load 36), against the 30 s limit. Same value, untimed.
    // `wide.pow(1000)` finds the least root of `3^n * 2` (`least_root`), whose square root by
    // num-bigint took 19.2 s at 8n against 0.56 s at n, most of the test's 22 s against its
    // 22 s limit; by the kernel's `sqrt_rem_uint`, 0.33 s at 8n and the whole set-up 0.52 s
    // (item PERF-wide-odd-base-ratio-9, 2026-11-20, load 80).
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

/// Row L1.39-head-rule: the head of `loops::houdini_loop(k)`, entered with `k` candidate
/// conjuncts `i <= s_j`, keeps the even ones by the M0.5 widening (Houdini's greatest fixpoint,
/// FME 2001, doi:10.1007/3-540-45251-6_29). The first phase stabilizes the head in a constant
/// number of passes (the entry, a pass that refutes the odd conjuncts, a pass that changes
/// nothing), each a join, a meet, a shift and a widening of `k` bounds in ordered sets,
/// O(k log k) in all: predicted T(8k)/T(k) = 8 · log 32768 / log 4096 = 10.0 at k = 4096;
/// measured 9.93 (instructions, 2026-11-21, load5 70), under the limit 10.5.
#[test]
fn a_loop_head_drops_refuted_conjuncts_in_k_log_k() {
    use super::super::loops::{houdini_loop, upper_symbols};
    use zedc::store::iterate::{order, phase1};
    let k = 1 << 12;
    let systems = scaling::inputs(k, |m| {
        let s = houdini_loop(m);
        let o = order(&s).unwrap();
        (s, o)
    });
    scaling::check(
        "the head of a loop entered with k candidate conjuncts",
        k,
        |m| {
            let (s, o) = &systems[&m];
            let head = &phase1(s, o)[0];
            assert_eq!(upper_symbols(head).len(), m.div_ceil(2));
        },
    );
}
