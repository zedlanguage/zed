//! Benchmarks of `roots`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// The roots are found in time polynomial in the size of the sparse polynomial: the degree
/// enters by its bits, and the coefficients by theirs.
#[test]
fn roots_scale_in_the_degree_and_in_the_bits() {
    let degrees = scaling::inputs(1 << 12, |n| of_degree(n as u64));
    scaling::check_order("the integer roots of (x^n + 1)(x - 4)", 1 << 12, 1, |n| {
        integer_roots(&degrees[&n], None, None);
    });
    // 256 and 2,048 bits (plan row ROOTS-cubic-bits-bytes). From 512 bits up the work grew as
    // num-bigint's products and quotients: callgrind, 2026-11-22, 14.1M instructions at
    // 2,048 bits and 300.0M at 16,384, 21.3 times, 92% in the chain of derivatives
    // (`chain_roots`), 61% in its evaluations and 22% in num-bigint's `div_floor`. num-bigint
    // 0.4.8 multiplies by long multiplication while the shorter factor, here `x` of `n / 64`
    // words, has at most 32 words (to 2,048 bits), by Karatsuba's method to 256 words (16,384
    // bits) and by Toom-3 past that; it divides by Knuth's algorithm D unless the dividend has
    // over 128 words and the divisor over 64 (tradeoff at the macro `interval_tests` in
    // `zed_kernel::poly::roots`). So from 1,024 to 4,096 bits each product grows by 21 to 64
    // times at 8 times the bits. The products and quotients are now the kernel's (`mul_int`,
    // `div_floor_int`), which keep num-bigint's up to their measured crossovers (`MUL_LEAF`,
    // `TOOM_COST`, `DIV_LEAF`, `DIV_COST`). Measured 2026-11-22 (DynamoRIO, instructions at 8
    // times the bits): 3.9 at 256 bits (3.18M and 12.38M), 8.8 at 512, 16.8 at 1,024, 22.8 at
    // 2,048, 25.3 at 4,096 and 13.2 at 65,536 (2.429G and 32.07G; bytes 385.8M and 2,216.5M,
    // 5.7 times). At 65,536 bits callgrind puts 91% of the instructions in num-bigint's
    // products, 77% of them through the kernel's `mul`. The steps of that search, counted by
    // the reviewers' model of it (cross-review XR-ROOTS-REF round 1, not measured here), all
    // at full precision over the five searches of the chain (two members of each sign, and
    // the root 5):
    //
    //   bits     cuts  Newton steps  bisections  evaluations
    //   256        42            33          51          212
    //   512        47            37          49          227
    //   1,024      52            41          50          245
    //   2,048      57            45          79          291
    //   4,096      62            49          78          307
    //   8,192      67            53          75          321
    //   16,384     72            57          92          355
    //   32,768     77            61          96          376
    //
    // Each of the four wide searches, of the cubic and of its derivative, for either sign,
    // takes about log2 n Newton steps, so `O(M(n) log n)`. Each now takes the guess of a
    // search at doubling precision and three evaluations at full precision after its cuts
    // (plan row ROOTS-doubling-newton, `zed_kernel::poly::roots::doubling`), so `O(M(n))`
    // past the cuts. From 1,024 to 4,096 bits no exact method is under the limit: the products
    // there are of 16 to 256 words, where the cheapest measured product is num-bigint's long
    // multiplication or Karatsuba's method, 27 to 64 times the work at 8 times the words, and
    // the kernel's transform costs more below `MUL_LEAF`, 400 words (`zed_kernel::num::fast`).
    // So, as `a_dense_product_scales` (COMPLEXITY.md), the order is timed where both sizes run
    // on the transform, in `roots_scale_in_the_bits_where_products_are_transforms` (plan row
    // DECISION-roots-bench-regime), and here at 256 bits, a run under 1 ms.
    let cubics = scaling::inputs(256, |bits| of_bits(bits as u64).0);
    scaling::check_order(
        "the integer roots of a cubic whose roots have n bits",
        256,
        1,
        |n| {
            integer_roots(&cubics[&n], None, None);
        },
    );
}

/// A cubic of three seeded random roots of `bits` bits each, the top bit set and the signs
/// drawn: dense coefficients, where those of [`of_bits`] are sparse in their bits, so that no
/// shortcut on the fixture's powers of 2 passes alone (cross-review XR-ROOTS-REF round 1, C1).
fn dense_cubic(bits: u64) -> Sparse {
    let mut rng = zed_tests::seed::Rng::new(0x6375_6269 ^ bits);
    let rs: Vec<BigInt> = (0..3)
        .map(|_| {
            let digits = (0..bits / 32).map(|_| rng.next_u64() as u32).collect();
            let r =
                BigInt::from(num_bigint::BigUint::new(digits)) | (BigInt::from(1u8) << (bits - 1));
            match rng.below_u64(2) {
                0 => r,
                _ => -r,
            }
        })
        .collect();
    expanded(&rs)
}

/// `c x^3 - c r^3` with `c` and `r` seeded random numbers of `bits` bits each: the binomial,
/// whose root is the cube root of the kernel's quotient (plan row ROOTS-binomial-div).
fn dense_binomial(bits: u64) -> Sparse {
    let mut rng = zed_tests::seed::Rng::new(0x6269_6e6f ^ bits);
    let mut wide = || {
        let digits = (0..bits / 32).map(|_| rng.next_u64() as u32).collect();
        BigInt::from(num_bigint::BigUint::new(digits)) | (BigInt::from(1u8) << (bits - 1))
    };
    let (c, r) = (wide(), wide());
    let c0 = -(&c * &r * &r * &r);
    Sparse::new([(0, c0), (3, c)])
}

/// The bits of the roots at size n of the benches
/// `roots_scale_in_the_bits_where_products_are_transforms`, `dense_roots_scale_in_the_bits` and
/// `a_binomial_root_scales_in_the_bits`, timed at n and 8n:
/// 262,144 and 2,097,152 bits, 4,096 and 32,768 words, past the measured crossovers of every
/// product and of the quotients at full precision (plan rows ROOTS-doubling-newton and
/// DECISION-roots-bench-regime, after the precedent of `a_dense_product_scales`, timed at 8,192
/// and 65,536 words; why 1,024 to 4,096 bits cannot pass at
/// `roots_scale_in_the_degree_and_in_the_bits`). Every product of the search at full precision
/// is of factors past `MUL_LEAF`, 400 words, so the kernel's transform, `O(n log n)`. The
/// quotients go to num-bigint's division, Burnikel and Ziegler's, whose work grows 2.87 times
/// per doubling, up to the switch of `zed_kernel::num::fast` (`DIV_LEAF`, `DIV_COST`), and
/// past it to the division by a reciprocal, `O(M(n))`.
///
/// Why a ratio taken across that switch is not a fault of the order: where the switch sits at
/// the measured crossover, the work at `n` is the less of the two methods', so the ratio at 8n
/// is at least the reciprocal's own, `reciprocal(8n) / reciprocal(n)`, and larger only because
/// the small size took the faster method. That holds only where the switch is at the
/// crossover. Measured in instructions (`crossover div-leaf`, DynamoRIO's `zed_icount`, run
/// h5-req30 on snapshot 25e53c9b5, 2026-11-23): for `2w` by `w`, the shape of the carry bounds
/// (`bounds`, a coefficient of `2n` bits by a point of `n`), num-bigint does less work up to
/// 3090 words (3192 on 2026-11-12), but `DIV_COST` as built (9.1) takes it at 2048, 2896 and
/// 5793 words and the reciprocal at 4096 and from 8192, up to 1.329 times the less work (at
/// 5793); for a quotient of a quarter of the divisor's words, the shape of a Newton step at
/// the top level of `doubling`, the crossover is 861 words of quotient (919 on 2026-11-12) and
/// the build takes num-bigint at 1448 (a divisor of 5792 words), 1.123 times the less work, and
/// the reciprocal at a divisor of 4096 words. So `2w` by `w` at `w` = 4,096 words, n here,
/// takes the reciprocal, as at 32,768 words, 8n; a divisor of a few words more than 4,096 is
/// inferred, not measured, to take num-bigint at n, as at 5793 words, and which divisors of
/// each level of the search have which width was not measured. At 131,072 bits, 2048 words,
/// both shapes were below their crossovers and at 1,048,576 past them, so that pair measured
/// the change of method, not the order: 12.974 times the instructions at 8n with the old
/// search (h5-req23), then 11.197 after the Newton step at doubling precision (h5-req26), the
/// quotients 8.40 times and the rest 4.55 times from 131,072 to 524,288 bits (Callgrind,
/// h5-req26).
///
/// The search at doubling precision makes the whole `O(M(n))` past the cuts, and the cuts are
/// `O(log n)` evaluations of `O(M(n))` each at powers of 2. The lower levels of `doubling`
/// divide numbers of half the bits of the level above, so some are below the crossovers at
/// every size: from 262,144 to 1,048,576 bits the division by a reciprocal went from 3 calls
/// to 10, 7.70 times its work, but 2.31 times per call, and the whole 4.52 times (run
/// h5-req27, callgrind); that each doubling of n adds about one more call per doubling level
/// is inferred from the levels' sizes, not measured per level. Measured at these sizes
/// (h5-req27): 9.445, 9.065 and 9.026 times the instructions at 8n for the three benches,
/// 3.0 s, 7.6 s and 1.6 s a piece; with the search at doubling precision turned off in the
/// production build, the first takes 10.588 and fails.
const TRANSFORM_BITS: usize = 262_144;

/// The integer roots of the cubic of [`of_bits`], whose roots have [`TRANSFORM_BITS`] and 8
/// times as many bits: the sizes and why, there.
#[test]
fn roots_scale_in_the_bits_where_products_are_transforms() {
    scaling::check_inputs(
        "the integer roots of a cubic whose roots have n bits",
        TRANSFORM_BITS,
        |bits| of_bits(bits as u64).0,
        |f| {
            integer_roots(f, None, None);
        },
    );
}

/// The integer roots of the dense cubic of [`dense_cubic`], at the sizes of
/// [`TRANSFORM_BITS`].
#[test]
fn dense_roots_scale_in_the_bits() {
    scaling::check_inputs(
        "the integer roots of a dense cubic of three random roots of n bits",
        TRANSFORM_BITS,
        |bits| dense_cubic(bits as u64),
        |f| {
            integer_roots(f, None, None);
        },
    );
}

/// The integer root of the binomial of [`dense_binomial`], at the sizes of
/// [`TRANSFORM_BITS`].
#[test]
fn a_binomial_root_scales_in_the_bits() {
    scaling::check_inputs(
        "the integer root of c x^3 - c r^3, c and r of n bits",
        TRANSFORM_BITS,
        |bits| dense_binomial(bits as u64),
        |f| {
            integer_roots(f, None, None);
        },
    );
}

/// In the number of terms the method is linear (`integer_roots`: each interval of its branch
/// and bound costs O(t) products of numbers of the bits of the 1-norm, and the intervals kept
/// lie about the roots), for a root at 4, which the cuts of the interval reach, and for one at
/// `2^40`, which Newton's method reaches. The method it replaced, a chain of `t` derivatives
/// of up to `t` terms each, was of order `t^3`: 80.5 times the work at 8 times the terms.
///
/// For the root at `2^40` the work is `t log t` (author decision P300: an O(n log n) method is
/// read against its predicted ratio): the branch and bound spends `2 log2(t) + 8` units on `t`
/// coefficients, measured at every `t` from 32 to 131,072, each unit O(t) operations on
/// numbers of one or two words (`zed_kernel::poly::roots::integer_roots`, where the count is
/// explained and proved at the test `the_count_of_units_on_far_roots_is_proved`). So
/// `T(t) = a t (log2 t + 4)`, whose ratio from 2,048 to 16,384 coefficients (1,024 and 8,192
/// here, two coefficients each) is `8 (14 + 4) / (11 + 4) = 9.60`. Measured 2026-11-20
/// (BENCH-over-nlogn-prediction item 15): 9.30 times the instructions and 9.16 times the
/// bytes; 30 and 36 units.
#[test]
fn roots_are_linear_in_the_number_of_terms() {
    let large = BigInt::from(1u8) << 40u32;
    let small = scaling::inputs(1_024, |n| of_terms(n, &BigInt::from(4)));
    scaling::check_order(
        "the integer roots of a polynomial of n terms",
        1_024,
        1,
        |n| {
            integer_roots(&small[&n], None, None);
        },
    );
    let far = scaling::inputs(1_024, |n| of_terms(n, &large));
    scaling::check_order(
        "the integer roots of a polynomial of n terms with a root at 2^40",
        1_024,
        1,
        |n| {
            integer_roots(&far[&n], None, None);
        },
    );
}

/// The families on which the branch and bound alone took about `c^(1/2)` and `c^(2/3)`
/// intervals for roots near `c = 2^bits` (plan row ROOTS-interval-bound): with the switch to
/// the chain after `chain_ends(t)` units, at 256 and 2,048 bits each is close to linear in the
/// bits, where the branch and bound alone would take past 2^128 intervals at the small size.
#[test]
fn roots_of_families_that_defeat_the_cuts_scale_in_the_bits() {
    let cubics = scaling::inputs(256, |bits| of_flat_cubic(bits as u64));
    scaling::check_order(
        "the integer roots of an increasing cubic with its real root near 2^n",
        256,
        1,
        |n| {
            integer_roots(&cubics[&n], None, None);
        },
    );
    let clusters = scaling::inputs(256, |bits| expanded(&cluster(bits as u64)));
    scaling::check_order(
        "the integer roots of four roots at 2^n..=2^n + 3",
        256,
        1,
        |n| {
            integer_roots(&clusters[&n], None, None);
        },
    );
}
