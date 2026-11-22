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
    // takes about log2 n Newton steps, so `O(M(n) log n)`. Only 256 bits is under the limit, a
    // run under 1 ms; a search at doubling precision is open with the row.
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
