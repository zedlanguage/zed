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
    // 256 and 2,048 bits. From 512 bits up the first runs allocate more than 10.5 times the
    // bytes at 8 times the bits: 11.6 times from 512, 17.2 from 1,024 and 20.1 from 2,048, with
    // the instructions 6.2, 7.0 and 7.9 times (TEST-bench-move-l0139; plan row
    // ROOTS-cubic-bits-bytes). Under 1 ms a run at this size.
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
/// explained; its proof is plan row PROOF-roots-terms-depth). So `T(t) = a t (log2 t + 4)`,
/// whose ratio from 2,048 to 16,384 coefficients (1,024 and 8,192 here, two coefficients each)
/// is `8 (14 + 4) / (11 + 4) = 9.60`. Measured 2026-11-20 (BENCH-over-nlogn-prediction item 15):
/// 9.30 times the instructions and 9.16 times the bytes; 30 and 36 units.
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
