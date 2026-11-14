//! Benchmarks of `roots`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// The roots are found in time polynomial in the size of the sparse polynomial: the degree
/// enters by its bits, and the coefficients by theirs.
#[test]
fn roots_scale_in_the_degree_and_in_the_bits() {
    for n in [1000, 8001] {
        let expected: Vec<BigInt> = match n % 2 {
            0 => vec![BigInt::from(4)],
            _ => vec![BigInt::from(-1), BigInt::from(4)],
        };
        assert_eq!(
            integer_roots(&of_degree(n), None, None),
            Roots::Listed(expected)
        );
    }
    let degrees = scaling::inputs(1 << 12, |n| of_degree(n as u64));
    scaling::check_order("the integer roots of (x^n + 1)(x - 4)", 1 << 12, 1, |n| {
        integer_roots(&degrees[&n], None, None);
    });
    for bits in [64, 512] {
        let (f, a, b) = of_bits(bits);
        let expected = vec![b, BigInt::from(5), a];
        assert_eq!(integer_roots(&f, None, None), Roots::Listed(expected));
    }
    let cubics = scaling::inputs(64, |bits| of_bits(bits as u64).0);
    scaling::check_order(
        "the integer roots of a cubic whose roots have n bits",
        64,
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
#[test]
fn roots_are_linear_in_the_number_of_terms() {
    let large = BigInt::from(1u8) << 40u32;
    for r in [BigInt::from(4), large.clone()] {
        for n in [8, 64] {
            assert_eq!(
                integer_roots(&of_terms(n, &r), None, None),
                Roots::Listed(vec![r.clone()])
            );
        }
    }
    let small = scaling::inputs(16, |n| of_terms(n, &BigInt::from(4)));
    scaling::check_order("the integer roots of a polynomial of n terms", 16, 1, |n| {
        integer_roots(&small[&n], None, None);
    });
    let far = scaling::inputs(16, |n| of_terms(n, &large));
    scaling::check_order(
        "the integer roots of a polynomial of n terms with a root at 2^40",
        16,
        1,
        |n| {
            integer_roots(&far[&n], None, None);
        },
    );
}
