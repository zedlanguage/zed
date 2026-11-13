//! The choice between the dense and the sparse product of `Poly::mul` (POLY-crossover-bench),
//! at the constants `crossover poly-*` measured: the shapes on which the earlier choice, by
//! the charges with unit constants, took the method that runs up to 9.6 and 2.8 times the
//! instructions, and the chosen product's growth with its terms.

use num_bigint::BigInt;
use zed_kernel::poly::crossover::{Sum, dense, sparse, takes_dense};
use zed_tests::scaling;

/// The sum of `c` times `2^60` plus the index at each index of `indices`: coefficients of one
/// full word for `c` up to 7, and differing, so that no product cancels.
fn sum(indices: impl IntoIterator<Item = u128>, c: i64) -> Sum {
    Sum::new(
        indices
            .into_iter()
            .map(|k| (k, BigInt::from(c) * ((BigInt::from(1) << 60) + k)))
            .collect(),
    )
}

/// The sum of 2 terms of coefficients of `words` 64-bit words.
fn wide(words: usize, c: i64) -> Sum {
    let big = (BigInt::from(1) << (64 * words - 1)) + c;
    Sum::new(vec![(0, big.clone()), (1, -big)])
}

#[test]
fn few_dense_terms_take_the_dense_product() {
    // Univariate sums of one-word coefficients: the dense product does fewer instructions from
    // 5 terms each; the earlier choice took the sparse product up to 45, 9.6 times the work.
    for t in [8, 16, 32] {
        let (a, b) = (sum(0..t, 3), sum(0..t, -5));
        assert!(takes_dense(&a, &b), "{t} terms");
        assert_eq!(dense(&a, &b), sparse(&a, &b), "{t} terms");
    }
}

#[test]
fn two_wide_terms_take_the_sparse_product() {
    // 2 terms each: the sparse product does fewer instructions at every width measured, 1 to
    // 1024 words; the earlier choice took the dense product from 11 words, up to 2.8 times.
    for words in [16, 128, 1024] {
        let (a, b) = (wide(words, 3), wide(words, 7));
        assert!(!takes_dense(&a, &b), "{words} words");
        assert_eq!(dense(&a, &b), sparse(&a, &b), "{words} words");
    }
}

#[test]
fn the_chosen_product_of_n_dense_terms() {
    let ins = scaling::inputs(1000, |n| (sum(0..n as u128, 3), sum(0..n as u128, -5)));
    scaling::check(
        "the chosen product of two univariate sums of n terms",
        1000,
        |n| {
            let (a, b) = &ins[&n];
            let product = match takes_dense(a, b) {
                true => dense(a, b),
                false => sparse(a, b),
            };
            assert_eq!(product.len(), 2 * n - 1);
        },
    );
}
