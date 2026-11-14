//! Item NUM-subquad at the rule of low complexity. Each family runs at n and 8n words, its
//! inputs built before it is timed. The answers are checked against num-bigint by
//! `wide_products_quotients_and_texts_agree_with_num_bigint` in `subquadratic.rs`.

use zed_tests::scaling::{check, inputs};

use super::super::subquadratic::{int, random, sparse};

/// `(2^(64n) + 1) x` for a dense `x` of n words, and `(2^(64n) + 1)(2^(64n) + 3)`: rows over
/// the sparse factor's two nonzero words, O(n), where the transforms are O(n log n).
#[test]
fn a_sparse_product_scales() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 63 ns a
    // word, 1x 33 ms, 1.5 GB at 8n, which holds n down.
    let n = 1 << 19;
    let numbers = inputs(n, |m| {
        let s = int(sparse(m));
        (s.clone(), int(random(m, 1)), int(sparse(m) + 2u32))
    });
    check(
        "a sparse factor of n words times a dense one and a sparse one",
        n,
        |m| {
            let (s, x, t) = &numbers[&m];
            assert!(!s.mul(x).expect("memory is given").is_zero());
            assert!(!s.mul(t).expect("memory is given").is_zero());
        },
    );
}

/// A dense number of 2n words divided by `2^(64n) + 1`, `div` and `mod`: long division over the
/// divisor's two nonzero words, O(n), where the reciprocal is O(n log n).
#[test]
fn a_sparse_division_scales() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 140 ns a
    // word, 1x 75 ms, 2.7 GB at 8n, which holds n down.
    let n = 1 << 19;
    let numbers = inputs(n, |m| (int(random(2 * m, 2)), int(sparse(m))));
    check("a number of 2n words div and mod 2^(64n) + 1", n, |m| {
        let (a, d) = &numbers[&m];
        assert!(!a.div_euclid(d).expect("memory is given").is_zero());
        assert!(!a.rem_euclid(d).expect("memory is given").is_zero());
    });
}

/// A dense number of 2n words `div` and `mod` a dense one of n words: Newton's reciprocal and
/// two products, O(n log n).
#[test]
fn dividing_a_wide_number_scales() {
    // Until KERNEL-div-newton the narrow Newton steps used num-bigint's products, so a run of
    // few steps by transforms counted the change of method as growth, and the test needed
    // n = 32,768 (10.05 times against 10.6, 2026-11-09). Each step is now a cyclic product by
    // transforms down to `RECIP_LEAF` bits: 9.6 times from 4,096 words against 11.0, in 0.3 s,
    // and 63.8 times with long division forced in place of the reciprocal (2026-11-09, load 18).
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 2.1 µs a
    // word, 1x 0.14 s, 1.0 GB at 8n. At 2^17 words, 1x 0.33 s, the first run at 8n allocated
    // 11.9 times the bytes of the first at n, over the limit of 10.5, so n stays at 2^16.
    let n = 1 << 16;
    let numbers = inputs(n, |m| (int(random(2 * m, 3)), int(random(m, 4))));
    check("a number of 2n words div and mod one of n words", n, |m| {
        let (a, d) = &numbers[&m];
        assert!(!a.div_euclid(d).expect("memory is given").is_zero());
        assert!(!a.rem_euclid(d).expect("memory is given").is_zero());
    });
}

/// The decimal text of a dense number of n words: by halves, each power of ten's reciprocal
/// built once, O(n log^2 n) (COMPLEXITY.md C31), held to the limit of 10.5 every scaling test
/// meets; 10.2 times at 2^16 words (2026-11-13). Both sizes are above `PRINT_WHOLE`, 7845
/// words, below which num-bigint's printing, faster there, writes the text
/// (`zed_kernel::num::to_decimal`). When that threshold was 60,000 words, the smaller size was
/// num-bigint's, and the change of method made 18.5 times the work (2026-11-08, COMPLEXITY.md
/// K81).
#[test]
fn printing_a_wide_number_scales() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 3.1 µs a
    // word, 1x 0.61 s, 3.0 GB at 8n, ratio 10.0, as at 2^18, where the test took 22 s.
    let n = 3 << 16;
    let numbers = inputs(n, |m| int(random(m, 8)));
    check("the decimal text of a number of n words", n, |m| {
        assert!(!numbers[&m].numer_text().unwrap().is_empty());
    });
}

/// A product of two dense numbers of n words, by `Rat::mul` and so `zed_kernel::num::mul_int`:
/// transforms modulo three primes, O(n log n), where num-bigint's Toom-3 is O(n^1.465).
#[test]
fn a_dense_product_scales() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 0.48 µs a
    // word, 1x 0.37 s, 1.8 GB at 8n; at 2^20 words the test took 16.5 s.
    let n = 3 << 18;
    let numbers = inputs(n, |m| (int(random(m, 50)), int(random(m, 51))));
    check("a product of two dense numbers of n words", n, |m| {
        let (x, y) = &numbers[&m];
        assert!(!x.mul(y).expect("memory is given").is_zero());
    });
}
