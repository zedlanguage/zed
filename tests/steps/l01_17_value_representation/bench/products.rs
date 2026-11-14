//! Item RAT-checked at the rule of low complexity: a product or quotient by a word. The answers
//! are checked exactly at a small width by `a_product_or_quotient_by_a_word_is_exact` in
//! `products.rs`.

use num_bigint::BigInt;
use num_traits::One;
use zed_kernel::Rat;
use zed_tests::scaling::{check_order, inputs};

use super::super::products::above;

/// `(2^n + 1) * 3`, `(2^n + 1)/3 * 1/3` and `(2^n + 1) / 3` at n and 8n bits: a product or
/// quotient by a word asks for its memory and builds the result in O(n), the gcd of the
/// rationals by one division by the word.
#[test]
fn a_product_or_quotient_by_a_word_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 0.25 ns a
    // bit, 1x 17 ms, 3.0 GB at 8n, which holds n down.
    let n = 1usize << 26;
    let numbers = inputs(n, |m| {
        let a = above(m as u64);
        let third = Rat::new(a.clone(), BigInt::from(3)).expect("3 is not zero");
        (Rat::int(a), third)
    });
    let three = Rat::int(BigInt::from(3));
    let a_third = Rat::new(BigInt::one(), BigInt::from(3)).expect("3 is not zero");
    check_order(
        "(2^n + 1) * 3, (2^n + 1)/3 * 1/3 and (2^n + 1) / 3",
        n,
        1,
        |m| {
            let (wide, third) = &numbers[&m];
            assert!(!wide.mul(&three).expect("memory is given").is_zero());
            assert!(!third.mul(&a_third).expect("memory is given").is_zero());
            let q = wide.div(&three).expect("memory is given");
            assert!(q.is_some_and(|q| !q.is_zero()));
        },
    );
}
