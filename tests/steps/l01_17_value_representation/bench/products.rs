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

/// Words that are each the product of two primes near 2^31, the hardest words for Pollard's
/// rho, `count` of them: `p_(2i) p_(2i+1)` over the primes from `2^31` up, so no two words
/// share a prime.
fn hard_words(count: usize) -> Vec<u64> {
    let primes: Vec<u64> = (1u64 << 31..)
        .filter(|&p| zed_numtheory::is_prime(p))
        .take(2 * count)
        .collect();
    primes.chunks(2).map(|w| w[0] * w[1]).collect()
}

/// The products of `n` and `8n` pairs of words, each word the product of two primes near 2^31:
/// `Rat::mul` factors nothing (plan row KEPT-power-form-print: the primes are found when the
/// value is printed), so a product costs what the product built as digits costs, up to the
/// constant of the kept form's bookkeeping, held below the scaling limit of 10.5, and the work
/// is O(n). When `Rat::mul` factored each word by Pollard's rho, one product cost 854,433 ns
/// against 61 ns built (2026-11-23, Colab).
#[test]
fn a_product_of_two_words_costs_what_a_built_product_costs() {
    let n = 1usize << 12;
    let words = hard_words(2 * 8 * n);
    let rats: Vec<Rat> = words.iter().map(|w| Rat::int(BigInt::from(*w))).collect();
    let products = |m: usize| {
        for pair in rats[..2 * m].chunks(2) {
            let p = pair[0].mul(&pair[1]).expect("memory is given");
            assert!(p.kept().2.is_empty(), "no prime is moved by a product");
        }
    };
    let (kept, ()) = zed_tests::scaling::least_cpu_ns(5, || products(n));
    let (built, ()) = zed_tests::scaling::least_cpu_ns(5, || {
        for pair in words[..2 * n].chunks(2) {
            std::hint::black_box(BigInt::from(pair[0]) * BigInt::from(pair[1]));
        }
    });
    eprintln!(
        "a product of two hard words: {} ns by Rat::mul, {} ns built",
        kept / n as u128,
        built / n as u128
    );
    assert!(
        kept * 2 < built * 21,
        "Rat::mul {kept} ns against {built} ns built, for {n} products"
    );
    check_order("products of n and 8n pairs of hard words", n, 1, products);
}

/// The text of `n` and `8n` products of two hard words ([`hard_words`]), each held as digits:
/// `Rat::integer_text` reduces each coefficient with methods of proved cost (trailing zeros,
/// a least root, `factor` below 2^44), which find no prime here, so each prints its digits,
/// and the work is O(n), a constant per word (plan row KEPT-power-form-print).
#[test]
fn the_text_of_a_product_of_two_words_costs_order_n() {
    let n = 1usize << 11;
    let words = hard_words(2 * 8 * n);
    let products: Vec<Rat> = (words.chunks(2))
        .map(|w| Rat::int(BigInt::from(w[0]) * BigInt::from(w[1])))
        .collect();
    check_order("the text of n and 8n products of hard words", n, 1, |m| {
        for p in &products[..m] {
            let text = p.integer_text();
            assert!(text.bytes().all(|b| b.is_ascii_digit()), "{text}");
        }
    });
}
