//! Item NUM-subquad: the products, quotients, remainders, gcds and decimal texts of wide
//! numbers cost O(n log n) to O(n log^2 n) in their width (`zed_kernel::num::fast`), and a
//! factor or divisor with few nonzero words, such as `2^s + 1`, costs O(n). The costs are
//! checked by `bench::subquadratic`; the answers here, against num-bigint, at widths where the
//! same methods are taken.

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Zero};
use zed_kernel::Rat;

/// A number of `words` 64-bit words drawn from `seed` (splitmix64), its top word not zero.
pub(crate) fn random(words: usize, seed: u64) -> BigInt {
    let mut x = seed;
    let mut halves: Vec<u32> = (0..words)
        .flat_map(|_| {
            x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            let z = z ^ (z >> 31);
            [z as u32, (z >> 32) as u32]
        })
        .collect();
    if let Some(top) = halves.last_mut() {
        *top |= 1 << 31;
    }
    BigInt::from(BigUint::new(halves))
}

/// `2^(64 words) + 1`: two nonzero words.
pub(crate) fn sparse(words: usize) -> BigInt {
    (BigInt::one() << (64 * words)) + 1u32
}

pub(crate) fn int(n: BigInt) -> Rat {
    Rat::int(n)
}

/// The integer of `r`, an integer.
fn whole(r: &Rat) -> &BigInt {
    r.integer_factors().0
}

/// What the benchmarks of `bench::subquadratic` time, each against num-bigint, with random
/// operands from a new seed each run:
/// - `(2^(64n) + 1) x` and `(2^(64n) + 1)(2^(64n) + 3)` at n = 2^16 words: rows over the
///   sparse factor's two nonzero words;
/// - a number of 2n words `div` and `mod` `2^(64n) + 1` at n = 2^16: long division over the
///   divisor's two words;
/// - a number of 2n words `div` and `mod` one of n words at n = 4,096: Newton's reciprocal;
/// - the decimal text of a number of 2^14 words, above `PRINT_WHOLE` (7,845 words), so written
///   by halves; and of `2^(64n) + 1`, `2^(64n)` less 1 and 0;
/// - a product of two dense numbers of 8,192 words: transforms modulo three primes.
///
/// The widths are those the benchmarks ran at before they moved, the text's a quarter of it,
/// since num-bigint's own text is slow there.
#[test]
fn wide_products_quotients_and_texts_agree_with_num_bigint() {
    let seed = super::seed("ZED_SUBQUADRATIC_SEED");
    let n = 1 << 16;
    let x = random(n, seed);
    let s = int(sparse(n));
    let product = s.mul(&int(x.clone())).expect("memory is given");
    assert_eq!(whole(&product), &(sparse(n) * &x), "seed {seed}");
    let t = int(sparse(n) + 2u32);
    let product = s.mul(&t).expect("memory is given");
    assert_eq!(
        whole(&product),
        &(sparse(n) * (sparse(n) + 2u32)),
        "seed {seed}"
    );

    let a = random(2 * n, seed ^ 1);
    let (q, r) = a.div_rem(&sparse(n));
    let (a, d) = (int(a), int(sparse(n)));
    let q_got = a.div_euclid(&d).expect("memory is given");
    let r_got = a.rem_euclid(&d).expect("memory is given");
    assert_eq!(whole(&q_got), &q, "seed {seed}");
    assert_eq!(whole(&r_got), &r, "seed {seed}");

    let n = 1 << 12;
    let (a, d) = (random(2 * n, seed ^ 2), random(n, seed ^ 3));
    let (q, r) = a.div_rem(&d);
    let (a, d) = (int(a), int(d));
    let q_got = a.div_euclid(&d).expect("memory is given");
    let r_got = a.rem_euclid(&d).expect("memory is given");
    assert_eq!(whole(&q_got), &q, "seed {seed}");
    assert_eq!(whole(&r_got), &r, "seed {seed}");

    let n = 1 << 14;
    let x = random(n, seed ^ 4);
    assert_eq!(
        int(x.clone()).numer_text().unwrap(),
        x.to_string(),
        "seed {seed}"
    );
    assert_eq!(int(sparse(n)).numer_text().unwrap(), sparse(n).to_string());
    assert_eq!(
        int(sparse(n) - 1u32).numer_text().unwrap(),
        (sparse(n) - 1u32).to_string()
    );
    assert_eq!(int(BigInt::zero()).numer_text().unwrap(), "0");

    let n = 1 << 13;
    let (x, y) = (random(n, seed ^ 5), random(n, seed ^ 6));
    let product = int(x.clone())
        .mul(&int(y.clone()))
        .expect("memory is given");
    assert_eq!(whole(&product), &(x * y), "seed {seed}");
}

/// Item BIGINT-fast-mul: `zed_kernel::num::mul_uint`, `mul_int` and `pow_uint` give
/// num-bigint's products on both sides of each crossover (512 words, and the computed costs
/// above it, where num-bigint's product, rows over nonzero words or the transforms are taken):
/// random factors from a new seed each run, all-ones words, powers of two and their
/// successors, one word by a number of 2^17 words, zero, and every pair of signs.
#[test]
fn products_agree_with_num_bigint_across_the_crossovers() {
    use zed_kernel::num::{mul_int, mul_uint, pow_uint};
    let seed = super::seed("ZED_CROSSOVER_PRODUCTS_SEED");
    let ones = |w: usize| (BigUint::one() << (64 * w)) - 1u32;
    let two = |w: usize| BigUint::one() << (64 * w - 1);
    let forms = |w: usize, seed: u64| {
        [
            random(w, seed).into_parts().1,
            ones(w),
            two(w),
            two(w) + 1u32,
        ]
    };
    let shapes = [
        (1, 1),
        (1, 1 << 17),
        (511, 511),
        (512, 512),
        (513, 513),
        (513, 70_000),
        (1024, 1024),
        (1536, 1536),
        (2048, 2048),
        (2049, 2049),
        (2560, 2560),
        (3000, 9000),
        (4097, 4097),
    ];
    let mut checked = 0;
    for (k, &(s, l)) in shapes.iter().enumerate() {
        let k = k as u64;
        for x in forms(s, seed.wrapping_add(2 * k)) {
            for y in forms(l, seed.wrapping_add(2 * k + 1)) {
                let want = &x * &y;
                assert_eq!(mul_uint(&x, &y), want, "{s} by {l} words, seed {seed}");
                assert_eq!(mul_uint(&y, &x), want, "{l} by {s} words, seed {seed}");
                checked += 2;
            }
        }
    }
    assert_eq!(checked, 13 * 4 * 4 * 2);
    let x = random(3000, seed.wrapping_add(40));
    let y = random(5000, seed.wrapping_add(41));
    for (a, b) in [(&x, &y), (&-&x, &y), (&x, &-&y), (&-&x, &-&y)] {
        assert_eq!(mul_int(a, b), a * b, "seed {seed}");
    }
    let zero = BigUint::zero();
    assert_eq!(mul_uint(&zero, &ones(5000)), zero);
    assert_eq!(mul_int(&BigInt::zero(), &-&x), BigInt::zero());
    let base = random(700, seed.wrapping_add(42)).into_parts().1;
    assert_eq!(
        pow_uint(&base, 5),
        num_traits::Pow::pow(&base, 5u32),
        "seed {seed}"
    );
    assert_eq!(pow_uint(&base, 0), BigUint::one());
}
