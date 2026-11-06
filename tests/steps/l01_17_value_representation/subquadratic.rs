//! Item NUM-subquad: the products, quotients, remainders, gcds and decimal texts of wide
//! numbers cost O(n log n) to O(n log^2 n) in their width (`zed_kernel::num::fast`), and a
//! factor or divisor with few nonzero words, such as `2^s + 1`, costs O(n). Each family runs at
//! n and 8n words, its inputs built before it is timed.

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Zero};
use zed_kernel::Rat;
use zed_tests::scaling::check;

/// A number of `words` 64-bit words drawn from `seed` (splitmix64), its top word not zero.
fn random(words: usize, seed: u64) -> BigInt {
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
fn sparse(words: usize) -> BigInt {
    (BigInt::one() << (64 * words)) + 1u32
}

fn int(n: BigInt) -> Rat {
    Rat::int(n)
}

/// The inputs `build(n)` and `build(8n)`, built before anything is timed.
fn built<T>(n: usize, build: impl Fn(usize) -> T) -> [T; 2] {
    [build(n), build(8 * n)]
}

/// The input of [`built`] for size `m`, `n` or `8n`.
fn at<T>(inputs: &[T; 2], n: usize, m: usize) -> &T {
    &inputs[usize::from(m != n)]
}

/// `(2^(64n) + 1) x` for a dense `x` of n words, and `(2^(64n) + 1)(2^(64n) + 3)`: rows over
/// the sparse factor's two nonzero words, O(n), where the transforms are O(n log n).
#[test]
fn a_sparse_product_scales() {
    let n = 1 << 16;
    let inputs = built(n, |m| {
        let s = int(sparse(m));
        (s.clone(), int(random(m, 1)), int(sparse(m) + 2u32))
    });
    let (s, x, t) = at(&inputs, n, n);
    assert_eq!(
        s.mul(x).expect("memory is given").integer_factors().0,
        &(sparse(n) * random(n, 1))
    );
    assert_eq!(
        s.mul(t).expect("memory is given").integer_factors().0,
        &(sparse(n) * (sparse(n) + 2u32))
    );
    check(
        "a sparse factor of n words times a dense one and a sparse one",
        n,
        |m| {
            let (s, x, t) = at(&inputs, n, m);
            assert!(!s.mul(x).expect("memory is given").is_zero());
            assert!(!s.mul(t).expect("memory is given").is_zero());
        },
    );
}

/// A dense number of 2n words divided by `2^(64n) + 1`, `div` and `mod`: long division over the
/// divisor's two nonzero words, O(n), where the reciprocal is O(n log n).
#[test]
fn a_sparse_division_scales() {
    let n = 1 << 16;
    let inputs = built(n, |m| (int(random(2 * m, 2)), int(sparse(m))));
    let (a, d) = at(&inputs, n, n);
    let (q, r) = random(2 * n, 2).div_rem(&sparse(n));
    let q_got = a.div_euclid(d).expect("memory is given");
    let r_got = a.rem_euclid(d).expect("memory is given");
    assert_eq!(q_got.integer_factors().0, &q);
    assert_eq!(r_got.integer_factors().0, &r);
    check("a number of 2n words div and mod 2^(64n) + 1", n, |m| {
        let (a, d) = at(&inputs, n, m);
        assert!(!a.div_euclid(d).expect("memory is given").is_zero());
        assert!(!a.rem_euclid(d).expect("memory is given").is_zero());
    });
}

/// A dense number of 2n words `div` and `mod` a dense one of n words: Newton's reciprocal and
/// two products, O(n log n).
#[test]
fn dividing_a_wide_number_scales() {
    let n = 1 << 13;
    let inputs = built(n, |m| (int(random(2 * m, 3)), int(random(m, 4))));
    let (a, d) = at(&inputs, n, n);
    let (q, r) = random(2 * n, 3).div_rem(&random(n, 4));
    assert_eq!(
        a.div_euclid(d)
            .expect("memory is given")
            .integer_factors()
            .0,
        &q
    );
    assert_eq!(
        a.rem_euclid(d)
            .expect("memory is given")
            .integer_factors()
            .0,
        &r
    );
    check("a number of 2n words div and mod one of n words", n, |m| {
        let (a, d) = at(&inputs, n, m);
        assert!(!a.div_euclid(d).expect("memory is given").is_zero());
        assert!(!a.rem_euclid(d).expect("memory is given").is_zero());
    });
}

/// `(a c) / (b c)` reduced to lowest terms, `a`, `b` and `c` of n/2 words: the half gcd, O(n
/// log^2 n), and two exact quotients by it.
#[test]
fn a_gcd_of_wide_numbers_scales() {
    let n = 1 << 13;
    let inputs = built(n, |m| {
        let c = random(m / 2, 5);
        (random(m / 2, 6) * &c, random(m / 2, 7) * &c)
    });
    let (num, den) = at(&inputs, n, n);
    let r = Rat::new(num.clone(), den.clone()).expect("not zero");
    let g = num.gcd(den);
    assert!(g.bits() >= 64 * (n as u64 / 2 - 1));
    assert_eq!(r, Rat::new(num / &g, den / &g).expect("not zero"));
    check(
        "(a c) / (b c) in lowest terms, a, b and c of n/2 words",
        n,
        |m| {
            let (num, den) = at(&inputs, n, m);
            assert!(
                !Rat::new(num.clone(), den.clone())
                    .expect("not zero")
                    .is_zero()
            );
        },
    );
}

/// The decimal text of a dense number of n words: by halves, each power of ten's reciprocal
/// built once, O(n log^2 n).
#[test]
fn printing_a_wide_number_scales() {
    let n = 1 << 14;
    let inputs = built(n, |m| int(random(m, 8)));
    assert_eq!(at(&inputs, n, n).numer_text(), random(n, 8).to_string());
    assert_eq!(int(sparse(n)).numer_text(), sparse(n).to_string());
    assert_eq!(
        int(sparse(n) - 1u32).numer_text(),
        (sparse(n) - 1u32).to_string()
    );
    assert_eq!(int(BigInt::zero()).numer_text(), "0");
    check("the decimal text of a number of n words", n, |m| {
        assert!(!at(&inputs, n, m).numer_text().is_empty());
    });
}
