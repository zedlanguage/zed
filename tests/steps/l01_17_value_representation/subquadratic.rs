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
    // Until KERNEL-div-newton the narrow Newton steps used num-bigint's products, so a run of
    // few steps by transforms counted the change of method as growth, and the test needed
    // n = 32,768 (10.05 times against 10.6, 2026-11-09). Each step is now a cyclic product by
    // transforms down to `RECIP_LEAF` bits: 9.6 times from 4,096 words against 11.0, in 0.3 s,
    // and 63.8 times with long division forced in place of the reciprocal (2026-11-09, load 18).
    let n = 1 << 12;
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
/// log^2 n), and two exact quotients by it (COMPLEXITY.md C31), held to the limit of 13 every
/// scaling test meets. It passes, 11.4 times the work against that order's limit of the day,
/// 13.3 (2026-11-12, RADIX-depth), and 11.4 (2026-11-13); it failed at 16.4 (2026-11-09), as
/// the transforms were dear.
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
/// built once, O(n log^2 n) (COMPLEXITY.md C31), held to the limit of 13 every scaling test
/// meets; 10.2 times (2026-11-13). Both sizes are
/// above `PRINT_WHOLE`, 7845 words, below which num-bigint's printing, faster there, writes the
/// text (`zed_kernel::num::to_decimal`). When that threshold was 60,000 words, the smaller size
/// was num-bigint's, and the change of method made 18.5 times the work (2026-11-08,
/// COMPLEXITY.md K81).
#[test]
fn printing_a_wide_number_scales() {
    let n = 1 << 16;
    let inputs = built(n, |m| int(random(m, 8)));
    assert_eq!(
        at(&inputs, n, n).numer_text().unwrap(),
        random(n, 8).to_string()
    );
    assert_eq!(int(sparse(n)).numer_text().unwrap(), sparse(n).to_string());
    assert_eq!(
        int(sparse(n) - 1u32).numer_text().unwrap(),
        (sparse(n) - 1u32).to_string()
    );
    assert_eq!(int(BigInt::zero()).numer_text().unwrap(), "0");
    check("the decimal text of a number of n words", n, |m| {
        assert!(!at(&inputs, n, m).numer_text().unwrap().is_empty());
    });
}

/// Item BIGINT-fast-mul: `zed_kernel::num::mul_uint`, `mul_int` and `pow_uint` give
/// num-bigint's products on both sides of each crossover (512 words, and the computed costs
/// above it, where num-bigint's product, rows over nonzero words or the transforms are taken):
/// random factors, all-ones words, powers of two and their successors, one word by a number of
/// 2^17 words, zero, and every pair of signs.
#[test]
fn products_agree_with_num_bigint_across_the_crossovers() {
    use zed_kernel::num::{mul_int, mul_uint, pow_uint};
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
        for x in forms(s, 2 * k as u64) {
            for y in forms(l, 2 * k as u64 + 1) {
                let want = &x * &y;
                assert_eq!(mul_uint(&x, &y), want, "{s} by {l} words");
                assert_eq!(mul_uint(&y, &x), want, "{l} by {s} words");
                checked += 2;
            }
        }
    }
    assert_eq!(checked, 13 * 4 * 4 * 2);
    let x = random(3000, 40);
    let y = random(5000, 41);
    for (a, b) in [(&x, &y), (&-&x, &y), (&x, &-&y), (&-&x, &-&y)] {
        assert_eq!(mul_int(a, b), a * b);
    }
    let zero = BigUint::zero();
    assert_eq!(mul_uint(&zero, &ones(5000)), zero);
    assert_eq!(mul_int(&BigInt::zero(), &-&x), BigInt::zero());
    let base = random(700, 42).into_parts().1;
    assert_eq!(pow_uint(&base, 5), num_traits::Pow::pow(&base, 5u32));
    assert_eq!(pow_uint(&base, 0), BigUint::one());
}

/// A product of two dense numbers of n words, by `Rat::mul` and so `zed_kernel::num::mul_int`:
/// transforms modulo three primes, O(n log n), where num-bigint's Toom-3 is O(n^1.465).
#[test]
fn a_dense_product_scales() {
    let n = 1 << 13;
    let inputs = built(n, |m| (int(random(m, 50)), int(random(m, 51))));
    let (x, y) = at(&inputs, n, n);
    assert_eq!(
        x.mul(y).expect("memory is given").integer_factors().0,
        &(random(n, 50) * random(n, 51))
    );
    check("a product of two dense numbers of n words", n, |m| {
        let (x, y) = at(&inputs, n, m);
        assert!(!x.mul(y).expect("memory is given").is_zero());
    });
}
