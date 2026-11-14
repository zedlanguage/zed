//! The crossovers of `num::fast` (plan row TEST-complete-kernel, author P189): division by
//! num-bigint at and past `DIV_LEAF`, `div_rem_past_leaf` on both sides of its choice between
//! long division over the divisor's nonzero words and the division by a reciprocal, the
//! product's methods on both sides of `MUL_LEAF`, a factor's kept spectra, the reciprocal, the
//! gcd, the reading of digits and the Bezout coefficients, each against num-bigint. Small
//! sizes only: the unit build sets `MUL_LEAF` at 48 words, and `DIV_LEAF` is 64 words.

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::num::crossover::{self, Kept};
use crate::num::{bezout_int, div_rem_uint, gcd_uint, gcd_uint_recursive, read_digits, rem_uint};

/// splitmix64 words, `words` of them, the top one not zero.
fn random(seed: u64, words: usize) -> BigUint {
    let mut x = seed;
    let mut w: Vec<u64> = (0..words)
        .map(|_| {
            x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        })
        .collect();
    if let Some(top) = w.last_mut() {
        *top |= 1 << 63;
    }
    from_words(&w)
}

fn from_words(w: &[u64]) -> BigUint {
    BigUint::from_slice(
        &w.iter()
            .flat_map(|&d| [d as u32, (d >> 32) as u32])
            .collect::<Vec<_>>(),
    )
}

/// A number of `words` words with exactly `nonzero` of them nonzero, the top and the lowest
/// among them (for `nonzero >= 2`), spread evenly.
fn with_nonzero(seed: u64, words: usize, nonzero: usize) -> BigUint {
    let fill = random(seed, words).to_u64_digits();
    let mut w = vec![0u64; words];
    for i in 0..nonzero {
        let at = match nonzero {
            1 => words - 1,
            _ => i * (words - 1) / (nonzero - 1),
        };
        w[at] = fill[at] | 1;
    }
    w[words - 1] |= 1 << 63;
    from_words(&w)
}

/// All ones, a power of two, one above it, and random, each of `words` words.
fn forms(words: usize, seed: u64) -> Vec<BigUint> {
    let bits = 64 * words as u64;
    let one = BigUint::one();
    vec![
        (&one << bits) - 1u32,
        &one << (bits - 1),
        (&one << (bits - 1)) + 1u32,
        random(seed, words),
    ]
}

/// Every division path agrees with num-bigint on `a / b`, `a >= b > 0`.
fn check_all_paths(a: &BigUint, b: &BigUint, case: &str) {
    let want = a.div_rem(b);
    assert_eq!(div_rem_uint(a, b), want, "div_rem, {case}");
    assert_eq!(rem_uint(a, b), want.1, "rem, {case}");
    assert_eq!(
        crossover::div_rem_past_leaf(a, b),
        want,
        "past leaf, {case}"
    );
    assert_eq!(
        crossover::div_rem_by_reciprocal(a, b),
        want,
        "reciprocal, {case}"
    );
    if b.bits() > 64 {
        assert_eq!(crossover::div_rem_sparse(a, b), want, "sparse, {case}");
    }
}

/// `div_rem` hands a divisor or a quotient of at most `DIV_LEAF` bits to num-bigint, and
/// decides past it: on each side of the leaf, by the divisor's width and by the quotient's,
/// at exactly `DIV_LEAF` bits and one bit past.
#[test]
fn division_on_both_sides_of_the_leaf() {
    let leaf = crossover::DIV_LEAF;
    assert_eq!(leaf, 4096);
    // (divisor, dividend, past the leaf?): the divisor of 4096 bits and of 4097, then the
    // quotient of 4096 bits and of 4097, the other part well past.
    // A random number of exactly `bits` bits.
    let wide = |seed, bits: u64| {
        let words = bits.div_ceil(64);
        random(seed, words as usize) >> (64 * words - bits)
    };
    let cases = [
        (wide(1, leaf), wide(2, leaf + 5000), false),
        (wide(3, leaf + 1), wide(4, leaf + 1 + 5000), true),
        (wide(5, 5000), wide(6, 5000 + leaf - 1), false),
        (wide(7, 5000), wide(8, 5000 + leaf), true),
    ];
    for (i, (b, a, past)) in cases.iter().enumerate() {
        assert!(a > b, "case {i}");
        assert_eq!(
            crossover::div_flip(a, b).is_some(),
            *past,
            "case {i}: decided past the leaf"
        );
        // The unit build sets `DIV_COST` infinite, so past the leaf num-bigint is never taken.
        assert_eq!(crossover::div_by_num_bigint(a, b), !*past, "case {i}");
        check_all_paths(a, b, &format!("case {i}"));
    }
}

/// `div_rem_past_leaf` takes long division over the divisor's nonzero words while they are
/// few and the reciprocal once they are many; the method flips once as the count grows, as
/// `sparse_flip` against `SPARSE_WORD` says, and both give num-bigint's quotient and remainder,
/// for a quotient narrower and one wider than the divisor.
#[test]
fn past_the_leaf_both_methods_and_the_flip_between_them() {
    // Dense divisors flip to the reciprocal only at a few hundred words.
    for (bw, aw) in [(600usize, 1200usize), (300, 1600)] {
        let mut methods = Vec::new();
        for nonzero in [
            1,
            2,
            3,
            5,
            9,
            17,
            33,
            bw / 4,
            bw / 2,
            3 * bw / 4,
            bw - 1,
            bw,
        ] {
            let b = with_nonzero(nonzero as u64, bw, nonzero);
            let a = random(100 + nonzero as u64, aw);
            let rows = crossover::div_by_rows(&a, &b);
            let flip = crossover::sparse_flip(&a, &b).expect("a flip past the leaf");
            assert_eq!(
                rows,
                crossover::SPARSE_WORD <= flip,
                "{bw} words, {nonzero} nonzero"
            );
            methods.push(rows);
            let case = format!("{aw} by {bw} words, {nonzero} nonzero");
            check_all_paths(&a, &b, &case);
            // The extreme remainders: zero, and one less than the divisor.
            let q = &a >> (64 * bw);
            check_all_paths(&(&q * &b), &b, &format!("{case}, exact"));
            check_all_paths(
                &(&q * &b + (&b - 1u32)),
                &b,
                &format!("{case}, largest remainder"),
            );
        }
        // Rows at the few, the reciprocal at the many, and one change between.
        assert!(
            methods[0] && !methods[methods.len() - 1],
            "{bw} words: {methods:?}"
        );
        let changes = methods.windows(2).filter(|w| w[0] != w[1]).count();
        assert_eq!(changes, 1, "{bw} words: {methods:?}");
    }
}

/// Dividends and divisors of the edge forms past the leaf: all ones, a power of two, one above
/// it, and random, each against each; a dividend equal to the divisor; a dividend below it.
#[test]
fn edge_forms_past_the_leaf() {
    for a in forms(140, 9) {
        for b in forms(66, 10) {
            check_all_paths(
                &a,
                &b,
                &format!("{a:x} by {b:x}")
                    .chars()
                    .take(40)
                    .collect::<String>(),
            );
        }
    }
    let b = random(11, 70);
    check_all_paths(&b, &b, "a == b");
    let below = &b - 1u32;
    assert_eq!(div_rem_uint(&below, &b), (BigUint::zero(), below.clone()));
    assert_eq!(rem_uint(&below, &b), below);
    assert_eq!(
        div_rem_uint(&BigUint::zero(), &b),
        (BigUint::zero(), BigUint::zero())
    );
}

/// Small operands, at and below one word, where num-bigint divides: 1 by 1, `u64::MAX` by
/// itself and by 1, a two-word dividend by a one-word divisor.
#[test]
fn small_divisions() {
    let max = BigUint::from(u64::MAX);
    let two_words = (&max << 64u32) | &max;
    for (a, b) in [
        (BigUint::one(), BigUint::one()),
        (max.clone(), max.clone()),
        (max.clone(), BigUint::one()),
        (two_words.clone(), max.clone()),
        (two_words.clone(), BigUint::from(3u32)),
    ] {
        assert_eq!(div_rem_uint(&a, &b), a.div_rem(&b), "{a} by {b}");
        assert_eq!(rem_uint(&a, &b), &a % &b, "{a} by {b}");
    }
}

/// `div_rem` of a zero divisor is a caller's bug, refused by a panic, never a value.
#[test]
#[should_panic(expected = "a division by zero")]
fn a_zero_divisor_panics() {
    div_rem_uint(&BigUint::one(), &BigUint::zero());
}

/// The product's method: num-bigint at or below `MUL_LEAF` words of the shorter factor, and
/// past it rows or transforms as `transform_flip` against `TRANSFORM_COST` says; rows for a
/// factor with one nonzero word. Each method's product equals num-bigint's.
#[test]
fn products_on_both_sides_of_the_leaf() {
    let leaf = crossover::MUL_LEAF;
    assert_eq!(leaf, 48);
    let mut seen = Vec::new();
    for (la, lb) in [
        (1, 1),
        (leaf, leaf),
        (leaf, 300),
        (leaf + 1, leaf + 1),
        (leaf + 1, 300),
        (100, 100),
        (400, 400),
    ] {
        for (x, y) in forms(la, la as u64)
            .iter()
            .zip(forms(lb, 3 + lb as u64).iter())
        {
            let method = crossover::mul_method(x, y);
            seen.push(method);
            let flip = crossover::transform_flip(x, y);
            assert_eq!(flip.is_none(), la.min(lb) <= leaf, "{la} by {lb}");
            assert_eq!(
                crossover::toom_flip(x, y).is_none(),
                la.min(lb) <= leaf,
                "{la} by {lb}"
            );
            match flip {
                None => assert_eq!(method, "num-bigint", "{la} by {lb}"),
                Some(f) => {
                    let rows = crossover::TRANSFORM_COST >= f;
                    assert_eq!(
                        method,
                        if rows { "rows" } else { "transforms" },
                        "{la} by {lb}"
                    );
                }
            }
            let want = x * y;
            assert_eq!(crossover::mul_by_rows(x, y), want, "rows, {la} by {lb}");
            assert_eq!(
                crossover::mul_by_transforms(x, y),
                want,
                "transforms, {la} by {lb}"
            );
            assert_eq!(crate::num::mul_uint(x, y), want, "mul, {la} by {lb}");
        }
    }
    let sparse = with_nonzero(1, 100, 1);
    let dense = random(2, 100);
    assert_eq!(crossover::mul_method(&sparse, &dense), "rows");
    assert!(
        seen.contains(&"transforms") && seen.contains(&"rows"),
        "{seen:?}"
    );
}

/// A factor's kept spectra: its products by every width up to `other`, edge forms included,
/// equal num-bigint's whether taken by the spectra or by `mul`, and the choice follows
/// `cached_flip` against `CACHED_COST` wherever that decides.
#[test]
fn kept_spectra_products() {
    for (wx, other) in [(49, 49), (60, 100), (100, 60)] {
        for x in forms(wx, wx as u64) {
            let kept = Kept::new(x.clone(), other);
            assert_eq!(kept.value(), &x);
            for wy in [1, 2, 48, 49, other - 1, other] {
                for y in forms(wy, 7 + wy as u64) {
                    let want = &x * &y;
                    assert_eq!(kept.mul(&y), want, "{wx} by {wy} of {other}");
                    assert_eq!(kept.factor_mul(&y), want, "{wx} by {wy} of {other}");
                    if let Some(f) = kept.cached_flip(&y) {
                        assert_eq!(
                            kept.by_spectra(&y),
                            crossover::CACHED_COST < f,
                            "{wx} by {wy}"
                        );
                    }
                }
            }
            assert!(kept.mul(&BigUint::zero()).is_zero());
        }
    }
}

/// `2^2k / x` floored, for `x` of `k` bits, at each leaf, the least (4 bits, below which the
/// leaf is raised to 4), one word and wide: of the forms all ones, a power of two, one above,
/// and random.
#[test]
fn reciprocals() {
    let one = BigUint::one();
    for k in [1u64, 2, 3, 63, 64, 65, 200, 1000, 3000] {
        let words = k.div_ceil(64) as usize;
        let xs = [
            (&one << k) - 1u32,
            &one << (k - 1),
            (&one << (k - 1)) + 1u32,
            random(k, words) >> (64 * words as u64 - k),
        ];
        for x in xs.into_iter().filter(|x| x.bits() == k) {
            let want = (&one << (2 * k)) / &x;
            for leaf in [0, 4, 64, crossover::RECIP_LEAF, 4096] {
                assert_eq!(
                    crossover::reciprocal(&x, leaf),
                    want,
                    "{k} bits, leaf {leaf}"
                );
            }
        }
    }
}

/// The gcd at each leaf and lift, and the plain and recursive forms: a zero operand, equal
/// operands, coprime ones, a shared factor, a shared power of two, widths that differ.
#[test]
fn gcds() {
    let f = random(1, 20);
    let cases = [
        (BigUint::zero(), random(2, 30)),
        (random(3, 30), BigUint::zero()),
        (random(4, 40), random(4, 40)),
        (random(5, 40), random(6, 40)),
        (&f * random(7, 30), &f * random(8, 50)),
        (random(9, 30) << 200u32, random(10, 30) << 77u32),
        (random(11, 3), random(12, 120)),
        (BigUint::one(), random(13, 50)),
    ];
    for (i, (a, b)) in cases.iter().enumerate() {
        let want = a.gcd(b);
        assert_eq!(gcd_uint(a, b), want, "case {i}");
        assert_eq!(gcd_uint_recursive(a, b), want, "case {i}, recursive");
        if a.is_zero() || b.is_zero() {
            continue;
        }
        for leaf in [64, 1024, crossover::GCD_LEAF] {
            for lift in [64, crossover::LIFT_BITS] {
                assert_eq!(
                    crossover::gcd(a, b, leaf, lift),
                    want,
                    "case {i}, {leaf}, {lift}"
                );
            }
        }
    }
}

/// Decimal digits read at each leaf: one digit, leading zeros, a run of nines, lengths around
/// the leaf, and a long text read by halves.
#[test]
fn digits_read_at_each_leaf() {
    let long: String = (0..700)
        .map(|i| char::from(b'0' + (i * 7 % 10) as u8))
        .collect();
    let texts = [
        "0",
        "7",
        "007",
        "0000",
        "99999999999999999999",
        "18446744073709551616",
        &long,
    ];
    for t in texts {
        let want = BigUint::parse_bytes(t.as_bytes(), 10).expect("decimal");
        assert_eq!(read_digits(t), want, "{t}");
        for leaf in [1, 2, 19, 20, crossover::LEAF_DIGITS, 1000] {
            assert_eq!(crossover::read_digits(t, leaf), want, "{t}, leaf {leaf}");
        }
    }
}

/// Bezout's coefficients `s a + t b = gcd(a, b)` at each lift, signs of `a` and `b` included
/// through `bezout_int`, and a zero operand.
#[test]
fn bezout_coefficients() {
    let f = random(1, 5);
    let cases = [
        (random(2, 3), random(3, 7)),
        (&f * random(4, 10), &f * random(5, 60)),
        (random(6, 60) << 70u32, random(7, 2) << 3u32),
        (BigUint::one(), random(8, 9)),
        (random(9, 4), random(9, 4)),
    ];
    for (i, (a, b)) in cases.iter().enumerate() {
        let want = a.gcd(b);
        for lift in [64, crossover::LIFT_BITS] {
            let (g, s, t) = crossover::bezout(a, b, lift).expect("coefficients");
            assert_eq!(g, want, "case {i}, lift {lift}");
            assert_eq!(
                s * BigInt::from(a.clone()) + t * BigInt::from(b.clone()),
                BigInt::from(g)
            );
        }
        for (sa, sb) in [(1, 1), (-1, 1), (1, -1), (-1, -1)] {
            let (a, b) = (BigInt::from(a.clone()) * sa, BigInt::from(b.clone()) * sb);
            let (g, s, t) = bezout_int(&a, &b).expect("coefficients");
            assert_eq!(g, BigInt::from(want.clone()), "case {i}, signs {sa} {sb}");
            assert_eq!(&s * &a + &t * &b, g, "case {i}, signs {sa} {sb}");
        }
    }
    let b = BigInt::from(random(10, 3));
    let (g, s, t) = bezout_int(&BigInt::zero(), &b).expect("coefficients");
    assert_eq!(
        (g.clone(), &s * BigInt::zero() + &t * &b),
        (b.clone(), b.clone())
    );
    let (g0, ..) = bezout_int(&-&b, &BigInt::zero()).expect("coefficients");
    assert_eq!(g0, b);
    let _ = (g, s);
}
