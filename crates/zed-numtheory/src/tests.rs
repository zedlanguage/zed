use num_bigint::BigUint;
use num_integer::Integer;

use super::*;

/// The gcd by Euclid's algorithm, the definition the binary one is checked against.
fn euclid(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The random words of the test `test`, from the shared generator with a new seed each run,
/// printed (`crate::seed::Rng::fresh`).
fn words(test: &str) -> impl FnMut() -> u64 {
    let (mut rng, _) = crate::seed::Rng::fresh(test);
    move || rng.next_u64()
}

/// The edge words: 0, 1, 2, small primes and powers of 2, and the largest values.
const EDGES: [u64; 12] = [
    0,
    1,
    2,
    3,
    4,
    6,
    1 << 32,
    1 << 63,
    18_446_744_073_709_551_557,
    u64::MAX - 1,
    u64::MAX,
    (1 << 61) - 1,
];

#[test]
fn the_word_gcds_agree_with_euclid() {
    for a in 0..200u64 {
        for b in 0..200u64 {
            let want = euclid(a.into(), b.into());
            assert_eq!(u128::from(gcd_u64(a, b)), want, "{a} {b}");
            assert_eq!(gcd_u128(a.into(), b.into()), want, "{a} {b}");
        }
    }
    for a in EDGES {
        for b in EDGES {
            assert_eq!(
                u128::from(gcd_u64(a, b)),
                euclid(a.into(), b.into()),
                "{a} {b}"
            );
        }
    }
    let mut next = words("the_word_gcds_agree_with_euclid");
    for _ in 0..10_000 {
        let (a, b, c) = (next(), next(), next() >> 40);
        // A common factor `c`, so that the gcd is not nearly always 1.
        let (x, y) = (u128::from(a) * u128::from(c), u128::from(b) * u128::from(c));
        assert_eq!(gcd_u128(x, y), euclid(x, y), "{x} {y}");
        assert_eq!(
            u128::from(gcd_u64(a, b)),
            euclid(a.into(), b.into()),
            "{a} {b}"
        );
    }
    assert_eq!(gcd_u128(u128::MAX, u128::MAX), u128::MAX);
    assert_eq!(gcd_u128(1 << 127, 0), 1 << 127);
    assert_eq!(gcd_u128(1 << 127, 1 << 100), 1 << 100);
    // Equal operands: the first difference is 0, whose trailing zeros are the full width.
    assert_eq!(gcd_u128(1 << 127, 1 << 127), 1 << 127);
    assert_eq!(gcd_u64(1 << 63, 1 << 63), 1 << 63);
}

#[test]
fn the_big_remainder_and_gcd_by_a_word_agree_with_num_bigint() {
    let mut next = words("the_big_remainder_and_gcd_by_a_word_agree_with_num_bigint");
    for n in 0..40 {
        let x: BigUint = (0..n).fold(BigUint::from(0u8), |x, _| (x << 64u32) + next());
        let ds = [
            1,
            2,
            3,
            5,
            12,
            15,
            1 << 63,
            1_000_003,
            (1 << 61) - 1,
            u64::MAX,
            next(),
        ];
        for d in ds.into_iter().filter(|&d| d > 0) {
            let r = u64::try_from(&x % d).unwrap();
            assert_eq!(rem_big_u64(&x, d), r, "{x} mod {d}");
            let want = u64::try_from(x.gcd(&BigUint::from(d))).unwrap();
            assert_eq!(gcd_big_u64(&x, d), want, "gcd({x}, {d})");
        }
    }
    // A shared factor wider than the remainder's first word.
    let big = BigUint::from(u64::MAX) * 1_000_003u64 * 999_983u64;
    assert_eq!(gcd_big_u64(&big, 1_000_003 * 7), 1_000_003);
    assert_eq!(gcd_big_u64(&(big << 5u32), 1_000_003 * 64), 1_000_003 * 32);
    assert_eq!(gcd_big_u64(&BigUint::from(0u8), 15), 15);
}

#[test]
fn products_and_powers_modulo_a_word_agree_with_num_bigint() {
    let mut next = words("products_and_powers_modulo_a_word_agree_with_num_bigint");
    let mut moduli: Vec<u64> = EDGES.iter().copied().filter(|&m| m > 0).collect();
    moduli.extend((0..20).map(|_| next()));
    for &m in &moduli {
        for _ in 0..50 {
            let (a, b, e) = (next(), next(), next() >> (next() % 64));
            let bm = BigUint::from(m);
            let want = (BigUint::from(a) * b) % &bm;
            assert_eq!(BigUint::from(mul_mod(a, b, m)), want, "{a} * {b} mod {m}");
            let want = BigUint::from(a).modpow(&BigUint::from(e), &bm);
            assert_eq!(BigUint::from(pow_mod(a, e, m)), want, "{a} ^ {e} mod {m}");
            let wide = (BigUint::from(e) << 70u32) + next();
            let want = BigUint::from(a).modpow(&wide, &bm);
            assert_eq!(
                BigUint::from(pow_mod_big(a, &wide, m)),
                want,
                "{a}^{wide} mod {m}"
            );
        }
        assert_eq!(pow_mod(0, 0, m), 1 % m);
        assert_eq!(pow_mod_big(0, &BigUint::from(0u8), m), 1 % m);
    }
    for a in 0..30 {
        for e in 0..30 {
            for m in 1..30 {
                let want = (0..e).fold(1 % m, |r, _| r * a % m);
                assert_eq!(pow_mod(a, e, m), want, "{a}^{e} mod {m}");
                assert_eq!(
                    pow_mod_big(a, &BigUint::from(e), m),
                    want,
                    "{a}^{e} mod {m}"
                );
            }
        }
    }
    // Fermat at the largest 64-bit prime, where every product is widest.
    let q = u64::MAX - 58;
    assert_eq!(pow_mod(12_345, q - 1, q), 1);
    assert_eq!(pow_mod(q - 1, 2, q), 1);
    // `pow_mod` is `const`, for tables computed at compile time.
    const FERMAT: u64 = pow_mod(3, 1_000_002, 1_000_003);
    assert_eq!(FERMAT, 1);
}

/// The copy in presburger's `row_sums/plane.rs` before the move: Euclid on the signed values
/// with truncated division. Kept here only to show the shared routine gives the same
/// cofactors on every input, so no lifted point changes.
fn bezout_signed_before(a: i128, b: i128) -> Option<(i128, i128)> {
    let (mut r0, mut r1) = (a, b);
    let (mut s0, mut s1) = (1i128, 0i128);
    let (mut t0, mut t1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0.checked_div(r1)?;
        (r0, r1) = (r1, r0.checked_sub(q.checked_mul(r1)?)?);
        (s0, s1) = (s1, s0.checked_sub(q.checked_mul(s1)?)?);
        (t0, t1) = (t1, t0.checked_sub(q.checked_mul(t1)?)?);
    }
    match r0 {
        1 => Some((s0, t0)),
        -1 => Some((s0.checked_neg()?, t0.checked_neg()?)),
        _ => None,
    }
}

#[test]
fn bezout_cofactors_give_the_gcd_and_are_the_least() {
    let mut next = words("bezout_cofactors_give_the_gcd_and_are_the_least");
    let mut xs: Vec<i128> = (-40..=40).collect();
    xs.extend([
        i128::MAX,
        i128::MAX - 1,
        i128::MIN + 1,
        1 << 126,
        -(1 << 126),
    ]);
    xs.extend((0..60).map(|_| (next() as i128) << (next() % 64)));
    xs.extend((0..60).map(|_| -((next() as i128) << (next() % 63))));
    for &a in &xs {
        for &b in &xs {
            let (g, s, t) = bezout_i128(a, b).expect("no i128::MIN");
            let want = gcd_u128(a.unsigned_abs(), b.unsigned_abs());
            assert_eq!(g as u128, want, "gcd {a} {b}");
            assert_eq!(
                s.wrapping_mul(a).wrapping_add(t.wrapping_mul(b)),
                g,
                "{a} {b}"
            );
            if g != 0 {
                assert!(
                    s.unsigned_abs() <= (b.unsigned_abs() / want).max(1),
                    "{a} {b}"
                );
                assert!(
                    t.unsigned_abs() <= (a.unsigned_abs() / want).max(1),
                    "{a} {b}"
                );
            }
            if g == 1 {
                assert_eq!(bezout_signed_before(a, b), Some((s, t)), "{a} {b}");
            }
        }
    }
    assert_eq!(bezout_i128(0, 0), Some((0, 1, 0)));
    assert_eq!(bezout_i128(i128::MIN, 3), None);
    assert_eq!(bezout_i128(3, i128::MIN), None);
}

/// `m61::P = 2^61 - 1` is prime, which `m61::inv` (Fermat) and the callers listed at `m61`
/// rely on: by `is_prime`, exact on every 64-bit word, and by the Lucas-Lehmer test (D. H.
/// Lehmer, "An extended theory of Lucas' functions", Annals of Math. 31(3):419-448, 1930,
/// doi:10.2307/1968235), which uses no code of `is_prime`. Read 2026-11-21 in the JSTOR scan
/// (from LibGen). Section 5.3, p. 443, takes `2^n - 1` "with n an odd prime", and Theorem 5.4
/// reads: "The number N = 2^n - 1 is a prime if and only if it divides the (n-1)-st term of
/// the series 4, 14, 194, 37634, ..., S_k, ... where S_k = S_(k-1)^2 - 2." The proof sets
/// `S_k = V_(2^k)` for the Lucas sequence with `R = 2`, `Q = -1`; necessity is Theorem 4.9,
/// sufficiency is that the rank of apparition of `N` is then `2^n = N + 1`, so `N` is prime by
/// Theorem 5.1. The loop below counts from `s = 4` as the first term, so after `n - 2` squarings
/// `s` is the paper's `(n-1)`-st term; it reduces modulo `N` at each step, which changes no
/// residue. `61` and `11` are odd primes, as the theorem needs. The composite `2^11 - 1 =
/// 23 * 89` fails the test, which shows the loop can fail; neither case checks the test on
/// any other exponent.
#[test]
fn the_mersenne_modulus_is_prime() {
    use m61::P;
    assert!(is_prime(P));
    let mut s = 4;
    for _ in 0..61 - 2 {
        s = m61::sub(m61::mul(s, s), 2);
    }
    assert_eq!(s, 0, "Lucas-Lehmer for 2^61 - 1");
    // A negative control: 2^11 - 1 = 2047 = 23 * 89 fails the same test.
    let m = (1u64 << 11) - 1;
    let mut s = 4;
    for _ in 0..11 - 2 {
        s = (s * s + m - 2) % m;
    }
    assert_ne!(s, 0, "Lucas-Lehmer for 2^11 - 1");
}

#[test]
fn the_mersenne_arithmetic_agrees_with_division() {
    use m61::P;
    let mut next = words("the_mersenne_arithmetic_agrees_with_division");
    let mut xs = vec![0, 1, 2, P - 2, P - 1, 1 << 60, (1 << 60) + 1];
    xs.extend((0..200).map(|_| next() % P));
    for &a in &xs {
        for &b in &xs {
            let want = u128::from(a) * u128::from(b) % u128::from(P);
            assert_eq!(u128::from(m61::mul(a, b)), want, "{a} * {b}");
            assert_eq!(m61::add(a, b), (a + b) % P, "{a} + {b}");
            assert_eq!(m61::sub(a, b), (a + P - b) % P, "{a} - {b}");
        }
        // `b = P` is read as 0.
        assert_eq!(m61::add(a, P), a, "{a} + P");
        if a != 0 {
            assert_eq!(m61::mul(a, m61::inv(a)), 1, "1 / {a}");
        }
    }
    let bp = BigUint::from(P);
    for &b in xs.iter().take(40) {
        for e in [0u64, 1, 2, P - 2, P - 1, P, u64::MAX, next()] {
            let want = BigUint::from(b).modpow(&BigUint::from(e), &bp);
            assert_eq!(BigUint::from(m61::pow_word(b, e)), want, "{b}^{e} by word");
            let e = BigUint::from(e);
            let want = BigUint::from(b).modpow(&e, &bp);
            assert_eq!(BigUint::from(m61::pow(b, &e)), want, "{b}^{e}");
            let wide = &e << 90u32;
            let want = BigUint::from(b).modpow(&wide, &bp);
            assert_eq!(BigUint::from(m61::pow(b, &wide)), want, "{b}^{wide}");
        }
    }
    // A base at or past `P`, reduced first: `P^e = 0` for `e > 0`, and `0^0 = 1`.
    assert_eq!(m61::pow(P, &BigUint::from(5u8)), 0);
    assert_eq!(m61::pow(P, &BigUint::from(0u8)), 1);
    assert_eq!(m61::pow(P + 3, &BigUint::from(2u8)), 9);
    assert_eq!(m61::pow(u64::MAX, &BigUint::from(1u8)), u64::MAX % P);
}

/// `m61::reduce` is `x % P` on every `u128` near an edge of its two folds: each power of two
/// and its neighbors (the folds split at bit 61), the multiples `kP` and their neighbors for
/// `k` up to 130 (`2P - 1` is the largest sum a fold can leave, and `64P + 64` the largest the
/// first fold leaves of a `u128`), `P^2`, `(P - 1)^2` and `2^122` with theirs (the largest
/// product of two residues, which `m61::mul` folds once), words of all ones in each part,
/// `u128::MAX`, and words drawn at random. Also that `m61::mul` agrees with it on products of
/// residues near `P`. It catches a missing second fold (a wrong answer past `P^2`), a `>` for
/// `>=` (an answer of `P` itself for `x = P` or `2P`), and a cast that drops bits.
#[test]
fn the_reduction_of_a_wide_word_agrees_with_division() {
    use m61::P;
    let p = u128::from(P);
    let mut xs: Vec<u128> = Vec::new();
    let mut near = |x: u128| {
        for d in 0..3u128 {
            xs.extend([x.wrapping_add(d), x.wrapping_sub(d)]);
        }
    };
    for k in 0..128 {
        near(1u128 << k);
    }
    for k in 0..131u128 {
        near(k * p);
    }
    near(p * p);
    near((p - 1) * (p - 1));
    near(1u128 << 122);
    near(u128::MAX);
    near(u128::MAX - p);
    near(p << 61 | p);
    near((p << 61 | p) << 61 | p);
    let mut next = words("the_reduction_of_a_wide_word_agrees_with_division");
    xs.extend((0..2000).map(|_| u128::from(next()) << 64 | u128::from(next())));
    xs.extend((0..2000).map(|_| u128::from(next())));
    for &x in &xs {
        assert_eq!(u128::from(m61::reduce(x)), x % p, "{x}");
    }
    let mut rs = vec![0, 1, 2, P - 3, P - 2, P - 1, (1 << 60) - 1, 1 << 60];
    rs.extend((0..100).map(|_| next() % P));
    for &a in &rs {
        for &b in &rs {
            let x = u128::from(a) * u128::from(b);
            assert_eq!(m61::mul(a, b), m61::reduce(x), "{a} * {b}");
        }
    }
}

/// The polynomial hash of `bytes` by Horner's rule, one byte at a time, and `b` to their length:
/// the definition `m61::PolyBytes::hash` is checked against.
fn horner(b: u64, bytes: &[u8]) -> (u64, u64) {
    bytes.iter().fold((0, 1), |(h, p), &x| {
        (m61::add(m61::mul(h, b), u64::from(x) + 1), m61::mul(p, b))
    })
}

#[test]
fn the_eight_byte_hash_is_horners_rule() {
    use m61::P;
    let mut next = words("the_eight_byte_hash_is_horners_rule");
    for b in [0, 1, 2, P - 1, 0x0f3d_5b79_a2c4_e681, next() % P] {
        let poly = m61::PolyBytes::new(b);
        // Every tail length, and every chunk boundary up to eight chunks, with random bytes, all
        // 0xFF (the largest digits, the largest sum before a fold) and all zero bytes.
        let mut lens: Vec<usize> = (0..=72).collect();
        lens.extend((0..8).map(|_| (next() % 5000) as usize));
        for n in lens {
            let random: Vec<u8> = (0..n).map(|_| next() as u8).collect();
            for bytes in [random, vec![0xFF; n], vec![0; n]] {
                assert_eq!(poly.hash(&bytes), horner(b, &bytes), "base {b}, {n} bytes");
            }
        }
    }
}

/// The hashes `p` joined as a balanced tree, halves first.
fn joined_as_a_tree(p: &[m61::PolyHash]) -> m61::PolyHash {
    match p {
        [] => m61::PolyHash::EMPTY,
        [x] => *x,
        _ => joined_as_a_tree(&p[..p.len() / 2]).then(joined_as_a_tree(&p[p.len() / 2..])),
    }
}

/// `PolyHash` joins as the strings join: random strings cut at random places, their pieces'
/// hashes joined left to right and as a balanced tree, against Horner's rule over the whole;
/// one-digit units against Horner's rule of the digit; and `Prefix::span` of every span of a
/// short string against Horner's rule over it.
#[test]
fn poly_hashes_join_as_their_strings_do() {
    use m61::{P, PolyHash, Prefix};
    let mut next = words("poly_hashes_join_as_their_strings_do");
    let digit = |x: &u8| u64::from(*x) + 1;
    for b in [0, 1, 2, P - 1, 0x0f3d_5b79_a2c4_e681, next() % P] {
        let poly = m61::PolyBytes::new(b);
        let hash = |s: &[u8]| {
            let (h, pow) = poly.hash(s);
            PolyHash { h, pow }
        };
        for _ in 0..40 {
            let n = (next() % 200) as usize;
            let s: Vec<u8> = (0..n).map(|_| next() as u8).collect();
            let mut cuts: Vec<usize> = (0..(next() % 9))
                .map(|_| (next() as usize) % (n + 1))
                .collect();
            cuts.extend([0, n]);
            cuts.sort_unstable();
            let pieces: Vec<PolyHash> = cuts.windows(2).map(|w| hash(&s[w[0]..w[1]])).collect();
            let want = horner(b, &s);
            let left = pieces.iter().fold(PolyHash::EMPTY, |a, &p| a.then(p));
            assert_eq!((left.h, left.pow), want, "base {b}, cuts {cuts:?}");
            let t = joined_as_a_tree(&pieces);
            assert_eq!((t.h, t.pow), want, "base {b}, cuts {cuts:?}, as a tree");
            let units = s
                .iter()
                .fold(PolyHash::EMPTY, |a, x| a.then(PolyHash::unit(digit(x), b)));
            assert_eq!((units.h, units.pow), want, "base {b}, one digit at a time");
        }
        let s: Vec<u8> = (0..40).map(|_| next() as u8).collect();
        let pre = Prefix::new(b, s.iter().map(digit));
        let pow = m61::powers(b, s.len());
        assert_eq!(pre.len(), s.len());
        assert_eq!(pre.whole(), horner(b, &s).0);
        for i in 0..=s.len() {
            assert_eq!(pow[i], horner(b, &s[..i]).1, "base {b}, B^{i}");
            assert_eq!(pre.get(i), horner(b, &s[..i]).0);
            for j in i..=s.len() {
                assert_eq!(
                    pre.span(i, j, &pow),
                    horner(b, &s[i..j]).0,
                    "base {b}, {i}..{j}"
                );
            }
        }
    }
}

/// `cbrt_floor` at every cube `k^3` up to `2^64 - 1` and at its two neighbors, where a float
/// estimate is most often one off, at `2^64 - 1`, and on random words by its definition
/// `r^3 <= n < (r + 1)^3`.
#[test]
fn the_cube_roots_are_exact() {
    // `cbrt(2^64 - 1) = 2642245`, as `2642245^3 = 18446724184312856125 < 2^64 - 1` and
    // `2642246^3 > 2^64`, both checked here.
    let top = 2_642_245u64;
    assert!(u128::from(top).pow(3) <= u128::from(u64::MAX));
    assert!(u128::from(top + 1).pow(3) > u128::from(u64::MAX));
    assert_eq!(cbrt_floor(u64::MAX), top);
    assert_eq!(cbrt_floor(0), 0);
    for k in 1..=top {
        let c = k * k * k;
        assert_eq!(cbrt_floor(c - 1), k - 1, "{k}^3 - 1");
        assert_eq!(cbrt_floor(c), k, "{k}^3");
        if c < u64::MAX {
            assert_eq!(cbrt_floor(c + 1), k, "{k}^3 + 1");
        }
    }
    let mut next = words("the_cube_roots_are_exact");
    for n in (0..100_000).map(|_| next()).chain(EDGES) {
        let r = u128::from(cbrt_floor(n));
        assert!(
            r.pow(3) <= u128::from(n) && u128::from(n) < (r + 1).pow(3),
            "{n}"
        );
    }
}

/// `sqrt_exact_u128` against squaring: every `v` below `2^20`, and `k^2` and its neighbors for
/// random `k` up to `2^64 - 1`, so up to `v` near `2^128`.
#[test]
fn the_square_test_is_exact() {
    for v in 0..1u128 << 20 {
        let s = v.isqrt();
        assert_eq!(sqrt_exact_u128(v), (s * s == v).then_some(s), "{v}");
    }
    let mut next = words("the_square_test_is_exact");
    for k in (0..100_000).map(|_| next()).chain(EDGES) {
        let k = u128::from(k);
        let v = k * k;
        assert_eq!(sqrt_exact_u128(v), Some(k), "{k}^2");
        // `k^2 - 1` is a square only at `k = 1` (0), and `k^2 + 1` only at `k = 0` (1).
        if k > 1 {
            assert_eq!(sqrt_exact_u128(v - 1), None, "{k}^2 - 1");
        }
        if k > 0 {
            assert_eq!(sqrt_exact_u128(v + 1), None, "{k}^2 + 1");
        }
    }
}

#[test]
fn the_inverse_seed_is_right_in_five_bits() {
    for x in (1..32u64).step_by(2) {
        assert_eq!(x.wrapping_mul(x.wrapping_mul(3) ^ 2) % 32, 1, "{x}");
    }
}

#[test]
fn inverses_modulo_2_64_are_inverses() {
    let mut next = words("inverses_modulo_2_64_are_inverses");
    let mut xs = vec![
        1,
        3,
        5,
        u64::MAX,
        u64::MAX - 2,
        (1 << 63) + 1,
        (1 << 61) - 1,
    ];
    xs.extend((0..10_000).map(|_| next() | 1));
    for x in xs {
        assert_eq!(x.wrapping_mul(inverse_mod_2_64(x)), 1, "{x}");
    }
}

#[test]
fn powers_modulo_2_64_agree_with_num_bigint() {
    // Moved from zedc-int's completeness tests with the function (it was `pow_word` there).
    for (b, e) in [
        (3u64, 0u64),
        (0, 0),
        (0, 5),
        (3, 1),
        (3, 40),
        (3, 41),
        (u64::MAX, 3),
        (2, 64),
        (2, 63),
        (0x9e37_79b9_7f4a_7c15, u64::MAX),
    ] {
        let unit = BigUint::from(1u32) << 64u32;
        let want = BigUint::from(b)
            .modpow(&BigUint::from(e), &unit)
            .iter_u64_digits()
            .next()
            .unwrap_or(0);
        assert_eq!(pow_mod_2_64(b, e), want, "{b} ^ {e}");
    }
}

#[test]
fn odd_roots_modulo_2_64_are_the_one_odd_root() {
    let mut next = words("odd_roots_modulo_2_64_are_the_one_odd_root");
    // Indices 1, odd primes, and odd composites (the function needs only an odd index).
    for p in [
        1u64,
        3,
        5,
        7,
        9,
        15,
        31,
        61,
        127,
        509,
        4093,
        65_521,
        u64::MAX,
    ] {
        let mut os = vec![1u64, 3, u64::MAX, u64::MAX - 2, (1 << 63) + 1];
        os.extend((0..300).map(|_| next() | 1));
        for o in os {
            let x = odd_root_mod_2_64(o, p);
            assert!(x % 2 == 1, "o = {o}, p = {p}");
            assert_eq!(pow_mod_2_64(x, p), o, "o = {o}, p = {p}");
        }
    }
    // Uniqueness, by brute force modulo 2^8: the low 8 bits of the root are the only odd
    // residue below 2^8 whose `p`-th power is `o` there.
    for p in [3u64, 5, 9, 255] {
        for o in (1..256u64).step_by(2) {
            let roots: Vec<u64> = (1..256u64)
                .step_by(2)
                .filter(|&x| pow_mod_2_64(x, p) % 256 == o)
                .collect();
            assert_eq!(roots, [odd_root_mod_2_64(o, p) % 256], "o = {o}, p = {p}");
        }
    }
}

/// Primality by trial division, the definition.
fn prime_by_trial(n: u64) -> bool {
    n >= 2
        && (2..)
            .take_while(|d| d * d <= n)
            .all(|d| !n.is_multiple_of(d))
}

#[test]
fn the_next_prime_is_the_least_prime_above() {
    for n in 0..5000u64 {
        let want = (n + 1..).find(|&q| prime_by_trial(q));
        assert_eq!(next_prime(n), want, "{n}");
    }
    let largest = 18_446_744_073_709_551_557u64;
    assert_eq!(next_prime(largest - 1), Some(largest));
    assert_eq!(next_prime(largest), None);
    assert_eq!(next_prime(u64::MAX), None);
    // The primes above `2^32` and `2^63`.
    assert_eq!(next_prime(1 << 32), Some(4_294_967_311));
    assert_eq!(next_prime(1 << 63), Some(9_223_372_036_854_775_837));
}

#[test]
fn the_least_prime_table_agrees_with_trial_division() {
    for top in [0u32, 1, 2, 3, 4, 10, 97, 1000] {
        let table = least_prime_factors(top);
        assert_eq!(table.len(), top as usize + 1);
        for (j, &e) in table.iter().enumerate() {
            let j = j as u64;
            let want = match j {
                0 | 1 => 0,
                _ if prime_by_trial(j) => PRIME,
                _ => (2..).find(|d| j.is_multiple_of(*d)).unwrap() as u16,
            };
            assert_eq!(e, want, "{j}");
        }
    }
    // Past `2^16`, where an entry no longer fits below the marker unless the proof holds: the
    // least factors of the composites to `2^20` are below `2^10`, and 65521 (the largest prime
    // below `2^16`) and 65537 (above it) are marked prime.
    let top = 1 << 20;
    let table = least_prime_factors(top);
    for j in (2..=top).step_by(997) {
        let want = match (2..).take_while(|d| d * d <= j).find(|d| j % d == 0) {
            Some(d) => d as u16,
            None => PRIME,
        };
        assert_eq!(table[j as usize], want, "{j}");
    }
    assert_eq!(table[65_521], PRIME);
    assert_eq!(table[65_537], PRIME);
    // 1000001 = 101 * 9901.
    assert_eq!(table[1_000_001], 101);
    // Every entry, by trial division, for tops one block long, one past it, and several blocks
    // long and ending inside a block (blocks of 2^15 entries below top = 2^30): the edges
    // between blocks are where a prime's first multiple is computed again.
    let block = 1u32 << 15;
    for top in [block - 1, block, block + 1, 3 * block + 17, 200_003] {
        let table = least_prime_factors(top);
        assert_eq!(table.len(), top as usize + 1);
        for j in 2..=top {
            let want = match (2..).take_while(|d| d * d <= j).find(|d| j % d == 0) {
                Some(d) => d as u16,
                None => PRIME,
            };
            assert_eq!(table[j as usize], want, "top {top} j {j}");
        }
        assert_eq!((table[0], table[1]), (0, 0));
    }
}

/// The constant of the write bound at [`least_prime_factors`]: the primes below 2^16 number
/// 6542 and the sum of their reciprocals is below 3, so the sieve makes fewer than
/// `3 top + 6542` writes for any `top < 2^32`.
#[test]
fn the_sieve_writes_fewer_than_three_times_top() {
    let odd = odd_primes_below(1 << 16);
    let primes: Vec<u64> = std::iter::once(2)
        .chain((1..odd.len()).filter(|&i| odd[i]).map(|i| 2 * i as u64 + 1))
        .collect();
    assert_eq!(primes.len(), 6542);
    let sum: f64 = primes.iter().map(|&p| 1.0 / p as f64).sum();
    // Each term is rounded by at most half an ulp of a value below 1, and the 6542 additions
    // add at most 6542 ulps of a sum below 4: under 1e-11 in all, far from the margin.
    println!("sum of 1/p over the primes below 2^16: {sum:.6}");
    assert!(sum < 3.0 - 1e-9, "{sum}");
}

/// The sieve with blocks shorter than [`SIEVE_BLOCK`] gives the same table: blocks of
/// `isqrt(top) + 1` entries (the least the sieve uses, reached for `top` past about 2^30,
/// a 2 GiB table too large for a unit test), and of 1, 2 and 7 entries, where nearly every
/// multiple sits at a block edge.
#[test]
fn the_least_prime_table_does_not_depend_on_the_block_length() {
    for top in [0u32, 1, 2, 3, 48, 49, 50, 1000, 4097] {
        let want = least_prime_factors_in_blocks(top, usize::MAX);
        for block in [1, 2, 7, top.isqrt() as usize + 1] {
            assert_eq!(
                least_prime_factors_in_blocks(top, block),
                want,
                "top {top} block {block}"
            );
        }
    }
    let top = 300_007;
    let want = least_prime_factors(top);
    assert_eq!(
        least_prime_factors_in_blocks(top, top.isqrt() as usize + 1),
        want
    );
    assert_eq!(least_prime_factors_in_blocks(top, 1000), want);
}

#[test]
fn the_odd_sieve_agrees_with_trial_division() {
    for n in (0u64..300).chain([1024, 5000]) {
        let prime = odd_primes_below(n);
        assert_eq!(prime.len() as u64, n.div_ceil(2), "{n}");
        for (i, &p) in prime.iter().enumerate() {
            let q = 2 * i as u64 + 1;
            assert_eq!(p, prime_by_trial(q), "{q} below {n}");
        }
    }
    // An odd `n` is in its own table: the last entry of `odd_primes_below(3)` is 3.
    assert_eq!(odd_primes_below(3), vec![false, true]);
    // A square of a prime as the last entry is struck: 9 = 3^2 and 25 = 5^2.
    assert!(!odd_primes_below(9)[4]);
    assert!(!odd_primes_below(25)[12]);
}

/// `is_prime` agrees with the sieve at every `n` below `psi_3 = 25326001`, where it uses one,
/// two or three bases, and says no to `psi_1`, `psi_2` and `psi_3`, the composites that pass
/// those bases, and to the least that pass the first four (`psi_4 = 3215031751`). Here, not in
/// `factor.rs`'s tests, since the sieve is in `lib.rs`, which uses `factor.rs`: the test there
/// closed an import cycle (step S.1f).
#[test]
fn primality_agrees_with_the_sieve_below_psi_3() {
    const PSI_3: u64 = 25_326_001;
    let odd = odd_primes_below(PSI_3);
    for n in 0..PSI_3 {
        let want = n == 2 || (n % 2 == 1 && odd[(n / 2) as usize]);
        assert_eq!(is_prime(n), want, "{n}");
    }
    for psi in [2047, 1_373_653, PSI_3, 3_215_031_751] {
        assert!(!is_prime(psi), "{psi}");
    }
}

#[test]
fn the_first_primes_are_the_primes_in_order() {
    let want: Vec<u64> = (2..20_000).filter(|&q| prime_by_trial(q)).collect();
    for n in [0, 1, 2, 3, 17, 18, 19, 100, want.len()] {
        assert_eq!(first_primes(n), want[..n], "{n}");
    }
    // Past several doublings of the bound: the 100000th prime is 1299709.
    assert_eq!(first_primes(100_000).last(), Some(&1_299_709));
    // The bench `first_primes(n)` at n = 100,000 and 8n relies on these: the last bound is
    // 2^21 at n (above) and 2^24 at 8n.
    let last = first_primes(800_000).last().copied();
    assert!(last.is_some_and(|p| 1 << 23 < p && p < 1 << 24), "{last:?}");
}

/// `shares_a_factor_by_table` by its definition, a gcd of every pair.
fn shares_a_factor_by_pairs(vals: &[u32]) -> Vec<bool> {
    (0..vals.len())
        .map(|i| (0..vals.len()).any(|j| j != i && gcd_u64(vals[i].into(), vals[j].into()) != 1))
        .collect()
}

/// The table's count of the values a prime divides stops at 2, so a prime held by many values
/// does not run its marker down into the least prime factors, nor wrap a count: 300 even
/// values, and 601 (a prime), give 300 answers of true and one of false. (Written by the
/// orchestrator for the earlier `u8` count, which overflowed past 255 without the stop; moved
/// from zedc-presburger with the table.)
#[test]
fn the_table_count_of_a_prime_held_by_many_values_does_not_wrap() {
    let mut vals: Vec<u32> = (1..=300).map(|k| 2 * k).collect();
    vals.push(601);
    let mut want = vec![true; 300];
    want.push(false);
    assert_eq!(shares_a_factor_by_table(&vals, 601), want);
}

/// The fact the `u16` table of `shares_a_factor_by_table` rests on: 65521 is the largest prime
/// below 2^16, so the least prime factor of a composite up to `u32::MAX` (at most the square
/// root, below 2^16) is at most 65521 and never one of the three prime markers 65533 to 65535.
/// The bound is reached: 65521^2 is at most `u32::MAX`.
#[test]
fn largest_prime_below_2_16_is_65521() {
    let p = u64::from(LARGEST_PRIME_BELOW_2_16);
    assert!(prime_by_trial(p));
    assert!((p + 1..1 << 16).all(|n| !prime_by_trial(n)));
    assert!(p.pow(2) <= u64::from(u32::MAX));
    const { assert!(LARGEST_PRIME_BELOW_2_16 < PRIME_HELD_BY_TWO) };
}

/// Every entry of the `u16` table reads back as its number's least prime factor, by trial
/// division, up to a `top` with composites whose least prime factor is large (`251^2`,
/// `251 * 257`); and after every value up to `top` is counted twice, every prime's marker is at
/// its last count and still reads as that prime, so each value shares a factor with its copy
/// (except 1).
#[test]
fn the_shared_factor_table_reads_every_least_prime_factor() {
    let top = 251 * 257;
    let lpf = |n: u32| {
        (2..)
            .find(|d| d * d > n || n.is_multiple_of(*d))
            .filter(|d| d * d <= n)
            .unwrap_or(n)
    };
    let table = least_prime_factors(top);
    for x in 2..=top {
        assert_eq!(least_prime_factor(&table, x), lpf(x), "{x}");
    }
    let mut small: Vec<u32> = (1..=top).collect();
    small.extend(1..=top);
    let want: Vec<bool> = small.iter().map(|&v| v > 1).collect();
    assert_eq!(shares_a_factor_by_table(&small, top), want);
    // And each value once, against the pairwise answer, on the values near `top`.
    let near: Vec<u32> = (top - 40..=top).collect();
    assert_eq!(
        shares_a_factor_by_table(&near, top),
        shares_a_factor_by_pairs(&near)
    );
}

/// The table gives the pairwise answer on arithmetic progressions `start + i stride`, with
/// shared and unshared primes, ones, and repeats.
#[test]
fn the_shared_factor_table_agrees_with_the_pairs() {
    for start in 1..7u32 {
        for stride in [0u32, 1, 2, 3, 5, 6, 30, 97, 210] {
            for n in [1u32, 2, 3, 5, 8, 13, 40, 120] {
                let vals: Vec<u32> = (0..n).map(|i| start + i * stride).collect();
                let top = start + (n - 1) * stride;
                assert_eq!(
                    shares_a_factor_by_table(&vals, top),
                    shares_a_factor_by_pairs(&vals),
                    "{vals:?}"
                );
            }
        }
    }
    assert_eq!(shares_a_factor_by_table(&[], 1), Vec::<bool>::new());
}

/// The factors of 0 and 1 are empty (0 has no factorization; `0 >> 0.trailing_zeros()` would
/// shift by 64), and the factors of the largest values are their primes.
#[test]
fn the_factors_at_the_ends_of_u64() {
    assert_eq!(factor(0), []);
    assert_eq!(factor(1), []);
    assert_eq!(factor(2), [(2, 1)]);
    assert_eq!(factor(1 << 63), [(2, 63)]);
    // 2 (2^63 - 1), and 2^63 - 1 = 7^2 * 73 * 127 * 337 * 92737 * 649657.
    assert_eq!(
        factor(u64::MAX - 1),
        [
            (2, 1),
            (7, 2),
            (73, 1),
            (127, 1),
            (337, 1),
            (92_737, 1),
            (649_657, 1)
        ]
    );
    assert!(!is_prime(0) && !is_prime(1) && is_prime(2) && !is_prime(u64::MAX));
    assert!(is_prime(u64::MAX - 58));
}

/// Each documented precondition broken is refused, with its message. A zero modulus is a
/// division by zero, refused in every build with std's message or the crate's; the other
/// checks are `debug_assert!`s, compiled into the dev profile the tests run in, so their tests
/// are compiled there only.
mod refused {
    use super::*;

    #[test]
    #[should_panic(expected = "attempt to calculate the remainder with a divisor of zero")]
    fn a_product_modulo_zero() {
        mul_mod(3, 4, 0);
    }

    #[test]
    #[should_panic(expected = "attempt to calculate the remainder with a divisor of zero")]
    fn a_power_modulo_zero() {
        pow_mod(3, 4, 0);
    }

    #[test]
    #[should_panic(expected = "attempt to calculate the remainder with a divisor of zero")]
    fn a_wide_power_modulo_zero() {
        pow_mod_big(3, &BigUint::from(4u8), 0);
    }

    #[test]
    #[should_panic(expected = "the base of a hash modulo P is below P")]
    fn a_hash_base_of_p() {
        m61::PolyBytes::new(m61::P);
    }

    /// Before TEST-dry-shared-units, `rem_big_u64(0, 0)` gave 0: the fold over no words
    /// divides nothing.
    #[test]
    #[should_panic(expected = "a modulus above 0")]
    fn a_remainder_of_zero_by_zero() {
        rem_big_u64(&BigUint::from(0u8), 0);
    }

    #[test]
    #[should_panic(expected = "a modulus above 0")]
    fn a_remainder_by_zero() {
        rem_big_u64(&BigUint::from(5u8), 0);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "a divisor above 0")]
    fn a_big_gcd_with_zero() {
        gcd_big_u64(&BigUint::from(6u8), 0);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "an odd number")]
    fn an_inverse_of_an_even_number() {
        inverse_mod_2_64(4);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "an odd residue and an odd index")]
    fn a_root_of_an_even_residue() {
        odd_root_mod_2_64(4, 3);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "an odd residue and an odd index")]
    fn a_root_of_an_even_index() {
        odd_root_mod_2_64(3, 4);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "a residue below P and one at most P")]
    fn a_sum_with_p_first() {
        m61::add(m61::P, 0);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "a residue below P and one at most P")]
    fn a_sum_past_p() {
        m61::add(0, m61::P + 1);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "residues below P")]
    fn a_difference_with_p() {
        m61::sub(1, m61::P);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "residues below P")]
    fn a_product_with_the_largest_word() {
        m61::mul(u64::MAX, 2);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "a base below P")]
    fn a_power_of_p() {
        m61::pow_word(m61::P, 2);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "a residue in 1..P")]
    fn an_inverse_of_zero() {
        m61::inv(0);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "a residue in 1..P")]
    fn an_inverse_of_p() {
        m61::inv(m61::P);
    }

    /// Before TEST-dry-shared-units a 0 gave `false` (it shares every prime) and a value past
    /// `top` an index out of bounds.
    #[test]
    #[should_panic(expected = "the value 0 is not in 1..=3")]
    fn a_zero_in_the_shared_factor_table() {
        shares_a_factor_by_table(&[2, 0], 3);
    }

    #[test]
    #[should_panic(expected = "the value 4 is not in 1..=3")]
    fn a_value_past_the_top_of_the_shared_factor_table() {
        shares_a_factor_by_table(&[4], 3);
    }
}

/// Negative controls: for each property test above, a wrong version of its routine (one step
/// dropped or changed) run on that test's inputs, which the test's reference must tell apart
/// from the right one. A control that passed would mean the test's inputs cannot see that
/// mistake.
mod controls {
    use super::*;

    /// Stein's gcd without the common power of two put back: `the_word_gcds_agree_with_euclid`.
    #[test]
    fn a_gcd_that_drops_the_common_twos_is_caught() {
        let wrong = |mut a: u64, mut b: u64| {
            if a == 0 || b == 0 {
                return a | b;
            }
            a >>= a.trailing_zeros();
            loop {
                b >>= b.trailing_zeros();
                if a > b {
                    (a, b) = (b, a);
                }
                b -= a;
                if b == 0 {
                    return a;
                }
            }
        };
        let caught = (0..200u64)
            .flat_map(|a| (0..200u64).map(move |b| (a, b)))
            .filter(|&(a, b)| u128::from(wrong(a, b)) != euclid(a.into(), b.into()))
            .count();
        assert!(caught > 0);
        assert_eq!(wrong(4, 6), 1);
    }

    /// The float estimate of the cube root without the two exact loops: `the_cube_roots_are_exact`
    /// sees it go wrong at some cube or neighbor.
    #[test]
    fn a_cube_root_without_its_correction_is_caught() {
        let wrong = |n: u64| (n as f64).cbrt() as u64;
        let caught = (1..=2_642_245u64)
            .filter(|&k| {
                let c = k * k * k;
                wrong(c - 1) != k - 1 || wrong(c) != k
            })
            .count();
        assert!(caught > 0);
    }

    /// The square filter taken modulo 63 with the residues modulo 64: it turns squares away,
    /// which `the_square_test_is_exact` sees below `2^20`.
    #[test]
    fn a_square_filter_of_the_wrong_modulus_is_caught() {
        let mask = (0..64u64).fold(0u64, |m, i| m | 1 << (i * i % 64));
        let wrong = |v: u128| {
            if mask >> (v % 63) & 1 == 0 {
                return None;
            }
            let s = v.isqrt();
            (s * s == v).then_some(s)
        };
        assert!((0..1u128 << 20).any(|v| wrong(v) != sqrt_exact_u128(v)));
    }

    /// The words of a big integer folded from the least significant, not the most:
    /// `the_big_remainder_and_gcd_by_a_word_agree_with_num_bigint`.
    #[test]
    fn a_remainder_folded_the_wrong_way_is_caught() {
        let wrong = |x: &BigUint, m: u64| {
            let m = u128::from(m);
            x.iter_u64_digits()
                .fold(0u128, |r, d| ((r << 64) | u128::from(d)) % m) as u64
        };
        let mut next = words("a_remainder_folded_the_wrong_way_is_caught");
        let x = (BigUint::from(next()) << 64u32) + next();
        let d = 1_000_003;
        assert_eq!(rem_big_u64(&x, d), u64::try_from(&x % d).unwrap());
        assert_ne!(wrong(&x, d), u64::try_from(&x % d).unwrap(), "{x}");
    }

    /// Squaring over the bits of the exponent from the low bit with the loop of the high bit:
    /// the power by the reversed bits. `products_and_powers_modulo_a_word_agree_with_num_bigint`.
    #[test]
    fn a_power_by_the_reversed_bits_is_caught() {
        let wrong = |a: u64, e: &BigUint, m: u64| {
            let b = a % m;
            let mut r = 1 % m;
            for i in 0..e.bits() {
                r = mul_mod(r, r, m);
                if e.bit(i) {
                    r = mul_mod(r, b, m);
                }
            }
            r
        };
        let (a, e, m) = (3, BigUint::from(6u8), 1_000_003);
        assert_eq!(pow_mod_big(a, &e, m), 729);
        // 6 is 110 in binary; reversed, 011 is 3.
        assert_eq!(wrong(a, &e, m), 27);
    }

    /// Bezout cofactors swapped: `bezout_cofactors_give_the_gcd_and_are_the_least`, whose check
    /// `s a + t b = g` fails for them unless `a = b` up to sign.
    #[test]
    fn swapped_bezout_cofactors_are_caught() {
        let (g, s, t) = bezout_i128(12, 5).unwrap();
        assert_eq!(s * 12 + t * 5, g);
        assert_ne!(t * 12 + s * 5, g);
    }

    /// The Mersenne product without its last subtraction:
    /// `the_mersenne_arithmetic_agrees_with_division`, on random residues.
    #[test]
    fn a_mersenne_product_left_unreduced_is_caught() {
        use m61::P;
        let wrong = |a: u64, b: u64| {
            let x = u128::from(a) * u128::from(b);
            (x as u64 & P) + (x >> 61) as u64
        };
        let mut next = words("a_mersenne_product_left_unreduced_is_caught");
        let xs: Vec<u64> = (0..200).map(|_| next() % P).collect();
        let caught = xs
            .iter()
            .flat_map(|&a| xs.iter().map(move |&b| (a, b)))
            .filter(|&(a, b)| {
                u128::from(wrong(a, b)) != u128::from(a) * u128::from(b) % u128::from(P)
            })
            .count();
        assert!(caught > 0);
    }

    /// The byte hash with the digit `b`, not `b + 1`: `the_eight_byte_hash_is_horners_rule`,
    /// whose all-zero texts then hash to 0 at every length.
    #[test]
    fn a_hash_without_the_offset_digit_is_caught() {
        let b = 0x0f3d_5b79_a2c4_e681;
        let wrong = |bytes: &[u8]| {
            bytes
                .iter()
                .fold(0, |h, &x| m61::add(m61::mul(h, b), u64::from(x)))
        };
        let poly = m61::PolyBytes::new(b);
        for n in 1..=72 {
            assert_ne!(
                poly.hash(&vec![0; n]).0,
                wrong(&vec![0; n]),
                "{n} zero bytes"
            );
        }
    }

    /// The inverse modulo 2^64 with three Newton steps, right in 40 bits only:
    /// `inverses_modulo_2_64_are_inverses`.
    #[test]
    fn an_inverse_one_step_short_is_caught() {
        let wrong = |x: u64| {
            let mut y = x.wrapping_mul(3) ^ 2;
            for _ in 0..3 {
                y = y.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(y)));
            }
            y
        };
        let mut next = words("an_inverse_one_step_short_is_caught");
        assert!((0..1000).any(|_| {
            let x = next() | 1;
            x.wrapping_mul(wrong(x)) != 1
        }));
    }

    /// The odd root with five Newton steps, right in 32 bits only:
    /// `odd_roots_modulo_2_64_are_the_one_odd_root`.
    #[test]
    fn a_root_one_step_short_is_caught() {
        let wrong = |o: u64, p: u64| {
            let mut x = 1u64;
            for _ in 0..5 {
                let y = pow_mod_2_64(x, p - 1);
                let f = y.wrapping_mul(x).wrapping_sub(o);
                x = x.wrapping_sub(f.wrapping_mul(inverse_mod_2_64(y.wrapping_mul(p))));
            }
            x
        };
        let mut next = words("a_root_one_step_short_is_caught");
        assert!((0..300).any(|_| {
            let o = next() | 1;
            pow_mod_2_64(wrong(o, 3), 3) != o
        }));
    }

    /// The segmented sieve with the given order of primes and first multiple: the right one is
    /// `least_prime_factors_in_blocks`, from the greatest prime down and from `p^2`.
    fn sieve(top: u32, block: usize, rising: bool, from_square: bool) -> Vec<u16> {
        let len = top as usize + 1;
        let mut table = vec![0u16; len];
        let r = top.isqrt() as usize;
        let mut primes: Vec<usize> = (2..=r).filter(|&p| prime_by_trial(p as u64)).collect();
        if !rising {
            primes.reverse();
        }
        for lo in (0..len).step_by(block) {
            let hi = (lo + block).min(len);
            for &p in &primes {
                let mut first = lo.div_ceil(p) * p;
                if from_square {
                    first = first.max(p * p);
                }
                for j in (first..hi).step_by(p) {
                    table[j] = p as u16;
                }
            }
            for (j, e) in table[lo..hi].iter_mut().enumerate() {
                if *e == 0 && lo + j >= 2 {
                    *e = PRIME;
                }
            }
        }
        table
    }

    /// `the_least_prime_table_agrees_with_trial_division` and
    /// `the_least_prime_table_does_not_depend_on_the_block_length`: the replica above, with
    /// the right choices, is the crate's table; with the primes rising, 12 ends with 3; with the
    /// first multiple not raised to `p^2`, 2 ends as composite.
    #[test]
    fn a_sieve_in_the_wrong_order_or_from_the_wrong_start_is_caught() {
        for (top, block) in [(1000, 7), (4097, 65), (300_007, 1000)] {
            assert_eq!(
                sieve(top, block, false, true),
                least_prime_factors_in_blocks(top, block)
            );
        }
        let rising = sieve(1000, 7, true, true);
        assert_eq!(rising[12], 3);
        assert_ne!(rising, least_prime_factors(1000));
        let early = sieve(1000, 7, false, false);
        assert_eq!(early[2], 2);
        assert_ne!(early, least_prime_factors(1000));
    }

    /// The odd sieve striking from `q`, not `q^2`, so that each odd prime strikes itself:
    /// `the_odd_sieve_agrees_with_trial_division`.
    #[test]
    fn an_odd_sieve_that_strikes_its_primes_is_caught() {
        let wrong = |n: u64| {
            let len = n.div_ceil(2) as usize;
            let mut prime = vec![true; len];
            if let Some(one) = prime.first_mut() {
                *one = false;
            }
            let mut i = 1;
            while (2 * i + 1) * (2 * i + 1) < 2 * len {
                if prime[i] {
                    let q = 2 * i + 1;
                    for j in (q / 2..len).step_by(q) {
                        prime[j] = false;
                    }
                }
                i += 1;
            }
            prime
        };
        assert!(odd_primes_below(300)[1], "3 is prime");
        assert!(!wrong(300)[1], "the wrong sieve strikes 3");
    }

    /// One Miller-Rabin base used up to 2048 instead of below `psi_1 = 2047`:
    /// `primality_agrees_with_the_sieve_below_psi_3` rejects 2047 = 23 * 89, which the base 2
    /// alone calls a probable prime.
    #[test]
    fn one_base_past_its_bound_is_caught() {
        let n: u64 = 2047;
        let (s, d) = (
            (n - 1).trailing_zeros(),
            (n - 1) >> (n - 1).trailing_zeros(),
        );
        let mut x = pow_mod(2, d, n);
        let strong = x == 1
            || x == n - 1
            || (1..s).any(|_| {
                x = mul_mod(x, x, n);
                x == n - 1
            });
        assert!(strong, "2047 is a strong probable prime to the base 2");
        assert!(!is_prime(n));
    }

    /// The first primes without 2: `the_first_primes_are_the_primes_in_order`.
    #[test]
    fn first_primes_without_two_are_caught() {
        let odd = odd_primes_below(64);
        let wrong: Vec<u64> = (1..odd.len())
            .filter(|&i| odd[i])
            .map(|i| 2 * i as u64 + 1)
            .take(3)
            .collect();
        assert_eq!(first_primes(3), [2, 3, 5]);
        assert_ne!(wrong, first_primes(3));
    }

    /// The pairs reference that skips equal values, against the table:
    /// `the_shared_factor_table_agrees_with_the_pairs`, whose stride 0 repeats a value.
    #[test]
    fn shared_factors_that_ignore_repeats_are_caught() {
        let vals = [4, 4, 9];
        let wrong: Vec<bool> = (0..vals.len())
            .map(|i| {
                (0..vals.len())
                    .any(|j| vals[j] != vals[i] && gcd_u64(vals[i].into(), vals[j].into()) != 1)
            })
            .collect();
        assert_eq!(shares_a_factor_by_table(&vals, 9), [true, true, false]);
        assert_eq!(shares_a_factor_by_pairs(&vals), [true, true, false]);
        assert_ne!(wrong, shares_a_factor_by_pairs(&vals));
    }
}

/// `coprime_base_u64` gives `cb S`: elements above 1, distinct and pairwise coprime; each
/// input's pairs by increasing element, each `k >= 1`, rebuilding the input; and the
/// elements are the classes of primes by proportional exponent vectors over the inputs
/// (two primes are in one element of `cb S` exactly when their vectors are proportional, the
/// definition the zed-kernel tests use), checked through `factor`: the primes of one element
/// have proportional vectors, and those of two elements do not. On every pair and triple of
/// 1 to 40, the edge words, and random lists of products of small primes and random words.
#[test]
fn the_word_coprime_base_is_natural() {
    fn natural(xs: &[u64]) {
        let (base, ks) = coprime_base_u64(xs);
        for (i, &a) in base.iter().enumerate() {
            assert!(a > 1, "{xs:?}: {base:?}");
            for &b in &base[i + 1..] {
                assert_eq!(gcd_u64(a, b), 1, "{xs:?}: {base:?}");
            }
        }
        assert_eq!(ks.len(), xs.len());
        for (&x, k) in xs.iter().zip(&ks) {
            assert!(k.windows(2).all(|w| w[0].0 < w[1].0), "{x}: {k:?}");
            let mut prod = 1u128;
            for &(e, m) in k {
                assert!(m >= 1);
                prod *= u128::from(base[e as usize]).pow(u32::try_from(m).expect("below 64"));
            }
            assert_eq!(prod, u128::from(x), "{xs:?}: {base:?} {k:?}");
        }
        // The exponent vector of each prime over the inputs, divided by the gcd of its entries.
        let primitive = |p: u64| -> Vec<u64> {
            let v: Vec<u64> = (xs.iter())
                .map(|&x| {
                    let (mut x, mut e) = (x, 0);
                    while x.is_multiple_of(p) {
                        x /= p;
                        e += 1;
                    }
                    e
                })
                .collect();
            let g = v.iter().fold(0, |g, &e| gcd_u64(g, e));
            v.iter().map(|e| e / g).collect()
        };
        let classes: Vec<Vec<Vec<u64>>> = (base.iter())
            .map(|&c| factor(c).into_iter().map(|(p, _)| primitive(p)).collect())
            .collect();
        for (i, c) in classes.iter().enumerate() {
            assert!(c.windows(2).all(|w| w[0] == w[1]), "{xs:?}: {base:?}");
            for d in &classes[i + 1..] {
                assert_ne!(c[0], d[0], "{xs:?}: {base:?}");
            }
        }
    }
    natural(&[]);
    natural(&[1]);
    for a in 1..=40u64 {
        for b in 1..=40u64 {
            natural(&[a, b]);
            for c in [1u64, 2, 6, 9, 12, 27, 30, 36] {
                natural(&[a, b, c]);
            }
        }
    }
    let edges: Vec<u64> = EDGES.iter().copied().filter(|&e| e > 0).collect();
    natural(&edges);
    natural(&[
        4_294_967_291u64 * 4_294_967_291,
        4_294_967_291,
        2 * 4_294_967_291,
    ]);
    natural(&[1 << 63, 1 << 62, 4, 8, 3 << 61]);
    natural(&[3u64.pow(40), 9, 3u64.pow(40), 1]);
    let mut next = words("the_word_coprime_base_is_natural");
    let smalls = [2u64, 3, 5, 7, 11, 13];
    for _ in 0..2000 {
        let k = 1 + next() % 12;
        let xs: Vec<u64> = (0..k)
            .map(|_| match next() % 4 {
                0 => next() | 1,
                1 => (next() >> 4) * smalls[(next() % 6) as usize],
                // A product of small prime powers, each at most 13^5; a factor that would
                // pass 2^64 is left out.
                _ => (0..next() % 6).fold(1u64, |w, _| {
                    let q = smalls[(next() % 6) as usize].pow(1 + (next() % 5) as u32);
                    w.checked_mul(q).unwrap_or(w)
                }),
            })
            .collect();
        natural(&xs);
    }
}

#[test]
#[should_panic(expected = "a coprime base of positive integers, given 0")]
fn the_word_coprime_base_refuses_0() {
    coprime_base_u64(&[6, 0]);
}

/// Each input's `(element, multiplicity)` list as `(element value, multiplicity)`, sorted, and
/// the elements sorted: the two paths may number the elements differently.
fn by_value(base: &[u64], ks: &[Vec<(u32, u64)>]) -> (Vec<u64>, Vec<Vec<(u64, u64)>>) {
    let mut elements = base.to_vec();
    elements.sort_unstable();
    let ks = (ks.iter())
        .map(|k| {
            let mut k: Vec<(u64, u64)> = k.iter().map(|&(e, m)| (base[e as usize], m)).collect();
            k.sort_unstable();
            k
        })
        .collect();
    (elements, ks)
}

/// Random word lists of `1..=most` inputs: random odd words, words with a small prime, products
/// of small prime powers, products of two primes near 2^20 and 2^32 and their powers, and
/// primes past 2^24, so that many inputs share a prime.
fn word_lists(test: &str, rounds: usize, most: u64) -> Vec<Vec<u64>> {
    let mut next = words(test);
    let smalls = [2u64, 3, 5, 7, 11, 13];
    let mids = [1_048_573u64, 1_048_583, 1_048_589, 16_777_259, 16_777_289];
    let wides = [4_294_967_291u64, 4_294_967_279];
    (0..rounds)
        .map(|_| {
            let k = 1 + next() % most;
            (0..k)
                .map(|_| match next() % 6 {
                    0 => next() | 1,
                    1 => (next() >> 4) * smalls[(next() % 6) as usize],
                    2 => mids[(next() % 5) as usize] * mids[(next() % 5) as usize],
                    3 => wides[(next() % 2) as usize] * wides[(next() % 2) as usize],
                    // A cube of a prime near 2^24 would pass 2^64; the prime is taken then.
                    4 => {
                        let m = mids[(next() % 5) as usize];
                        m.checked_pow(1 + (next() % 3) as u32).unwrap_or(m)
                    }
                    _ => (0..next() % 6).fold(1u64, |w, _| {
                        let q = smalls[(next() % 6) as usize].pow(1 + (next() % 5) as u32);
                        w.checked_mul(q).unwrap_or(w)
                    }),
                })
                .collect()
        })
        .collect()
}

/// `coprime_base_by_factoring` gives the elements and multiplicities of `coprime_base_u64`,
/// which `the_word_coprime_base_is_natural` holds to the definition, so the same `cb S`: on
/// every pair and triple of 1 to 40 with small third inputs, the edge words, wide powers and
/// products of two primes near 2^32, and random lists of up to 40 inputs.
#[test]
fn the_factored_coprime_base_is_natural() {
    fn same(xs: &[u64]) {
        let (fb, fk) = coprime_base_by_factoring(xs);
        let (rb, rk) = coprime_base_u64(xs);
        assert_eq!(by_value(&fb, &fk), by_value(&rb, &rk), "{xs:?}");
        for k in &fk {
            assert!(k.windows(2).all(|w| w[0].0 < w[1].0), "{xs:?}: {fk:?}");
        }
    }
    same(&[]);
    same(&[1]);
    for a in 1..=40u64 {
        for b in 1..=40u64 {
            same(&[a, b]);
            for c in [1u64, 2, 6, 9, 12, 27, 30, 36] {
                same(&[a, b, c]);
            }
        }
    }
    let edges: Vec<u64> = EDGES.iter().copied().filter(|&e| e > 0).collect();
    same(&edges);
    same(&[
        4_294_967_291u64 * 4_294_967_291,
        4_294_967_291,
        2 * 4_294_967_291,
    ]);
    same(&[1 << 63, 1 << 62, 4, 8, 3 << 61]);
    same(&[3u64.pow(40), 9, 3u64.pow(40), 1]);
    // 36 = 2^2 3^2 and 1296 = 2^4 3^4: both primes have the vector (2, 4), `l` 2 and
    // `w` (1, 2), so one element 2^2 3^2 = 36, with 1296 = 36^2. 12 = 2^2 3 and 144 = 2^4 3^2:
    // vectors (2, 4) and (1, 2), the same `w` (1, 2) with `l` 2 and 1, so one element
    // 2^2 3 = 12, with 144 = 12^2.
    same(&[36, 1296]);
    same(&[12, 144]);
    for xs in word_lists("the_factored_coprime_base_is_natural", 2000, 40) {
        same(&xs);
    }
}

#[test]
#[should_panic(expected = "a coprime base of positive integers, given 0")]
fn the_factored_coprime_base_refuses_0() {
    coprime_base_by_factoring(&[6, 0]);
}

/// `shares_a_factor_by_factoring` is the definition, a gcd above 1 with another input, on the
/// lists of `the_factored_coprime_base_is_natural`, equal inputs and ones.
#[test]
fn the_factored_shares_agree_with_pairwise_gcds() {
    fn same(xs: &[u64]) {
        let want: Vec<bool> = (0..xs.len())
            .map(|i| (0..xs.len()).any(|j| j != i && gcd_u64(xs[i], xs[j]) > 1))
            .collect();
        assert_eq!(shares_a_factor_by_factoring(xs), want, "{xs:?}");
    }
    same(&[]);
    same(&[1]);
    same(&[1, 1]);
    same(&[7, 7]);
    same(&[7, 1, 7]);
    same(&[6, 35, 11]);
    for a in 1..=40u64 {
        for b in 1..=40u64 {
            for c in [1u64, 2, 6, 9, 35, 37] {
                same(&[a, b, c]);
            }
        }
    }
    for xs in word_lists("the_factored_shares_agree_with_pairwise_gcds", 2000, 40) {
        same(&xs);
    }
}

/// `log2_bounds(x, k)` holds `2^k log2(x)` between its ends, checked exactly as `2^lo <=
/// x^(2^k) <= 2^hi`, with `hi - lo` 1 or 2: for 1, powers of 2 (where `lo` is exact) and
/// their neighbors, small primes, values of more bits than `q = k + 8` (so the first shift
/// rounds), and random words, at `k` from 0 to 10; and at `k = 64` against `f64` for words.
#[test]
fn log2_bounds_hold_and_are_tight() {
    let mut xs: Vec<BigUint> = [1u64, 2, 3, 5, 7, 255, 256, 257, 1 << 40, (1 << 40) - 1]
        .into_iter()
        .map(BigUint::from)
        .collect();
    xs.push((BigUint::from(1u32) << 300u32) + 1u32);
    xs.push((BigUint::from(1u32) << 301u32) - 1u32);
    xs.push(BigUint::from(3u32).pow(200));
    let mut w = words("log2_bounds_hold_and_are_tight");
    for _ in 0..40 {
        xs.push(BigUint::from(w() >> (w() % 64)) + 1u32);
    }
    for x in &xs {
        for k in 0..=10u32 {
            let (lo, hi) = log2_bounds(x, k);
            let width = &hi - &lo;
            assert!(
                width == BigUint::from(1u32) || width == BigUint::from(2u32),
                "{x} at {k}: {lo}..{hi}"
            );
            let p = x.pow(1u32 << k);
            let lo_u = u64::try_from(&lo).expect("a small bound");
            let hi_u = u64::try_from(&hi).expect("a small bound");
            assert!(BigUint::from(1u32) << lo_u <= p, "{x} at {k}: low end {lo}");
            assert!(
                p <= BigUint::from(1u32) << hi_u,
                "{x} at {k}: high end {hi}"
            );
            if x.count_ones() == 1 {
                assert_eq!(lo, BigUint::from(x.bits() - 1) << k, "{x} at {k}");
            }
        }
    }
    for x in xs.iter().filter(|x| x.bits() <= 53) {
        let (lo, hi) = log2_bounds(x, 64);
        let f = (u64::try_from(x).expect("a word") as f64).log2();
        let scale = 2f64.powi(64);
        let (lo_f, hi_f) = (
            lo.to_string().parse::<f64>().expect("a number") / scale,
            hi.to_string().parse::<f64>().expect("a number") / scale,
        );
        assert!(
            lo_f <= f + 1e-12 && f - 1e-12 <= hi_f,
            "{x}: {lo_f}..{hi_f} against {f}"
        );
    }
}

/// `inverse_mod_u64` against its definition: for every `a < m <= 40`, the least `x` with
/// `a x = 1 (mod m)` by a scan (moved from zed-kernel's `types::empty` test, whose copy it
/// replaced), so `None` exactly when `gcd(a, m) > 1` and `Some(0)` modulo 1; then at the edge
/// words, with random `a` and `m`, against `a x mod m = 1` and `x < m` when it gives one and
/// against `gcd(a, m) > 1` when it does not; and for a prime `m` against Fermat's `a^(m - 2)`,
/// the copies of `siqs` and zed-kernel's `num::fast` it replaced.
#[test]
fn inverses_modulo_a_word() {
    for m in 1..=40u64 {
        for a in 0..m + 3 {
            let scanned = (0..m).find(|&x| a * x % m == 1 % m);
            assert_eq!(
                inverse_mod_u64(a, m),
                scanned,
                "the inverse of {a} modulo {m}"
            );
        }
    }
    let mut next = words("inverses_modulo_a_word");
    let mut ms: Vec<u64> = EDGES.iter().copied().filter(|&m| m > 0).collect();
    ms.extend((0..300).map(|_| next() | 1));
    ms.extend((0..300).map(|_| next() >> (next() % 64)).filter(|&m| m > 0));
    let mut found = 0;
    for &m in &ms {
        let mut aa: Vec<u64> = EDGES.to_vec();
        aa.extend([m - 1, m / 2, m.wrapping_add(1)]);
        aa.extend((0..20).map(|_| next()));
        for &a in &aa {
            match inverse_mod_u64(a, m) {
                Some(x) => {
                    found += 1;
                    assert!(x < m, "{a}^-1 mod {m} = {x}");
                    assert_eq!(mul_mod(a, x, m), 1 % m, "{a}^-1 mod {m} = {x}");
                }
                None => assert!(gcd_u64(a, m) > 1, "{a} mod {m} has no inverse"),
            }
        }
    }
    assert!(found > 1000, "{found} inverses found");
    for m in [2, 3, 5, 65_537, (1 << 61) - 1, 18_446_744_073_709_551_557] {
        for a in [1, 2, m - 1, m / 2, next() % m]
            .into_iter()
            .filter(|&a| a % m != 0)
        {
            assert_eq!(
                inverse_mod_u64(a, m),
                Some(pow_mod(a, m - 2, m)),
                "{a} mod {m}"
            );
        }
    }
}

/// `inverse_mod_2_128` at the edges and on random odd numbers: `x y = 1 (mod 2^128)`.
#[test]
fn inverses_modulo_2_128_are_inverses() {
    let mut next = words("inverses_modulo_2_128_are_inverses");
    let mut xs: Vec<u128> = vec![
        1,
        3,
        u128::MAX,
        u128::MAX - 2,
        (1 << 127) + 1,
        (1 << 64) + 1,
    ];
    xs.extend((0..10_000).map(|_| (u128::from(next()) << 64 | u128::from(next())) | 1));
    for x in xs {
        assert_eq!(x.wrapping_mul(inverse_mod_2_128(x)), 1, "{x}");
    }
}

/// `add_mod` and `mul_add_mod` against 128-bit arithmetic, at the edge words (operands at and
/// above the modulus among them, as the sumset of zedc-presburger passes `b = m`) and on random
/// ones.
#[test]
fn sums_and_products_modulo_a_word_agree_with_128_bits() {
    let mut next = words("sums_and_products_modulo_a_word_agree_with_128_bits");
    let mut xs: Vec<u64> = EDGES.to_vec();
    xs.extend((0..30).map(|_| next()));
    for &m in xs.iter().filter(|&&m| m > 0) {
        for &a in &xs {
            for &b in &xs[..20] {
                let (a1, b1, m1) = (u128::from(a), u128::from(b), u128::from(m));
                assert_eq!(
                    u128::from(add_mod(a, b, m)),
                    (a1 + b1) % m1,
                    "{a} + {b} mod {m}"
                );
                assert_eq!(u128::from(add_mod(a, m, m)), a1 % m1, "{a} + {m} mod {m}");
                assert_eq!(
                    u128::from(mul_add_mod(a, b, a, m)),
                    (a1 * b1 + a1) % m1,
                    "{a} {b} + {a} mod {m}"
                );
            }
        }
    }
}

mod m64_59 {
    use crate::m64_59::{P, add, mul};

    /// `P` is prime, so `0..P` is a field and the values of the treaps' priority polynomials at
    /// distinct points are independent (the module comment of `zed_collections::priority`), and
    /// it is the largest prime below `2^64`, as its doc says. Red when `P` is changed to
    /// `2^64 - 57` (composite) or to `2^64 - 83` (a smaller prime): checked 2026-11-19, in
    /// zed-kernel, before the move.
    #[test]
    fn p_is_the_largest_prime_below_2_to_the_64() {
        assert!(crate::is_prime(P));
        for n in P + 1..=u64::MAX {
            assert!(!crate::is_prime(n), "{n} is prime");
        }
    }

    #[test]
    fn the_field_operations_agree_with_division_by_p() {
        let p = u128::from(P);
        // P - 60 times P - 1 or P - 2 makes the second fold of the product carry
        // past 2^64: a reduction that folds the high word twice in 64-bit
        // arithmetic and drops that carry gives a wrong product there, and on no
        // other pair of this test (found by the cross-review XR-xor-shape-round-7-high).
        let edges = [
            0,
            1,
            2,
            58,
            59,
            60,
            P - 60,
            P - 2,
            P - 1,
            1 << 32,
            (1 << 63) + 5,
        ];
        let mut rng = crate::seed::Rng::new(1);
        let mut values: Vec<u64> = edges.to_vec();
        for _ in 0..2000 {
            values.push(rng.below_u64(P));
        }
        for &a in &values {
            for &b in &values[..40] {
                assert_eq!(
                    u128::from(mul(a, b)),
                    u128::from(a) * u128::from(b) % p,
                    "{a} * {b}"
                );
                assert_eq!(
                    u128::from(add(a, b)),
                    (u128::from(a) + u128::from(b)) % p,
                    "{a} + {b}"
                );
            }
        }
    }
}

/// `prime_powers` and `divisors` (moved from zed-kernel `types/empty.rs`,
/// DRY-bignum-crate-2026-11-26) against trial division, for 0 to 5,000, the highly composite
/// 720720 (240 divisors), a prime power, and a 64-bit prime and semiprime, whose divisors are
/// checked by their product of prime powers.
#[test]
fn prime_powers_and_divisors_agree_with_trial_division() {
    for n in 0u64..=5000 {
        let mut want = Vec::new();
        let mut m = n;
        let mut p = 2;
        while n > 1 && p * p <= m {
            if m % p == 0 {
                let mut q = 1;
                while m % p == 0 {
                    m /= p;
                    q *= p;
                }
                want.push((p, q));
            }
            p += 1;
        }
        if n > 1 && m > 1 {
            want.push((m, m));
        }
        assert_eq!(crate::prime_powers(n), want, "{n}");
        if n > 0 {
            let all: Vec<u64> = (1..=n).filter(|d| n % d == 0).collect();
            assert_eq!(crate::divisors(n), all, "{n}");
        }
    }
    assert_eq!(crate::divisors(720_720).len(), 240);
    assert_eq!(crate::prime_powers(3u64.pow(40)), vec![(3, 3u64.pow(40))]);
    let prime = 18_446_744_073_709_551_557u64;
    assert_eq!(crate::prime_powers(prime), vec![(prime, prime)]);
    assert_eq!(crate::divisors(prime), vec![1, prime]);
    let semi = 4_294_967_291u64 * 4_294_967_279;
    assert_eq!(
        crate::divisors(semi),
        vec![1, 4_294_967_279, 4_294_967_291, semi]
    );
}

/// The floor sums ([`floor_sum`], [`floor_sum_i128`]) against the sum itself and against the
/// AtCoder Library's form, the plan row FLOORSUM-bits's tests.
mod floor_sums {
    use num_bigint::BigInt;

    use crate::{floor_sum, floor_sum_i128};

    /// The AtCoder Library's form of the floor sum, which `floor_sum` had before FLOORSUM-bits
    /// (moved from zedc-affine's `lines::floor_sum`): the oracle for numbers too large to sum
    /// term by term.
    fn atcoder(n: &BigInt, m: &BigInt, a: &BigInt, b: &BigInt) -> BigInt {
        use num_integer::Integer;
        let (mut n, mut m) = (n.clone(), m.clone());
        let pairs = |n: &BigInt| (n * &(n - 1u32)) >> 1u32;
        let (q, mut a) = a.div_mod_floor(&m);
        let mut ans = &pairs(&n) * &q;
        let (q, mut b) = b.div_mod_floor(&m);
        ans += &n * &q;
        loop {
            if a >= m {
                let (q, r) = a.div_mod_floor(&m);
                ans += &pairs(&n) * &q;
                a = r;
            }
            if b >= m {
                let (q, r) = b.div_mod_floor(&m);
                ans += &n * &q;
                b = r;
            }
            let top = &(&a * &n) + &b;
            if top < m {
                return ans;
            }
            (n, b) = top.div_mod_floor(&m);
            std::mem::swap(&mut m, &mut a);
        }
    }

    /// Both forms on `(n, m, a, b)` against `want`.
    fn both(n: i64, m: i64, a: i64, b: i64, want: i64, seed: u64) {
        let big = |x: i64| BigInt::from(x);
        assert_eq!(
            floor_sum(&big(n), &big(m), &big(a), &big(b)),
            big(want),
            "seed {seed}: n {n} m {m} a {a} b {b}"
        );
        assert_eq!(
            floor_sum_i128(n.into(), m.into(), a.into(), b.into()),
            Some(want.into()),
            "seed {seed}: n {n} m {m} a {a} b {b}"
        );
    }

    /// The sum term by term.
    fn brute(n: i64, m: i64, a: i64, b: i64) -> i64 {
        (0..n).map(|i| (a * i + b).div_euclid(m)).sum()
    }

    /// Every `n` in 0..12, `m` in 1..7 and `a`, `b` in -9..9: the corner cases `n = 0`, `a = 0`,
    /// `b >= m`, `a >= m`, `m = 1` and negative `a` or `b` (the caller's contract: either sign)
    /// are among them.
    #[test]
    fn the_floor_sums_match_the_sum_on_every_small_case() {
        for n in 0..12 {
            for m in 1..7 {
                for a in -9..9 {
                    for b in -9..9 {
                        both(n, m, a, b, brute(n, m, a, b), 0);
                    }
                }
            }
        }
    }

    /// 20000 random `(n, m, a, b)` with `m` in 1..=60, `n` in 0..=90 and `a`, `b` in
    /// -1000..=1000.
    #[test]
    fn the_floor_sums_match_the_sum_on_random_cases() {
        let (mut rng, seed) =
            crate::seed::Rng::fresh("the_floor_sums_match_the_sum_on_random_cases");
        for _ in 0..20_000 {
            let (n, m) = (rng.int(0, 90), rng.int(1, 60));
            let (a, b) = (rng.int(-1000, 1000), rng.int(-1000, 1000));
            both(n, m, a, b, brute(n, m, a, b), seed);
        }
    }

    /// A random number of `digits` decimal digits, the first not 0, of either sign when
    /// `signed`.
    fn digits(rng: &mut crate::seed::Rng, digits: usize, signed: bool) -> BigInt {
        let mut s: String = (0..digits)
            .map(|k| char::from(b'0' + rng.int(i64::from(k == 0), 9) as u8))
            .collect();
        if signed && rng.int(0, 1) == 1 {
            s.insert(0, '-');
        }
        s.parse().expect("decimal digits")
    }

    /// 300 random `(n, m, a, b)` of 10 to 300 digits each, `a` and `b` of either sign, against
    /// the AtCoder Library's form; `floor_sum_i128` either refuses them or agrees.
    #[test]
    fn the_floor_sum_matches_the_atcoder_form_on_numbers_of_10_to_300_digits() {
        let (mut rng, seed) = crate::seed::Rng::fresh(
            "the_floor_sum_matches_the_atcoder_form_on_numbers_of_10_to_300_digits",
        );
        for _ in 0..300 {
            let mut size = || rng.int(10, 300) as usize;
            let (dn, dm, da, db) = (size(), size(), size(), size());
            let n = digits(&mut rng, dn, false);
            let m = digits(&mut rng, dm, false);
            let a = digits(&mut rng, da, true);
            let b = digits(&mut rng, db, true);
            let want = atcoder(&n, &m, &a, &b);
            assert_eq!(
                floor_sum(&n, &m, &a, &b),
                want,
                "seed {seed}: n {n} m {m} a {a} b {b}"
            );
        }
    }

    /// Near the ends of `i128`: `floor_sum_i128` gives `None` when a step overflows, and
    /// otherwise the sum, which `floor_sum` gives too. The sums: `n (n − 1) / 2 · 2^64` is
    /// about 2^191; `pairs(MAX)` overflows; `6 · MIN` overflows; `n = 0` sums nothing; the one
    /// term `⌊MAX / MAX⌋` is 1; the two terms `⌊2^100 / 2^100⌋` and
    /// `⌊(2^101 − 1) / 2^100⌋` are 1 each.
    #[test]
    fn the_word_floor_sum_refuses_an_overflow_and_agrees_where_it_fits() {
        let (top, low) = (i128::MAX, i128::MIN);
        let cases = [
            (1 << 64, 1, 1 << 64, 0, None),
            (top, 1, top, top, None),
            (3, 1, low, low, None),
            (0, 7, top, top, Some(0)),
            (1, top, top - 1, top, Some(1)),
            (2, 1 << 100, (1 << 100) - 1, 1 << 100, Some(2)),
        ];
        for (n, m, a, b, want) in cases {
            assert_eq!(floor_sum_i128(n, m, a, b), want, "n {n} m {m} a {a} b {b}");
            let big = |x: i128| BigInt::from(x);
            let sum = floor_sum(&big(n), &big(m), &big(a), &big(b));
            // Each refused case has `m = 1`, whose sum is `a n (n − 1) / 2 + b n`.
            let exact = match want {
                Some(w) => big(w),
                None => big(a) * big(n) * (big(n) - 1) / 2 + big(b) * big(n),
            };
            assert_eq!(sum, exact, "n {n} m {m} a {a} b {b}");
        }
    }
}
