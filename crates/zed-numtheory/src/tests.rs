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
}
