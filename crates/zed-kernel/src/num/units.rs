//! Direct tests of the integer routines other crates call through `num` (TEST-dry-shared-units,
//! for DRY-numeric-shared and DRY-number-theory): [`div_rem_uint`], [`rem_uint`],
//! [`div_floor_int`], [`mod_floor_int`], [`gcd_uint`], [`inverse_mod_uint`] and [`bezout_int`],
//! each against num-bigint and num-integer on the ends (0, 1, a word, `u64::MAX`, the
//! `DIV_LEAF` width on both sides of it, odd parts of 64 and 65 bits), on random operands with
//! a printed seed (`ZED_TEST_SEED` repeats a run), and with a negative control: a routine with
//! one known mistake that the same check must catch, so that a check that holds for anything
//! is caught too.

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Zero};

use super::{bezout_int, div_floor_int, div_rem_uint, gcd_uint, inverse_mod_uint, mod_floor_int};
use super::{rem_uint, trees};
use crate::seed::Rng;

/// `DIV_LEAF` in words: divisors at or below it go to num-bigint's division.
const LEAF_WORDS: usize = (super::fast::crossover::DIV_LEAF / 64) as usize;

/// A number of `words` random 64-bit words, its top word not zero.
fn wide(rng: &mut Rng, words: usize) -> BigUint {
    let mut ds: Vec<u64> = (0..words).map(|_| rng.next_u64()).collect();
    if let Some(top) = ds.last_mut() {
        *top |= 1 << 63;
    }
    BigUint::from_slice(
        &ds.iter()
            .flat_map(|&d| [d as u32, (d >> 32) as u32])
            .collect::<Vec<_>>(),
    )
}

/// The ends: 0, 1, 2, a word less one, a word, past a word, and powers of two.
fn ends() -> Vec<BigUint> {
    let one = BigUint::one();
    vec![
        BigUint::zero(),
        one.clone(),
        BigUint::from(2u32),
        BigUint::from(u64::MAX),
        &one << 64u32,
        (&one << 64u32) + 1u32,
        &one << 128u32,
        (&one << 4096u32) - 1u32,
        &one << 4096u32,
    ]
}

/// The widths, in words, on both sides of the leaf and of a word.
fn widths() -> Vec<usize> {
    vec![
        1,
        2,
        LEAF_WORDS - 1,
        LEAF_WORDS,
        LEAF_WORDS + 1,
        3 * LEAF_WORDS,
    ]
}

/// Floor division and its remainder agree with num-integer on every sign of the ends and of
/// random operands of every width pair, the dividend from a word to five times the divisor
/// (the reciprocal and the block paths of `fast::div_rem` and `fast::rem`).
#[test]
fn floor_division_agrees_with_num_integer() {
    let (mut rng, _) = Rng::fresh("floor_division_agrees_with_num_integer");
    let mut pairs: Vec<(BigUint, BigUint)> = Vec::new();
    for a in ends() {
        for m in ends().into_iter().filter(|m| !m.is_zero()) {
            pairs.push((a.clone(), m));
        }
    }
    for &mw in &widths() {
        for aw in [1, mw, 2 * mw + 1, 5 * mw] {
            let (a, m) = (wide(&mut rng, aw), wide(&mut rng, mw));
            // An exact multiple too, where the floor of opposite signs is the negated quotient.
            pairs.push((&a * &m, m.clone()));
            pairs.push((a, m));
        }
    }
    for (a, m) in &pairs {
        let (q, r) = div_rem_uint(a, m);
        assert_eq!(
            (&q, &r),
            (&(a / m), &(a % m)),
            "{} by {} bits",
            a.bits(),
            m.bits()
        );
        assert_eq!(rem_uint(a, m), r);
        let (a, m) = (BigInt::from(a.clone()), BigInt::from(m.clone()));
        for (a, m) in [(&a, &m), (&-&a, &m), (&a, &-&m), (&-&a, &-&m)] {
            let want = (Integer::div_floor(a, m), Integer::mod_floor(a, m));
            assert_eq!((div_floor_int(a, m), mod_floor_int(a, m)), want);
        }
    }
}

/// The floor's definition, checked on its own: `a = m q + r` with `r` of the sign of `m` and
/// below it in magnitude. The negative control: truncation (num-bigint's `/`) passes the same
/// check on operands of one sign and fails it on `-7` by `2`.
#[test]
fn the_floor_meets_its_definition_and_truncation_does_not() {
    fn meets(a: &BigInt, m: &BigInt, q: &BigInt, r: &BigInt) -> bool {
        let below = r.magnitude() < m.magnitude();
        let signed = r.is_zero() || (r.sign() == m.sign());
        *a == m * q + r && below && signed
    }
    for a in -40i64..=40 {
        for m in [-9i64, -2, -1, 1, 2, 9] {
            let (a, m) = (BigInt::from(a), BigInt::from(m));
            let (q, r) = (div_floor_int(&a, &m), mod_floor_int(&a, &m));
            assert!(meets(&a, &m, &q, &r), "{a} by {m}: {q} {r}");
        }
    }
    let (a, m) = (BigInt::from(-7), BigInt::from(2));
    let (q, r) = (&a / &m, &a % &m);
    assert!(meets(&-&a, &m, &(-&a / &m), &(-&a % &m)));
    assert!(!meets(&a, &m, &q, &r), "truncation gives {q} {r}");
}

/// A divisor of 0 breaks the stated precondition of each division, and each says so with one
/// message, whichever path it takes (`fast::rem` sends a narrow divisor to num-bigint).
mod refused {
    use super::*;

    #[test]
    #[should_panic(expected = "a division by zero")]
    fn div_rem_uint_by_zero() {
        div_rem_uint(&BigUint::from(5u32), &BigUint::zero());
    }

    #[test]
    #[should_panic(expected = "a division by zero")]
    fn rem_uint_by_zero() {
        rem_uint(&BigUint::from(5u32), &BigUint::zero());
    }

    #[test]
    #[should_panic(expected = "a division by zero")]
    fn div_floor_int_by_zero() {
        div_floor_int(&BigInt::from(-5), &BigInt::zero());
    }

    #[test]
    #[should_panic(expected = "a division by zero")]
    fn mod_floor_int_by_zero() {
        mod_floor_int(&BigInt::from(-5), &BigInt::zero());
    }

    /// The remainders of a product tree with a leaf 0: its product is 0, and the division by it
    /// is refused with the same message.
    #[test]
    #[should_panic(expected = "a division by zero")]
    fn remainders_by_a_leaf_of_zero() {
        let leaves = [BigUint::from(3u32), BigUint::zero()];
        let levels = trees::product_tree(&leaves);
        trees::remainders(&BigUint::from(7u32), &leaves, &levels);
    }

    /// Modulo 0 the ring is the integers, where 1 is its own inverse; the old `None` for every
    /// `a` was wrong for `a = 1`, so a modulus of 0 is refused.
    #[test]
    #[should_panic(expected = "a modulus above 0")]
    fn an_inverse_mod_zero() {
        inverse_mod_uint(&BigUint::one(), &BigUint::zero());
    }
}

/// `gcd_uint` agrees with num-integer on the ends, on odd parts of 64 and 65 bits under every
/// shift (both sides of its one-word path), on equal odd parts under unequal shifts, and on
/// random pairs of every width pair with and without a common factor.
#[test]
fn gcd_agrees_with_num_integer() {
    let (mut rng, _) = Rng::fresh("gcd_agrees_with_num_integer");
    let mut pairs: Vec<(BigUint, BigUint)> = Vec::new();
    for a in ends() {
        for b in ends() {
            pairs.push((a.clone(), b));
        }
    }
    let odd64 = BigUint::from(u64::MAX - 2);
    let odd65 = (BigUint::one() << 64u32) + 3u32;
    for s in [0u32, 1, 63, 64, 65, 200] {
        for t in [0u32, 5, 64] {
            pairs.push((&odd64 << s, &odd65 << t));
            pairs.push((&odd65 << s, &odd65 << t));
            pairs.push((&odd64 << s, (&odd64 * 3u32) << t));
        }
    }
    for &aw in &widths() {
        for bw in [1, aw, 2 * aw] {
            let (a, b, c) = (wide(&mut rng, aw), wide(&mut rng, bw), wide(&mut rng, 2));
            pairs.push((&a * &c, &b * &c));
            pairs.push((a, b));
        }
    }
    for (a, b) in &pairs {
        assert_eq!(
            gcd_uint(a, b),
            a.gcd(b),
            "{} and {} bits",
            a.bits(),
            b.bits()
        );
    }
}

/// The negative control of `gcd_agrees_with_num_integer`: a gcd of the odd parts alone, the
/// shared power of two left out, agrees on odd pairs and is caught on `4` and `6`.
#[test]
fn a_gcd_without_the_shared_power_of_two_is_caught() {
    let wrong = |a: &BigUint, b: &BigUint| {
        let odd = |x: &BigUint| x >> x.trailing_zeros().unwrap_or(0);
        odd(a).gcd(&odd(b))
    };
    let (a, b) = (BigUint::from(9u32), BigUint::from(15u32));
    assert_eq!(wrong(&a, &b), gcd_uint(&a, &b));
    let (a, b) = (BigUint::from(4u32), BigUint::from(6u32));
    assert_ne!(wrong(&a, &b), gcd_uint(&a, &b));
}

/// `inverse_mod_uint` meets its definition, `a x = 1 mod m` with `x < m`, exactly when
/// `gcd(a, m) = 1`, for odd, even and power-of-two moduli and `m = 1` (where every `a` has
/// the inverse 0), on the ends and on random operands of every width, `a` wider than `m` too.
#[test]
fn inverses_meet_their_definition() {
    let (mut rng, _) = Rng::fresh("inverses_meet_their_definition");
    let mut moduli: Vec<BigUint> = ends().into_iter().filter(|m| !m.is_zero()).collect();
    for &w in &widths() {
        let m = wide(&mut rng, w);
        moduli.push(&m | BigUint::one());
        moduli.push(&m >> 1u32 << 1u32);
        moduli.push(BigUint::one() << (64 * w as u32 - 1));
    }
    for m in &moduli {
        let mut xs = ends();
        let w = (m.bits() as usize).div_ceil(64);
        xs.push(wide(&mut rng, w));
        xs.push(wide(&mut rng, w + 1));
        xs.push(m - 1u32);
        for a in &xs {
            let got = inverse_mod_uint(a, m);
            let coprime = a.gcd(m).is_one();
            match got {
                Some(x) => {
                    assert!(coprime, "an inverse of {a} mod {m} with a common factor");
                    assert!(x < *m);
                    assert_eq!((a * &x) % m, BigUint::one() % m);
                }
                None => assert!(!coprime, "no inverse of {} mod {}", a.bits(), m.bits()),
            }
        }
    }
    // `m = 1`: the ring has one element, so every `a` is invertible, with inverse 0.
    assert_eq!(
        inverse_mod_uint(&BigUint::zero(), &BigUint::one()),
        Some(BigUint::zero())
    );
}

/// The negative control of `inverses_meet_their_definition`: an inverse not reduced below `m`
/// (`x + m`) passes the congruence and is caught by `x < m`.
#[test]
fn an_inverse_not_reduced_is_caught() {
    let (a, m) = (BigUint::from(3u32), BigUint::from(7u32));
    let x = inverse_mod_uint(&a, &m).expect("3 is a unit mod 7") + &m;
    assert_eq!((&a * &x) % &m, BigUint::one());
    assert!(x >= m);
}

/// `bezout_int` gives `s a + t b = g = gcd(a, b) >= 0` for every sign and the zeros (`(0, 0)`
/// gives `(0, 0, 0)`), on the ends and random pairs of every width pair, and its negative
/// control, cofactors with the signs of `a` and `b` dropped, is caught on `-3` and `5`.
#[test]
fn bezout_coefficients_meet_their_definition() {
    let (mut rng, _) = Rng::fresh("bezout_coefficients_meet_their_definition");
    let mut pairs: Vec<(BigUint, BigUint)> = Vec::new();
    for a in ends() {
        for b in ends() {
            pairs.push((a.clone(), b));
        }
    }
    for &aw in &widths() {
        for bw in [1, aw] {
            let c = wide(&mut rng, 1);
            pairs.push((wide(&mut rng, aw) * &c, wide(&mut rng, bw) * &c));
        }
    }
    for (a, b) in &pairs {
        let (a, b) = (BigInt::from(a.clone()), BigInt::from(b.clone()));
        for (a, b) in [(&a, &b), (&-&a, &b), (&a, &-&b), (&-&a, &-&b)] {
            let Some((g, s, t)) = bezout_int(a, b) else {
                panic!("no cofactors for {} and {} bits", a.bits(), b.bits());
            };
            assert_eq!(g, a.gcd(b));
            assert_eq!(&s * a + &t * b, g, "{} and {} bits", a.bits(), b.bits());
        }
    }
    assert_eq!(
        bezout_int(&BigInt::zero(), &BigInt::zero()),
        Some((BigInt::zero(), BigInt::zero(), BigInt::zero()))
    );
    // The cofactors of the magnitudes 3 and 5 meet the definition for 3 and 5, and fail it for
    // -3 and 5: `3 s + 5 t = 1` makes `-3 s + 5 t = 1 - 6 s`, and `s` is not 0 since 5 does not
    // divide 1.
    let (a, b) = (BigInt::from(-3), BigInt::from(5));
    let (g, s, t) = bezout_int(&-&a, &b).expect("narrow");
    assert_eq!(&s * -&a + &t * &b, g);
    assert_ne!(&s * &a + &t * &b, g);
}
