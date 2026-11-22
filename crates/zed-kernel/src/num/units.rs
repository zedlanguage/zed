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

/// Direct tests of [`Rat`] (TEST-kernel-num-rat-units): its arithmetic, powers, Euclidean
/// division, rounding, floats, residues and texts against the value built here from the kept
/// form by num-bigint alone ([`rat::exact`]), on zero, both signs, the ends of a word, wide
/// parts, decimals kept as powers of 2 and 5, and kept powers; each result is also checked to be
/// in the normal form `Rat` promises ([`Rat::from_kept`] reads it back). The private helpers
/// `rem` and `euclid`, the refusal record (`record`, `refused`, `replace_refused`, `Watch`) and
/// the refused branches of `==` and `Ord` are tested under `fixed_room`, which answers each ask
/// by a fixed bound, so a refusal is the same on every machine. Each test's doc names the
/// deliberate break it was run against once (a negative control, not committed) and caught.
mod rat {
    use std::cmp::Ordering::{Equal, Greater, Less};
    use std::sync::atomic::Ordering::Relaxed;

    use num_bigint::{BigInt, BigUint};
    use num_integer::Integer;
    use num_traits::{One, Signed, ToPrimitive, Zero};

    use super::super::tests::power;
    use super::super::{
        Exact, HOLDING, LiteralRounding, Rat, Rounding, Test, TooLarge, WATCHED, Watch, euclid,
        fixed_room, literal_f32, literal_f64, record, refused, rem, replace_refused,
    };
    use super::{LEAF_WORDS, wide};
    use crate::seed::Rng;

    fn int(n: i128) -> Rat {
        Rat::int(BigInt::from(n))
    }

    fn q(n: i64, d: i64) -> Rat {
        Rat::new(BigInt::from(n), BigInt::from(d)).expect("a test's denominator is not zero")
    }

    fn dec(text: &str) -> Rat {
        Rat::decimal(text)
            .expect("a short literal is given its memory")
            .expect("a decimal literal")
    }

    /// `n / d` in lowest terms with `d > 0`; `d` is not zero.
    fn lowest(n: BigInt, d: BigInt) -> (BigInt, BigInt) {
        let g = n.gcd(&d);
        let g = if d.is_negative() { -g } else { g };
        (n / &g, d / g)
    }

    /// The value of `r` as `(N, D)` in lowest terms, `D > 0`, built here from its kept form
    /// with num-bigint alone, apart from the code under test.
    fn exact(r: &Rat) -> (BigInt, BigInt) {
        let (num, den, pows) = r.kept();
        let (mut n, mut d) = (num.clone(), den.clone());
        for (p, e) in pows {
            let k = e
                .magnitude()
                .to_usize()
                .expect("a test's exponents are small");
            let pk = num_traits::pow(BigInt::from(*p), k);
            match e.is_positive() {
                true => n *= pk,
                false => d *= pk,
            }
        }
        lowest(n, d)
    }

    /// Whether `r` is held in the normal form `Rat` promises, as [`Rat::from_kept`] checks it.
    fn normal(r: &Rat) -> bool {
        let (n, d, pows) = r.kept();
        Rat::from_kept(n.clone(), d.clone(), pows.to_vec()).is_some()
    }

    /// `r` is `n / d`, held in normal form.
    #[track_caller]
    fn holds(r: &Rat, (n, d): (BigInt, BigInt), what: &str) {
        assert_eq!(exact(r), lowest(n, d), "{what}");
        assert!(normal(r), "{what}: {r:?} is not in normal form");
    }

    /// Zero, both signs, the ends of a word and past it, fractions, a wide numerator over a
    /// narrow denominator, decimals kept as powers of 2 and 5, kept powers of either sign and a
    /// coefficient beside a kept power (`12 * 2^65`, kept as `3 * 2^67`).
    fn values() -> Vec<Rat> {
        let two64 = BigInt::one() << 64u32;
        let mut v = vec![
            int(0),
            int(1),
            int(-1),
            int(2),
            int(-3),
            q(1, 3),
            q(-1, 3),
            q(7, 12),
            q(-7, 12),
            int(i64::MAX.into()),
            int(i64::MIN.into()),
            int(u64::MAX.into()),
            Rat::int(two64.clone()),
            Rat::int(-&two64),
            Rat::new(&two64 + 1, BigInt::from(3)).expect("3 is not zero"),
            Rat::int((BigInt::one() << 200u32) + 1),
            dec("1e30"),
            dec("2.5e-3"),
            dec("-1e-40"),
            power(3, 100),
            power(3, 100).neg(),
            power(6, 70),
            int(1).div(&power(7, 50)).unwrap().expect("not zero"),
            power(2, 65).mul(&int(12)).unwrap(),
        ];
        v.push(v[v.len() - 1].neg());
        // A prime past 32 bits, kept, and a plain multiple of its square: the test of whether a
        // kept prime divides a coefficient then reads it a word at a time (`divides`).
        let p = 4_294_967_311u64;
        v.push(power(p, 3));
        v.push(Rat::int(BigInt::from(p).pow(2u32) * 3));
        v
    }

    /// Sums, differences, products, quotients, negation, magnitude, order and equality of every
    /// pair of [`values`], against the built value: the plain-integer, plain-rational, zero and
    /// kept paths of `sum`, both paths of `mul`, a zero divisor, and `order` and `==` across
    /// forms. Negative controls, each run once: the kept path of `sum` adding where it should
    /// subtract (`signed` replaced by `+`), and `try_neg` returning the copy unnegated, both
    /// caught here.
    #[test]
    fn arithmetic_agrees_with_the_built_value_in_every_form() {
        let vs = values();
        for a in &vs {
            assert!(normal(a), "{a:?}");
            let (an, ad) = exact(a);
            holds(&a.neg(), (-&an, ad.clone()), &format!("-({a})"));
            holds(
                &a.try_neg().unwrap(),
                (-&an, ad.clone()),
                &format!("-({a})"),
            );
            holds(&a.abs(), (an.abs(), ad.clone()), &format!("|{a}|"));
            for b in &vs {
                let (bn, bd) = exact(b);
                let w = |op: &str| format!("{a} {op} {b}");
                let sum = (&an * &bd + &bn * &ad, &ad * &bd);
                holds(&a.add(b).unwrap(), sum, &w("+"));
                let diff = (&an * &bd - &bn * &ad, &ad * &bd);
                holds(&a.sub(b).unwrap(), diff, &w("-"));
                holds(&a.mul(b).unwrap(), (&an * &bn, &ad * &bd), &w("*"));
                match b.is_zero() {
                    true => assert!(a.div(b).unwrap().is_none(), "{}", w("/")),
                    false => holds(
                        &a.div(b).unwrap().expect("not zero"),
                        (&an * &bd, &ad * &bn),
                        &w("/"),
                    ),
                }
                let order = (&an * &bd).cmp(&(&bn * &ad));
                assert_eq!(a.try_cmp(b).unwrap(), order, "{}", w("<=>"));
                assert_eq!(a.cmp(b), order, "{}", w("cmp"));
                assert_eq!(a == b, order == Equal, "{}", w("=="));
            }
        }
        // One value in two forms is equal, and the other sign is not.
        assert_eq!(dec("1e3"), int(1000));
        assert_eq!(int(8), power(2, 3));
        assert_ne!(int(-8), power(2, 3));
    }

    /// `pow` to 0 through 5 and `pow_int` to -3 through 3 of every one of [`values`] and of
    /// `2^64 + 1`, against the built value: the factored parts of a word or less, the built
    /// powers of a wider part, a negative base to odd and even powers, a negative exponent
    /// (`recip`), and `0^e` for a negative `e` (`None`). Then bases 0, 1 and -1 to a kept
    /// exponent too large to build, read from its sign and parity, where base 2 is refused.
    /// Negative controls, each run once: the parity test of the bases ±1 turned over
    /// (`!e.is_even()` to `e.is_even()`), caught here; `recip` swapping the parts without
    /// moving the sign, caught by the normal-form check.
    #[test]
    fn powers_agree_with_the_built_value() {
        let mut vs = values();
        vs.push(Rat::int((BigInt::one() << 64u32) + 1));
        for a in &vs {
            let (an, ad) = exact(a);
            for e in 0..=5u32 {
                let p = a.pow(&BigUint::from(e)).unwrap();
                holds(&p, (an.pow(e), ad.pow(e)), &format!("({a})^{e}"));
            }
            for e in -3i64..=3 {
                let p = a.pow_int(&int(e.into())).unwrap();
                let k = e.unsigned_abs() as u32;
                let (n, d) = (an.pow(k), ad.pow(k));
                match (a.is_zero(), e < 0) {
                    (true, true) => assert!(p.is_none(), "0^{e}"),
                    (_, true) => holds(&p.expect("not zero"), (d, n), &format!("({a})^{e}")),
                    (_, false) => holds(&p.expect("defined"), (n, d), &format!("({a})^{e}")),
                }
            }
        }
        // `3^(2^40)` is odd and `2^(2^40)` even; built, either has some 2^40 bits.
        let (odd, even) = (power(3, 1 << 40), power(2, 1 << 40));
        fixed_room(1 << 20, || {
            for (e, sign) in [(&odd, -1), (&even, 1), (&odd.neg(), -1), (&even.neg(), 1)] {
                holds(
                    &int(1).pow_int(e).unwrap().unwrap(),
                    (1.into(), 1.into()),
                    "1^e",
                );
                let p = int(-1).pow_int(e).unwrap().unwrap();
                holds(&p, (sign.into(), 1.into()), "(-1)^e");
            }
            holds(
                &int(0).pow_int(&odd).unwrap().unwrap(),
                (0.into(), 1.into()),
                "0^e",
            );
            assert!(int(0).pow_int(&odd.neg()).unwrap().is_none());
            assert!(int(2).pow_int(&odd).is_err(), "2^e builds e");
        });
    }

    /// `rem_euclid` and `div_euclid` of every pair of integers among [`values`], against the
    /// floor modulo `|m|` and `q = (a - r) / m`: the plain path, an exact division of kept
    /// powers, a dividend smaller than `|m|` of each sign toward each sign of `m` (`0` and
    /// `±1`), and the general path that builds the divisor. Negative controls, each run once:
    /// the quotient of a negative dividend smaller than a negative `m` given as `-1` where it
    /// is `1`, and `rem_euclid` returning a negative small dividend itself (the `!negative`
    /// test removed), both caught here.
    #[test]
    fn euclidean_division_agrees_with_the_floor_by_the_magnitude() {
        let ints: Vec<Rat> = values().into_iter().filter(Rat::is_integer).collect();
        for a in &ints {
            for m in ints.iter().filter(|m| !m.is_zero()) {
                let ((an, _), (mn, _)) = (exact(a), exact(m));
                let r = an.mod_floor(&mn.abs());
                let quotient = (&an - &r) / &mn;
                let w = |op: &str| format!("{a} {op} {m}");
                holds(&a.rem_euclid(m).unwrap(), (r, BigInt::one()), &w("mod"));
                holds(
                    &a.div_euclid(m).unwrap(),
                    (quotient, BigInt::one()),
                    &w("div"),
                );
            }
        }
    }

    /// `rem` against num-bigint's `%` for divisors of one word and wider, and `euclid` for a
    /// zero, a positive and a negative remainder; under a room of 0 bits, a divisor of one word
    /// and the remainders that build nothing ask for nothing, while a wider divisor and a
    /// negative remainder are refused. Negative controls, each run once: `euclid` building
    /// `|m| - r` without asking (its `room` removed), and `rem` by one word off by one, both
    /// caught here.
    #[test]
    fn rem_and_euclid_ask_for_memory_only_where_they_build() {
        let (mut rng, _) = Rng::fresh("rem_and_euclid_ask_for_memory_only_where_they_build");
        let divisors = [
            BigUint::one(),
            BigUint::from(7u32),
            BigUint::from(u64::MAX),
            wide(&mut rng, 2),
            wide(&mut rng, LEAF_WORDS + 1),
        ];
        let dividends = [
            BigUint::zero(),
            BigUint::one(),
            BigUint::from(u64::MAX),
            wide(&mut rng, 1),
            wide(&mut rng, 5),
            wide(&mut rng, 3 * LEAF_WORDS),
        ];
        for m in &divisors {
            for a in &dividends {
                assert_eq!(
                    rem(a, m).unwrap(),
                    a % m,
                    "{} by {} bits",
                    a.bits(),
                    m.bits()
                );
            }
        }
        let a = &dividends[4];
        fixed_room(0, || {
            assert!(rem(a, &divisors[2]).is_ok(), "one word asks nothing");
            assert!(rem(a, &divisors[3]).is_err(), "two words ask");
        });
        let (m, five) = (BigUint::from(7u32), BigUint::from(5u32));
        let one = BigInt::one;
        holds(
            &euclid(BigUint::zero(), true, &m).unwrap(),
            (0.into(), one()),
            "-0",
        );
        holds(
            &euclid(five.clone(), false, &m).unwrap(),
            (5.into(), one()),
            "5",
        );
        holds(
            &euclid(five.clone(), true, &m).unwrap(),
            (2.into(), one()),
            "-5",
        );
        fixed_room(0, || {
            assert!(euclid(BigUint::zero(), true, &m).is_ok());
            assert!(euclid(five.clone(), false, &m).is_ok());
            assert!(euclid(five.clone(), true, &m).is_err(), "|m| - r is built");
        });
    }

    /// The record of refusals: none until one is recorded; the first is kept and the later
    /// dropped; [`refused`] clears it; the count of threads holding one is at least 1 while
    /// this one holds one (other threads move it too, so no more is asserted); and a [`Watch`]
    /// starts with none, sets the watch, and on its drop gives back the watch and the record it
    /// replaced, so a nested run keeps its own. Negative controls, each run once: `record`
    /// keeping the last refusal (`Some((t, e))` written over the first), and the `Watch`'s drop
    /// not giving back the outer record, both caught here.
    #[test]
    fn the_first_refusal_is_kept_until_read_and_a_watch_keeps_its_own() {
        let e = |k: u32| TooLarge {
            size: BigUint::from(k),
            ask: BigUint::from(k),
        };
        assert_eq!(refused(), None);
        record(Test::Order, e(1));
        assert!(HOLDING.load(Relaxed) >= 1);
        record(Test::Equality, e(2));
        assert_eq!(refused(), Some((Test::Order, e(1))));
        assert_eq!(refused(), None);
        assert_eq!(replace_refused(Some((Test::Equality, e(3)))), None);
        assert!(HOLDING.load(Relaxed) >= 1);
        assert_eq!(replace_refused(None), Some((Test::Equality, e(3))));
        record(Test::Order, e(4));
        assert!(!WATCHED.get());
        {
            let _outer = Watch::start();
            assert!(WATCHED.get());
            assert_eq!(refused(), None, "a watched run starts with no refusal");
            record(Test::Equality, e(5));
            {
                let _inner = Watch::start();
                assert_eq!(refused(), None);
                record(Test::Order, e(6));
            }
            assert!(WATCHED.get());
            assert_eq!(refused(), Some((Test::Equality, e(5))));
        }
        assert!(!WATCHED.get());
        assert_eq!(refused(), Some((Test::Order, e(4))));
        assert_eq!(refused(), None);
    }

    /// A comparison refused its memory (a room of 0 bits) gives the order of the normal forms,
    /// and is recorded only under a [`Watch`]: the kept `3 * 2^100` and the plain
    /// `3 * 2^100 - 1` have one bit length (102) and logarithms within `2^-100`, so neither of
    /// `bound::cmp`'s free tests orders them and its first round of bounds asks for memory;
    /// `8` and `2^3` are one value in two forms, so their equality needs the copy of the 8 that
    /// aligning makes. Unwatched, `==` aligns without asking and answers by value. The forms'
    /// order (`3 < 3 * 2^100 - 1` in the coefficient) is the reverse of the values'. Negative
    /// controls, each run once: `Ord` recording its refusal without a watch, and `==` answering
    /// `true` on a refusal, both caught here.
    #[test]
    fn a_refused_comparison_gives_the_forms_order_and_is_recorded_under_a_watch() {
        let a = power(2, 100).mul(&int(3)).unwrap();
        let b = Rat::int((BigInt::from(3) << 100u32) - 1);
        assert_eq!(
            a.cmp(&b),
            Greater,
            "3 * 2^100 > 3 * 2^100 - 1, given the memory"
        );
        fixed_room(0, || {
            assert!(a.try_cmp(&b).is_err());
            assert_eq!(a.cmp(&b), a.form_cmp(&b));
            assert_eq!(a.cmp(&b), Less, "(3, 1, [2^100]) < (3 * 2^100 - 1, 1, [])");
            assert!(int(8) == power(2, 3));
            assert_eq!(refused(), None, "nothing is recorded unwatched");
            let _watch = Watch::start();
            assert_eq!(a.cmp(&b), Less);
            assert!(matches!(refused(), Some((Test::Order, _))));
            assert!(int(8) != power(2, 3), "the forms differ");
            assert!(matches!(refused(), Some((Test::Equality, _))));
            assert!(int(8) == int(8), "plain numbers compare without a copy");
            assert_eq!(refused(), None);
        });
    }

    /// `is_even`, `small_integer`, `in_lowest_terms` and the text `Display` writes, on the
    /// forms each reads: a power of 2 kept or in the coefficient, the bound of 64 bits on both
    /// sides (`2^63`, `u64::MAX`, `2^64`, `3^40`, `3^64`), and a denominator of 1, a negative
    /// one and one not coprime. Negative controls, each run once: `small_integer`'s bound
    /// moved from 63 to 64 (so `2^64` is built), and `in_lowest_terms` taking a denominator
    /// of 1, both caught here.
    #[test]
    fn the_small_predicates_read_the_kept_form() {
        for (r, even) in [
            (int(0), true),
            (int(4), true),
            (int(-3), false),
            (int(u64::MAX.into()), false),
            (power(2, 1), true),
            (power(3, 5), false),
            (dec("1e30"), true),
            (power(2, 65).mul(&int(12)).unwrap(), true),
            (power(3, 7).mul(&int(-2)).unwrap(), true),
        ] {
            assert_eq!(r.is_even(), even, "{r:?}");
        }
        let two = BigInt::from(2);
        let three = BigInt::from(3);
        for (r, want) in [
            (int(0), Some(BigInt::zero())),
            (int(-5), Some(BigInt::from(-5))),
            (int(i64::MIN.into()), Some(BigInt::from(i64::MIN))),
            (int(u64::MAX.into()), Some(BigInt::from(u64::MAX))),
            (Rat::int(two.pow(64u32)), None),
            (power(2, 63), Some(two.pow(63u32))),
            (power(2, 63).neg(), Some(-two.pow(63u32))),
            (power(2, 64), None),
            (power(3, 40), Some(three.pow(40u32))),
            (power(3, 64), None),
        ] {
            assert_eq!(r.small_integer(), want, "{r:?}");
        }
        let lowest_terms = |n: i64, d: i64| Rat::in_lowest_terms(n.into(), d.into());
        for (n, d) in [(1, 3), (-1, 3), (7, 12)] {
            holds(
                &lowest_terms(n, d).expect("lowest"),
                (n.into(), d.into()),
                "n/d",
            );
        }
        for (n, d) in [(0, 5), (2, 4), (3, 1), (1, -3), (1, 0)] {
            assert!(lowest_terms(n, d).is_none(), "{n}/{d}");
        }
        for (r, text) in [
            (int(3), "3r"),
            (int(-3), "-3r"),
            (q(-1, 3), "-1r/3r"),
            (power(3, 4), "81r"),
            (int(1).div(&power(7, 2)).unwrap().unwrap(), "1r/49r"),
        ] {
            assert_eq!(r.to_string(), text);
        }
        // Refused the memory of its digits, a kept number is written by its powers.
        let (r, s) = (power(3, 100), int(1).div(&power(7, 50)).unwrap().unwrap());
        fixed_room(0, || {
            assert_eq!(r.to_string(), "rat(3^100)");
            assert_eq!(s.to_string(), "rat(1)/rat(7^50)");
            assert_eq!(q(1, 3).to_string(), "1r/3r");
        });
    }

    /// The whole number each rule gives, from the nearer of the two whole numbers around `n / d`
    /// by their distances, apart from `round_whole`'s test of `2 r` against `d`.
    fn rounded(n: &BigInt, d: &BigInt, rule: Rounding) -> BigInt {
        let lo = n.div_floor(d);
        if &lo * d == *n {
            return lo;
        }
        let hi = &lo + 1;
        let (below, above) = (n - &lo * d, &hi * d - n);
        let neg = n.is_negative();
        let nearer = |tie: bool| match below.cmp(&above) {
            Less => false,
            Greater => true,
            Equal => tie,
        };
        let up = match rule {
            Rounding::Floor => false,
            Rounding::Ceil => true,
            Rounding::Trunc => neg,
            Rounding::AwayFromZero => !neg,
            Rounding::TiesEven => nearer(lo.is_odd()),
            Rounding::TiesAway => nearer(!neg),
        };
        if up { hi } else { lo }
    }

    /// `round_whole` by each of the six rules on [`values`], on `n / d` for `n` in -13..=13 and
    /// `d` in 1..=4 (every tie of both signs), and on `±3^101 / 2`, a tie between kept powers;
    /// an integer is kept in its own form. Negative control, run once: a tie to even sent to
    /// the odd neighbor (`!q.is_even()` to `q.is_even()`), caught here.
    #[test]
    fn rounding_to_a_whole_number_meets_each_rule() {
        let rules = [
            Rounding::TiesEven,
            Rounding::TiesAway,
            Rounding::Floor,
            Rounding::Ceil,
            Rounding::Trunc,
            Rounding::AwayFromZero,
        ];
        let mut xs = values();
        for n in -13..=13 {
            for d in 1..=4 {
                xs.push(q(n, d));
            }
        }
        let half = power(3, 101).div(&int(2)).unwrap().expect("not zero");
        xs.extend([half.neg(), half, dec("-2.5"), dec("2.5e-3")]);
        for x in &xs {
            let (n, d) = exact(x);
            for rule in rules {
                let want = (rounded(&n, &d, rule), BigInt::one());
                holds(
                    &x.round_whole(rule).unwrap(),
                    want,
                    &format!("{x} {rule:?}"),
                );
            }
        }
        let kept = power(3, 100);
        assert_eq!(
            kept.round_whole(Rounding::Floor).unwrap().kept(),
            kept.kept()
        );
    }

    /// `to_f64` and `to_f32` on `n / d` small enough that the float division is the correctly
    /// rounded oracle, on decimals against `literal_f64` and `literal_f32`, and at the ends of
    /// each format: the largest finite, a value half an ulp above it (a tie, which goes to the
    /// even neighbor, infinity), the least subnormal, half of it (a tie to 0, an error), the
    /// largest subnormal, and the tie between it and the least normal. Then `Exact::float`
    /// read back by `to_f64`, and the order of the extended line. Negative control, run once:
    /// `Exact::float`'s subnormal exponent off by one (-1075), caught by the reading back.
    #[test]
    fn floats_are_the_nearest_ties_to_even_and_read_back() {
        for n in -40i64..=40 {
            for d in 1..=12 {
                let r = q(n, d);
                assert_eq!(r.to_f64().unwrap(), n as f64 / d as f64, "{n}/{d}");
                assert_eq!(r.to_f32().unwrap(), n as f32 / d as f32, "{n}/{d}");
            }
        }
        for t in [
            "0.1", "2.5e-3", "1e30", "1e-40", "1e308", "1e-320", "3.4e38", "1e-45",
        ] {
            for (s, x) in [("", dec(t)), ("-", dec(t).neg())] {
                let sign = if s.is_empty() { 1.0 } else { -1.0 };
                assert_eq!(
                    x.to_f64(),
                    literal_f64(t).unwrap().map(|f| sign * f),
                    "{s}{t}"
                );
                assert_eq!(
                    x.to_f32(),
                    literal_f32(t).unwrap().map(|f| sign as f32 * f),
                    "{s}{t}"
                );
            }
        }
        let two = |e: i64| match e >= 0 {
            true => power(2, e as u64),
            false => int(1).div(&power(2, e.unsigned_abs())).unwrap().unwrap(),
        };
        let times = |m: i128, e: i64| int(m).mul(&two(e)).unwrap();
        let f64s = [
            (two(1023), Ok(2f64.powi(1023))),
            (two(1024), Err(LiteralRounding::Infinite)),
            (times((1 << 53) - 1, 971), Ok(f64::MAX)),
            (times((1 << 55) - 3, 969), Ok(f64::MAX)),
            (times((1 << 55) - 2, 969), Err(LiteralRounding::Infinite)),
            (two(-1074), Ok(f64::from_bits(1))),
            (times(3, -1076), Ok(f64::from_bits(1))),
            (two(-1075), Err(LiteralRounding::Zero)),
            (two(-1022), Ok(f64::MIN_POSITIVE)),
            (
                times((1 << 52) - 1, -1074),
                Ok(f64::from_bits((1 << 52) - 1)),
            ),
            (times((1 << 53) - 1, -1075), Ok(f64::MIN_POSITIVE)),
            (int(u64::MAX.into()), Ok(u64::MAX as f64)),
            (int(i64::MIN.into()), Ok(i64::MIN as f64)),
        ];
        for (x, want) in f64s {
            assert_eq!(x.to_f64(), want, "{x}");
            let neg = want.map(|f| -f);
            assert_eq!(x.neg().to_f64(), neg, "-{x}");
        }
        let f32s = [
            (two(127), Ok(2f32.powi(127))),
            (two(128), Err(LiteralRounding::Infinite)),
            (times((1 << 24) - 1, 104), Ok(f32::MAX)),
            (two(-149), Ok(f32::from_bits(1))),
            (two(-150), Err(LiteralRounding::Zero)),
            (times((1 << 24) - 1, -150), Ok(f32::MIN_POSITIVE)),
        ];
        for (x, want) in f32s {
            assert_eq!(x.to_f32(), want, "{x}");
        }
        let floats = [
            0.0,
            -0.0,
            0.5,
            -1.5,
            0.1,
            1e300,
            f64::from_bits(1),
            f64::from_bits((1 << 52) - 1),
            f64::MIN_POSITIVE,
            f64::MAX,
            -f64::MAX,
        ];
        for x in floats {
            let Exact::Finite(r) = Exact::float(x) else {
                panic!("{x} is finite");
            };
            assert_eq!(r.to_f64().unwrap(), x, "{x}");
        }
        assert!(matches!(Exact::float(0.5), Exact::Finite(r) if *r == q(1, 2)));
        assert!(matches!(Exact::float(f64::from_bits(1)), Exact::Finite(r) if *r == two(-1074)));
        assert!(matches!(Exact::float(f64::NAN), Exact::NaN));
        assert!(matches!(Exact::float(f64::INFINITY), Exact::PosInf));
        assert!(matches!(Exact::float(f64::NEG_INFINITY), Exact::NegInf));
        let line = [
            -f64::INFINITY,
            -f64::MAX,
            -0.5,
            0.0,
            5e-324,
            f64::MAX,
            f64::INFINITY,
        ];
        let line: Vec<Exact> = line
            .into_iter()
            .chain([f64::NAN])
            .map(Exact::float)
            .collect();
        assert!(line.windows(2).all(|w| w[0] < w[1]));
    }

    /// `residues` and `integer_residues` against the built value modulo `M = 2^61 - 1` and
    /// `M - 1` (negative integers to their floor residue), equal for one value in two forms, and
    /// `built_parts` against the magnitudes of the built numerator and denominator;
    /// then the literal text of each form a value takes (`meKr`, the quotient `nr/dr`, and a
    /// power whose digits no memory holds), and the integer text of kept powers (the gcd of the
    /// exponents taken where it is shorter, a coefficient, primes grouped by exponent, largest
    /// first, and the digits where they are no longer). Negative controls, each run once: the
    /// negative branch of `integer_residues` returning `e` for `M - 1` unnegated, and
    /// `power_text` sorting the groups smallest exponent first, both caught here.
    #[test]
    fn residues_and_texts_are_the_value_s_whatever_its_form() {
        const M: u64 = (1 << 61) - 1;
        let modulo = |x: &BigInt, m: u64| x.mod_floor(&m.into()).to_u64().expect("below m");
        for a in values() {
            let (n, d) = exact(&a);
            let want = (n.is_negative(), modulo(&n.abs(), M), modulo(&d, M));
            assert_eq!(a.residues(), want, "{a}");
            if a.is_integer() {
                assert_eq!(
                    a.integer_residues(),
                    (modulo(&n, M), modulo(&n, M - 1)),
                    "{a}"
                );
            }
            let (bn, bd) = a.built_parts().unwrap();
            assert_eq!(
                (bn.into_owned(), bd.into_owned()),
                (n.into_parts().1, d.into_parts().1)
            );
        }
        assert_eq!(dec("1e3").residues(), int(1000).residues());
        assert_eq!(
            dec("-1e3").integer_residues(),
            int(-1000).integer_residues()
        );
        let wide = power(2, 65).mul(&int(12)).unwrap();
        let wide_text = format!("{}r", BigInt::from(3) << 67u32);
        for (r, text) in [
            (int(0), "0r"),
            (int(7), "7r"),
            (int(1000), "1e3r"),
            (dec("1e3"), "1e3r"),
            (dec("1e30"), "1e30r"),
            (dec("2.5e-3"), "25e-4r"),
            (dec("-1e-40"), "-1e-40r"),
            (q(1, 2), "5e-1r"),
            (q(1, 8), "125e-3r"),
            (int(-250), "-25e1r"),
            (q(1, 3), "1r/3r"),
            (q(-7, 12), "-7r/12r"),
            (int(1).div(&power(7, 2)).unwrap().unwrap(), "1r/49r"),
            (power(3, 5), "243r"),
            (wide, wide_text.as_str()),
        ] {
            assert_eq!(r.literal_text(), text, "{r:?}");
        }
        let huge = int(3).pow(&(BigUint::one() << 64u32)).unwrap();
        assert_eq!(huge.literal_text(), "rat(3^18446744073709551616)");
        let five = int(5);
        for (r, text) in [
            (power(3, 100), "3^100"),
            (power(12, 1000), "12^1000"),
            (power(3, 200).mul(&five.neg()).unwrap(), "-5*3^200"),
            (power(2, 10), "1024"),
            (power(6, 5), "6^5"),
            (power(6, 100).mul(&int(7)).unwrap(), "7*6^100"),
            (power(2, 100).mul(&power(3, 50)).unwrap(), "12^50"),
            (
                power(2, 3).mul(&power(3, 200)).unwrap().mul(&five).unwrap(),
                "5*3^200*2^3",
            ),
            (power(2, 1).mul(&power(3, 1)).unwrap(), "6"),
        ] {
            assert_eq!(r.integer_text(), text, "{r:?}");
        }
    }
}
