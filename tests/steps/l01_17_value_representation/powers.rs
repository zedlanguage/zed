//! Exact numbers held as powers of primes (sec:domains): `n/d * prod p^e`, with exponents kept
//! and not built. Each test compares the kept form with the value built out in full, or with
//! the standard library's correctly rounded reading of the same decimal text.

use num_bigint::BigInt;
use zed_kernel::Rat;
use zed_kernel::num::{LiteralRounding, literal_f32, literal_f64};
use zed_tests::instances::Rng;
use zed_tests::scaling::check_order;

/// The value built out: the plain rational of its digits.
fn built(r: &Rat) -> Rat {
    let n: BigInt = r.numer_text().parse().expect("a numerator is digits");
    let d: BigInt = r.denom_text().parse().expect("a denominator is digits");
    Rat::new(n, d).expect("a denominator is not zero")
}

fn int(n: i64) -> Rat {
    Rat::int(BigInt::from(n))
}

fn dec(text: &str) -> Rat {
    Rat::decimal(text).expect("a test literal is decimal")
}

/// `2^k`, with `k` of either sign.
fn two_to(k: i64) -> Rat {
    let p = int(2).pow(&k.unsigned_abs().into()).unwrap();
    if k < 0 {
        int(1).div(&p).expect("2^k is not zero")
    } else {
        p
    }
}

/// A random exact number: a decimal with an exponent, a power of a small base, or their
/// product or quotient, small enough to build.
fn random(rng: &mut Rng) -> Rat {
    let mantissa = rng.int(-999, 999);
    let point = rng.below(3);
    let text = match point {
        0 => format!("{mantissa}e{}", rng.int(-40, 40)),
        _ => format!("{mantissa}.{}e{}", rng.int(0, 99), rng.int(-40, 40)),
    };
    let d = dec(&text);
    let base = int(rng.pick(&[2, 3, 5, 6, 7, 10, 12, 15]));
    let p = base.pow(&(rng.below(30) as u64).into()).unwrap();
    match rng.below(4) {
        0 => d,
        1 => p,
        2 => d.mul(&p),
        _ => d.div(&p).expect("a power of a positive base is not zero"),
    }
}

#[test]
fn kept_powers_agree_with_the_built_value() {
    let mut rng = Rng::new(17);
    for _ in 0..2000 {
        let (a, b) = (random(&mut rng), random(&mut rng));
        let (ba, bb) = (built(&a), built(&b));
        let at = format!("{a:?} and {b:?}");
        assert_eq!(
            built(&a.add(&b).unwrap()),
            ba.add(&bb).unwrap(),
            "+ of {at}"
        );
        assert_eq!(
            built(&a.sub(&b).unwrap()),
            ba.sub(&bb).unwrap(),
            "- of {at}"
        );
        assert_eq!(built(&a.mul(&b)), ba.mul(&bb), "* of {at}");
        if !b.is_zero() {
            let q = a.div(&b).expect("b is not zero");
            assert_eq!(built(&q), ba.div(&bb).expect("b is not zero"), "/ of {at}");
        }
        assert_eq!(a.cmp(&b), ba.cmp(&bb), "order of {at}");
        assert_eq!(a == b, ba == bb, "== of {at}");
        assert!(a == ba, "{a:?} and its built value");
        assert_eq!(
            built(&a.pow(&3u32.into()).unwrap()),
            ba.pow(&3u32.into()).unwrap(),
            "cube of {a:?}"
        );
        assert_eq!(a.to_f64(), ba.to_f64(), "f64 of {a:?}");
        assert_eq!(a.to_f32(), ba.to_f32(), "f32 of {a:?}");
        if a.is_integer() && b.is_integer() && !b.is_zero() {
            assert_eq!(
                built(&a.rem_euclid(&b).unwrap()),
                ba.rem_euclid(&bb).unwrap(),
                "mod of {at}"
            );
            assert_eq!(
                built(&a.div_euclid(&b).unwrap()),
                ba.div_euclid(&bb).unwrap(),
                "div of {at}"
            );
        }
    }
}

/// The decimal text of `(2m + 1) * 2^k`, a number halfway between two floats when `2m` has the
/// float's width: for `k < 0` it is `(2m + 1) * 5^-k` tenths to the `-k`.
fn halfway(m: u64, k: i64) -> String {
    let odd = BigInt::from(2 * m + 1);
    if k >= 0 {
        format!("{}", odd << k as usize)
    } else {
        format!("{}e{k}", odd * BigInt::from(5).pow(k.unsigned_abs() as u32))
    }
}

/// What the projection should give, from the standard library's reading of the same text.
fn expected<F: std::str::FromStr + Into<f64> + Copy>(text: &str) -> Result<F, LiteralRounding>
where
    F::Err: std::fmt::Debug,
{
    let x: F = text.parse().expect("a decimal reads as a float");
    let wide: f64 = x.into();
    let zero = text.split(['e', 'E']).next().expect("split gives one part");
    if wide.is_infinite() {
        Err(LiteralRounding::Infinite)
    } else if wide == 0.0 && zero.bytes().any(|b| (b'1'..=b'9').contains(&b)) {
        Err(LiteralRounding::Zero)
    } else {
        Ok(x)
    }
}

#[test]
fn projection_matches_the_standard_reading() {
    let mut rng = Rng::new(33);
    let digits = |rng: &mut Rng, n: usize| -> String {
        (0..n)
            .map(|_| char::from(b'0' + rng.below(10) as u8))
            .collect()
    };
    for _ in 0..4000 {
        let n = 1 + rng.below(30);
        let f = rng.below(4);
        let (whole, frac) = (digits(&mut rng, n), digits(&mut rng, f));
        let text = format!("{whole}.{frac}0e{}", rng.int(-360, 330));
        let bits = |r: Result<f64, LiteralRounding>| r.map(f64::to_bits);
        assert_eq!(bits(literal_f64(&text)), bits(expected(&text)), "{text}");
        let text = format!("{whole}e{}", rng.int(-60, 50));
        let bits = |r: Result<f32, LiteralRounding>| r.map(f32::to_bits);
        assert_eq!(bits(literal_f32(&text)), bits(expected(&text)), "{text}");
    }
    // Ties at full width, normal and subnormal, which round to the even neighbor.
    for _ in 0..400 {
        let m = (1 << 52) | (rng.next_u64() >> 12);
        for k in [rng.int(-1100, -1076), rng.int(-1000, 900)] {
            let text = halfway(m >> (rng.below(30) * usize::from(k < -1074)), k);
            let bits = |r: Result<f64, LiteralRounding>| r.map(f64::to_bits);
            assert_eq!(bits(literal_f64(&text)), bits(expected(&text)), "{text}");
        }
        let m = (1 << 23) | (rng.next_u64() >> 41);
        let text = halfway(m, rng.int(-170, 100));
        let bits = |r: Result<f32, LiteralRounding>| r.map(f32::to_bits);
        assert_eq!(bits(literal_f32(&text)), bits(expected(&text)), "{text}");
    }
}

#[test]
fn corner_cases_of_kept_powers() {
    // Zero has no powers, whatever its exponent.
    assert!(dec("0e999").is_zero());
    assert_eq!(dec("0e999"), int(0));
    assert_eq!(dec("-0.0e-999999999999").numer_text(), "0");
    assert_eq!(literal_f64("0e99999999999"), Ok(0.0));
    // Negatives.
    assert_eq!(dec("-1.5e3"), int(-1500));
    assert_eq!(dec("-1.5e3").to_f64(), Ok(-1500.0));
    assert_eq!(dec("-2.5e-1").abs(), dec("0.25"));
    // Past either end of f64 and f32.
    assert_eq!(literal_f64("1e-400"), Err(LiteralRounding::Zero));
    assert_eq!(literal_f64("1e400"), Err(LiteralRounding::Infinite));
    assert_eq!(literal_f32("1e-50"), Err(LiteralRounding::Zero));
    assert_eq!(literal_f32("1e39"), Err(LiteralRounding::Infinite));
    assert_eq!(literal_f64("-1e-99999999999"), Err(LiteralRounding::Zero));
    // The largest f64 and the tie above it, which rounds to even: infinity.
    let max = int((1 << 53) - 1).mul(&two_to(971));
    assert_eq!(max.to_f64(), Ok(f64::MAX));
    let above = int((1 << 54) - 1).mul(&two_to(970));
    assert_eq!(above.to_f64(), Err(LiteralRounding::Infinite));
    let below = int((1 << 55) - 3).mul(&two_to(969));
    assert_eq!(below.to_f64(), Ok(f64::MAX));
    // Subnormals: the least, half of it (a tie, to the even zero), and three quarters of it.
    let least = f64::from_bits(1);
    assert_eq!(two_to(-1074).to_f64(), Ok(least));
    assert_eq!(two_to(-1075).to_f64(), Err(LiteralRounding::Zero));
    assert_eq!(int(3).mul(&two_to(-1076)).to_f64(), Ok(least));
    assert_eq!(int(3).mul(&two_to(-1075)).to_f64(), Ok(2.0 * least));
    assert_eq!(two_to(-149).to_f32(), Ok(f32::from_bits(1)));
    assert_eq!(two_to(-150).to_f32(), Err(LiteralRounding::Zero));
    // f32 ties at 2^24.
    assert_eq!(int((1 << 24) + 1).to_f32(), Ok(16_777_216.0));
    assert_eq!(int((1 << 24) + 3).to_f32(), Ok(16_777_220.0));
    assert_eq!(dec("16777217e0").to_f32(), Ok(16_777_216.0));
    // Powers that cancel to an integer.
    let one = dec("1e-5").mul(&int(10).pow(&5u32.into()).unwrap());
    assert_eq!(one, int(1));
    assert!(one.is_integer());
    assert_eq!(
        (one.numer_text(), one.denom_text()),
        ("1".into(), "1".into())
    );
    let q = int(6)
        .pow(&90u32.into())
        .unwrap()
        .div(&int(3).pow(&90u32.into()).unwrap())
        .unwrap();
    assert!(q.is_integer());
    assert_eq!(q.to_integer().unwrap(), BigInt::from(2).pow(90u32));
    assert_eq!(dec("2.5e1").mul(&dec("4e-1")), int(10));
    // One number in several forms is one number.
    assert_eq!(int(1000), dec("1e3"));
    assert_eq!(int(8), int(2).pow(&3u32.into()).unwrap());
    assert_eq!(
        dec("1.345e932").numer_text(),
        format!("1345{}", "0".repeat(929))
    );
}

/// Two numbers that agree in all but their last digit, so no bound short of their full width
/// tells them apart, are built and compared.
#[test]
fn close_products_compare_exactly() {
    let p = int(3).pow(&4000u32.into()).unwrap().mul(&int(7));
    let q = p.add(&int(1)).unwrap();
    assert!(p < q && q > p && p != q);
    // A power of ten on both is cancelled before the comparison.
    let t = int(10).pow(&5000u32.into()).unwrap();
    assert!(p.mul(&t) < q.mul(&t));
    // `2^84 < 3^53`, which differ in their third digit.
    assert!(int(2).pow(&84u32.into()).unwrap() < int(3).pow(&53u32.into()).unwrap());
    assert!(dec("2e84").div(&dec("1e84")).unwrap() > dec("1.9e0"));
    // A negative product reverses the order.
    assert!(p.neg() > q.neg());
}

/// Plain rationals and integers take their own fast paths; doubling both operands puts a
/// power of 2 in them and sends them through the general path. On integers and rationals of
/// either sign, zero and the ends of the 64-bit range, the two paths give the same sum,
/// difference, product, order, equality and sign, with the same digits.
#[test]
fn plain_fast_paths_agree_with_the_general_path() {
    let big = BigInt::from(7) * BigInt::from(10).pow(40u32);
    let mut values = vec![
        int(0),
        int(1),
        int(-1),
        int(6),
        int(-15),
        int(i64::MAX),
        int(i64::MIN),
        Rat::int(big.clone()),
        Rat::int(-big),
    ];
    for (n, d) in [(3, 4), (-5, 6), (5, -6), (1, 3), (-9, 10), (7, 1i64 << 40)] {
        values.push(Rat::new(BigInt::from(n), BigInt::from(d)).unwrap());
    }
    let two = int(2).pow(&1u32.into()).unwrap();
    let four = two.mul(&two);
    let text = |r: &Rat| (r.numer_text(), r.denom_text());
    for a in &values {
        for b in &values {
            let (a2, b2) = (a.mul(&two), b.mul(&two));
            let at = format!("{a} and {b}");
            let sum = a2.add(&b2).unwrap();
            assert_eq!(text(&sum), text(&a.add(b).unwrap().mul(&two)), "+ of {at}");
            let diff = a2.sub(&b2).unwrap();
            assert_eq!(text(&diff), text(&a.sub(b).unwrap().mul(&two)), "- of {at}");
            assert_eq!(text(&a2.mul(&b2)), text(&a.mul(b).mul(&four)), "* of {at}");
            assert_eq!(a2.cmp(&b2), a.cmp(b), "order of {at}");
            assert_eq!(a2 == b2, a == b, "== of {at}");
            assert_eq!(
                (sum.is_negative(), sum.is_zero()),
                (a.add(b).unwrap().is_negative(), a.add(b).unwrap().is_zero()),
                "sign of {at}"
            );
        }
    }
}

/// `div` and `mod` by a power of primes with an exponent near `10^12` subtract exponents when
/// the division is exact, and a dividend smaller than the divisor is its own remainder, so
/// none of these builds a number of `10^12` bits.
#[test]
fn an_exact_division_by_a_huge_power_builds_nothing() {
    let e: u64 = 1_000_000_000_000;
    let ten = int(10).pow(&e.into()).unwrap();
    let two = int(2).pow(&e.into()).unwrap();
    let five = int(5).pow(&e.into()).unwrap();
    assert_eq!(ten.div_euclid(&two).unwrap(), five);
    assert_eq!(ten.rem_euclid(&two).unwrap(), int(0));
    assert_eq!(ten.neg().div_euclid(&two).unwrap(), five.neg());
    assert_eq!(ten.div_euclid(&two.neg()).unwrap(), five.neg());
    assert_eq!(ten.rem_euclid(&five.neg()).unwrap(), int(0));
    // A dividend below the divisor: quotient `0`, or `-1` toward a positive divisor for a
    // negative dividend, and the dividend itself as the remainder when it is not negative.
    assert_eq!(int(5).div_euclid(&two).unwrap(), int(0));
    assert_eq!(int(5).rem_euclid(&two).unwrap(), int(5));
    assert_eq!(two.rem_euclid(&ten).unwrap(), two);
    assert_eq!(int(-5).div_euclid(&two).unwrap(), int(-1));
    assert_eq!(int(-5).div_euclid(&two.neg()).unwrap(), int(1));
    // `2^(10^12) * 3` by `2^(10^12 - 1)` is exactly 6.
    let near = int(2).pow(&(e - 1).into()).unwrap();
    assert_eq!(two.mul(&int(3)).div_euclid(&near).unwrap(), int(6));
    assert!(ten.is_even() && !five.is_even() && !int(-3).is_even() && int(0).is_even());
}

/// A base wider than 64 bits is not factored; its power is built.
#[test]
fn a_power_of_a_wide_base_is_built() {
    let wide: BigInt = (BigInt::from(1) << 64) + 13;
    let r = Rat::int(wide.clone()).pow(&7u32.into()).unwrap();
    assert_eq!(r, Rat::int(wide.pow(7u32)));
    let mixed = Rat::int(wide.clone())
        .mul(&two_to(100))
        .pow(&3u32.into())
        .unwrap();
    assert_eq!(built(&mixed), Rat::int(wide.pow(3u32) << 300));
}

/// Building, ordering, multiplying, dividing and projecting `10^n` costs a few products of
/// numbers of `log n` bits, not the `3.3 n` bits of the value.
#[test]
fn ten_to_n_costs_its_exponent_and_not_its_digits() {
    check_order(
        "10^n built, compared, multiplied and projected",
        1 << 20,
        0,
        |n| {
            let a = int(10).pow(&(n as u64).into()).unwrap();
            let b = dec(&format!("1.345e{n}"));
            assert!(a < b);
            let c = a.mul(&b);
            assert!(c > b);
            assert_eq!(c.div(&a).expect("10^n is not zero"), b);
            assert_eq!(c.div_euclid(&a).unwrap(), b);
            assert_eq!(c.rem_euclid(&b).unwrap(), int(0));
            assert_eq!(a.to_f64(), Err(LiteralRounding::Infinite));
            assert_eq!(dec(&format!("1e-{n}")).to_f64(), Err(LiteralRounding::Zero));
        },
    );
}
