//! The exact numbers of `num` (plan row TEST-complete-kernel, author P189): Euclidean `div` and
//! `mod` at each pair of signs, plain and kept forms; `^` by an integer at the bases `0`, `1`
//! and `-1` and at others, each sign and parity of the exponent; the nearest `f64` and `f32` at
//! zero, the subnormals, the ties and past the largest finite; `-x`, parity, the built parts
//! and the literal text. Expected results from DESIGN.md L1.17, L1.18 and sec:domains.

use std::borrow::Cow;

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::num::{LiteralRounding, Rat};

fn int(n: i64) -> Rat {
    Rat::int(BigInt::from(n))
}

fn ratio(n: i64, d: i64) -> Rat {
    Rat::new(BigInt::from(n), BigInt::from(d)).expect("a nonzero denominator")
}

/// The value of a decimal literal's text, such as `1e400000`, kept as powers of 2 and 5.
fn dec(text: &str) -> Rat {
    Rat::decimal(text).expect("memory").expect("a decimal")
}

/// `2^k` kept as a power, for any `k`.
fn two_to(k: i64) -> Rat {
    Rat::from_kept(BigInt::one(), BigInt::one(), vec![(2, BigInt::from(k))]).expect("a kept form")
}

/// `a div m` and `a mod m` are Euclidean: `a = m (a div m) + (a mod m)` with `0 <= a mod m <
/// |m|`, so `-1 div 4, -1 mod 4` is `-1, 3` (DESIGN.md L1.18, `div` and `mod`).
#[test]
fn euclidean_division_at_each_pair_of_signs() {
    let cases = [
        // (a, m, a div m, a mod m)
        (7, 2, 3, 1),
        (-7, 2, -4, 1),
        (7, -2, -3, 1),
        (-7, -2, 4, 1),
        (-1, 4, -1, 3),
        (1, -4, 0, 1),
        (-4, 4, -1, 0),
        (4, -4, -1, 0),
        (0, 5, 0, 0),
        (0, -5, 0, 0),
        (3, 5, 0, 3),
        (-3, -5, 1, 2),
        (i64::MAX, 1, i64::MAX, 0),
        (i64::MIN, -1, 0, 0),
        (i64::MIN, 7, -1317624576693539402, 6),
    ];
    for (a, m, q, r) in cases {
        let (ra, rm) = (int(a), int(m));
        let want_q = match (a, m) {
            (i64::MIN, -1) => Rat::int(-BigInt::from(i64::MIN)),
            _ => int(q),
        };
        assert_eq!(ra.div_euclid(&rm).expect("memory"), want_q, "{a} div {m}");
        assert_eq!(ra.rem_euclid(&rm).expect("memory"), int(r), "{a} mod {m}");
    }
}

/// Euclidean division of kept powers, built or not: `2^100 mod 7`, `-(2^100) mod 7`, `10^1000
/// mod 7` from a literal, an exact division keeping the powers, a dividend below `|m|`, a kept
/// divisor.
#[test]
fn euclidean_division_of_kept_powers() {
    let big = BigInt::one() << 100u32;
    let p = two_to(100);
    let seven = int(7);
    let check = |a: &Rat, m: &Rat, a_built: &BigInt, m_built: &BigInt| {
        // Euclidean: the remainder in `0 ..< |m|`.
        let r = a_built.mod_floor(&BigInt::from(m_built.magnitude().clone()));
        let q = (a_built - &r) / m_built;
        assert_eq!(
            a.rem_euclid(m).expect("memory"),
            Rat::int(r.clone()),
            "{a} mod {m}"
        );
        assert_eq!(a.div_euclid(m).expect("memory"), Rat::int(q), "{a} div {m}");
    };
    check(&p, &seven, &big, &BigInt::from(7));
    check(&p.neg(), &seven, &-&big, &BigInt::from(7));
    check(&p.neg(), &seven.neg(), &-&big, &BigInt::from(-7));
    check(&p, &two_to(30), &big, &(BigInt::one() << 30u32));
    check(&int(5), &p, &BigInt::from(5), &big);
    check(&int(-5), &p, &BigInt::from(-5), &big);
    let tens = dec("1e1000");
    let ten_k = num_traits::pow(BigInt::from(10), 1000);
    check(&tens, &seven, &ten_k, &BigInt::from(7));
    check(&tens, &int(-3), &ten_k, &BigInt::from(-3));
    // An exact division keeps the powers: `2^100 div 2^30` is `2^70` as a kept power.
    assert_eq!(p.div_euclid(&two_to(30)).expect("memory"), two_to(70));
}

/// `x ^ n` by an integer `n` (DESIGN.md L1.17): `0`, `1` and `-1` to any power stay small,
/// read from the sign and parity of `n` alone, a huge `n` included; `0 ^ n` with `n < 0` is
/// `#divByZero` (`None` here); a negative `n` inverts the power, the sign kept on the
/// numerator.
#[test]
fn powers_by_an_integer() {
    let huge_even = two_to(200);
    let huge_odd = huge_even.add(&int(1)).expect("memory");
    let cases: Vec<(Rat, Rat, Option<Rat>)> = vec![
        (int(0), int(0), Some(int(1))),
        (int(0), int(3), Some(int(0))),
        (int(0), huge_even.clone(), Some(int(0))),
        (int(0), int(-1), None),
        (int(0), huge_even.neg(), None),
        (int(1), huge_odd.clone(), Some(int(1))),
        (int(1), huge_odd.neg(), Some(int(1))),
        (int(-1), huge_even.clone(), Some(int(1))),
        (int(-1), huge_odd.clone(), Some(int(-1))),
        (int(-1), huge_odd.neg(), Some(int(-1))),
        (int(-1), int(0), Some(int(1))),
        (int(2), int(10), Some(int(1024))),
        (int(2), int(-2), Some(ratio(1, 4))),
        (int(-2), int(3), Some(int(-8))),
        (int(-2), int(-3), Some(ratio(-1, 8))),
        (ratio(2, 3), int(-3), Some(ratio(27, 8))),
        (ratio(-2, 3), int(-3), Some(ratio(-27, 8))),
        (ratio(-2, 3), int(2), Some(ratio(4, 9))),
        (dec("0.5"), int(-2), Some(int(4))),
        (two_to(-3), int(-2), Some(int(64))),
        (ratio(7, 5), int(0), Some(int(1))),
    ];
    for (x, n, want) in cases {
        assert_eq!(x.pow_int(&n).expect("memory"), want, "{x} ^ {n}");
    }
    // A large power is kept, not built: `3 ^ 2^20` holds its exponent.
    let p = int(3)
        .pow_int(&two_to(20))
        .expect("memory")
        .expect("a value");
    let (_, pows) = p.integer_factors();
    assert_eq!(pows, &[(3, BigInt::one() << 20u32)]);
}

/// The nearest `f64` and `f32`, ties to even, and the two refusals: a value past the largest
/// finite float rounds to infinity, and a nonzero value at most half the least subnormal
/// rounds to zero (DESIGN.md L1.18: `f64` of an `int` or a `rat` is `#overflow` beyond the
/// largest finite value).
#[test]
fn nearest_floats() {
    let f64_cases: Vec<(Rat, Result<f64, LiteralRounding>)> = vec![
        (int(0), Ok(0.0)),
        (int(1), Ok(1.0)),
        (int(-3), Ok(-3.0)),
        (ratio(1, 3), Ok(1.0 / 3.0)),
        (ratio(-1, 3), Ok(-1.0 / 3.0)),
        (dec("0.1"), Ok(0.1)),
        (dec("1e308"), Ok(1e308)),
        (dec("1e309"), Err(LiteralRounding::Infinite)),
        (dec("-1e309"), Err(LiteralRounding::Infinite)),
        (two_to(1023), Ok(2f64.powi(1023))),
        (two_to(1024), Err(LiteralRounding::Infinite)),
        // The largest finite, and the tie above it, which rounds to even: past the largest.
        (
            two_to(1024).sub(&two_to(971)).expect("memory"),
            Ok(f64::MAX),
        ),
        (
            two_to(1024).sub(&two_to(970)).expect("memory"),
            Err(LiteralRounding::Infinite),
        ),
        (
            two_to(1024)
                .sub(&two_to(970))
                .expect("memory")
                .sub(&int(1))
                .expect("memory"),
            Ok(f64::MAX),
        ),
        // The least subnormal, half of it (a tie to even: zero), and three quarters of it.
        (two_to(-1074), Ok(f64::from_bits(1))),
        (two_to(-1074).neg(), Ok(-f64::from_bits(1))),
        (two_to(-1075), Err(LiteralRounding::Zero)),
        (
            two_to(-1075).add(&two_to(-1200)).expect("memory"),
            Ok(f64::from_bits(1)),
        ),
        (
            two_to(-1076).mul(&int(3)).expect("memory"),
            Ok(f64::from_bits(1)),
        ),
        // A tie between two subnormals, to the even one: 1.5 and 2.5 times the least.
        (
            two_to(-1075).mul(&int(3)).expect("memory"),
            Ok(f64::from_bits(2)),
        ),
        (
            two_to(-1075).mul(&int(5)).expect("memory"),
            Ok(f64::from_bits(2)),
        ),
        (dec("1e-400"), Err(LiteralRounding::Zero)),
        (two_to(-1022), Ok(f64::MIN_POSITIVE)),
        // 1 + 2^-53 is the tie between 1 and the next float: to even, 1.
        (int(1).add(&two_to(-53)).expect("memory"), Ok(1.0)),
        (
            int(1)
                .add(&two_to(-53))
                .expect("memory")
                .add(&two_to(-100))
                .expect("memory"),
            Ok(1.0 + f64::EPSILON),
        ),
    ];
    for (x, want) in f64_cases {
        let got = x.to_f64();
        match (&got, &want) {
            (Ok(g), Ok(w)) => assert_eq!(g.to_bits(), w.to_bits(), "f64 of {x}"),
            _ => assert_eq!(got, want, "f64 of {x}"),
        }
    }
    let f32_cases: Vec<(Rat, Result<f32, LiteralRounding>)> = vec![
        (int(0), Ok(0.0)),
        (int(-7), Ok(-7.0)),
        (dec("0.1"), Ok(0.1f32)),
        (int(16_777_217), Ok(16_777_216.0)),
        (int(16_777_219), Ok(16_777_220.0)),
        (two_to(127), Ok(2f32.powi(127))),
        (two_to(128), Err(LiteralRounding::Infinite)),
        (
            two_to(128).sub(&two_to(103)).expect("memory"),
            Err(LiteralRounding::Infinite),
        ),
        (two_to(128).sub(&two_to(104)).expect("memory"), Ok(f32::MAX)),
        (two_to(-149), Ok(f32::from_bits(1))),
        (two_to(-150), Err(LiteralRounding::Zero)),
        (two_to(-150).neg(), Err(LiteralRounding::Zero)),
        (
            two_to(-150).mul(&int(3)).expect("memory"),
            Ok(f32::from_bits(2)),
        ),
        (dec("1e39"), Err(LiteralRounding::Infinite)),
    ];
    for (x, want) in f32_cases {
        let got = x.to_f32();
        match (&got, &want) {
            (Ok(g), Ok(w)) => assert_eq!(g.to_bits(), w.to_bits(), "f32 of {x}"),
            _ => assert_eq!(got, want, "f32 of {x}"),
        }
    }
}

/// `-x` by `neg` and `try_neg` at zero, each sign, a fraction and a kept power, and `abs`.
#[test]
fn negation() {
    for (x, want) in [
        (int(0), int(0)),
        (int(5), int(-5)),
        (int(-5), int(5)),
        (ratio(-1, 3), ratio(1, 3)),
        (two_to(100), two_to(100).neg()),
        (two_to(-100).neg(), two_to(-100)),
    ] {
        assert_eq!(x.neg(), want, "-{x}");
        assert_eq!(x.try_neg().expect("memory"), want, "-{x}");
        assert_eq!(x.try_neg().expect("memory").try_neg().expect("memory"), x);
        assert_eq!(
            x.abs(),
            if x.is_negative() { want } else { x.clone() },
            "abs {x}"
        );
    }
    assert!(!int(0).neg().is_negative());
}

/// Parity of an integer: zero, each sign, odd and even coefficients, and kept powers of 2 and
/// of another prime.
#[test]
fn parity() {
    for (x, even) in [
        (int(0), true),
        (int(1), false),
        (int(-1), false),
        (int(2), true),
        (int(-4), true),
        (int(i64::MAX), false),
        (int(i64::MIN), true),
        (two_to(100), true),
        (two_to(100).neg(), true),
        (
            int(1)
                .pow_int(&two_to(20))
                .expect("memory")
                .expect("a value"),
            false,
        ),
        (
            int(3).pow_int(&int(50)).expect("memory").expect("a value"),
            false,
        ),
        (
            int(3)
                .pow_int(&two_to(20))
                .expect("memory")
                .expect("a value"),
            false,
        ),
        (
            int(6)
                .pow_int(&two_to(20))
                .expect("memory")
                .expect("a value"),
            true,
        ),
        (dec("1e100"), true),
        (dec("5e100"), true),
        (dec("1.5e1"), false),
        (dec("2.5e1"), false),
    ] {
        assert!(x.is_integer(), "{x}");
        assert_eq!(x.is_even(), even, "{x}");
    }
}

/// `|N|` and `D` of `±N/D` in lowest terms, built: the same for every form of one value, a
/// side with no powers (here the numerator) borrowed.
#[test]
fn built_parts() {
    let big = BigUint::one() << 100u32;
    let five = |k: u32| num_traits::pow(BigUint::from(5u32), k as usize);
    let cases: Vec<(Rat, BigUint, BigUint, bool)> = vec![
        (int(0), BigUint::zero(), BigUint::one(), true),
        (int(-6), BigUint::from(6u32), BigUint::one(), true),
        (ratio(-2, 3), BigUint::from(2u32), BigUint::from(3u32), true),
        (two_to(100), big.clone(), BigUint::one(), false),
        (two_to(-100).neg(), BigUint::one(), big.clone(), true),
        (dec("2.5e-3"), BigUint::one(), BigUint::from(400u32), true),
        (dec("-1e20"), five(20) << 20u32, BigUint::one(), false),
    ];
    for (x, n, d, borrowed) in cases {
        let (got_n, got_d) = x.built_parts().expect("memory");
        assert_eq!((got_n.as_ref(), got_d.as_ref()), (&n, &d), "{x}");
        assert_eq!(
            matches!(got_n, Cow::Borrowed(_)),
            borrowed,
            "{x}, numerator borrowed"
        );
    }
    // Two forms of 2^100 build alike.
    let plain = Rat::int(BigInt::from(big.clone()));
    assert_eq!(
        plain.built_parts().expect("memory"),
        two_to(100).built_parts().expect("memory")
    );
}

/// The literal text of a value, as the type syntax writes it: `meKr` for a decimal, `m` not
/// divisible by 10, `0r` for zero, and the quotient `nr/dr` for a value that is no decimal;
/// equal values print alike whatever form they hold.
#[test]
fn literal_texts() {
    for (x, want) in [
        (int(0), "0r"),
        (int(7), "7r"),
        (int(-7), "-7r"),
        (int(70), "7e1r"),
        (dec("0.5"), "5e-1r"),
        (dec("-25e9"), "-25e9r"),
        (dec("1e400000"), "1e400000r"),
        (dec("2.50"), "25e-1r"),
        (dec("0.125"), "125e-3r"),
        (ratio(1, 8), "125e-3r"),
        (two_to(-3), "125e-3r"),
        (two_to(10), "1024r"),
        (ratio(1, 3), "1r/3r"),
        (ratio(-2, 3), "-2r/3r"),
        (two_to(-1).mul(&ratio(1, 3)).expect("memory"), "1r/6r"),
    ] {
        assert_eq!(x.literal_text(), want, "{x}");
    }
}
