//! Interval ends at the edges of `i64` and `i128`. An end has one form for each value inside
//! `i128` (a word inside `i64`, a big value past it) and may have several outside it (a big
//! value, or a kept sum of powers or roots). Equal values must hash alike and compare equal
//! whatever operation produced them, so a hash set of ends finds each value in any form. The
//! values `i128::MIN` and `i128::MAX + 1 = 2^127` are where a negation, a product or a quotient
//! of a kept value can come back inside `i128`.

use std::collections::HashSet;
use std::hash::BuildHasher;

use num_bigint::BigInt;
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::interval::{End, Num};

fn hash_of<T: std::hash::Hash>(v: &T) -> u64 {
    std::hash::BuildHasherDefault::<std::collections::hash_map::DefaultHasher>::default()
        .hash_one(v)
}

fn two_to(k: u32) -> BigInt {
    BigInt::from(1) << k
}

/// `2^k`, kept as a power once it is outside `i128`.
fn pow2(k: u32) -> Num {
    Num::from(2).pow(k)
}

/// The value of `v`, written out.
fn value(v: &Num) -> BigInt {
    v.to_string()
        .parse()
        .expect("a value prints as decimal text")
}

/// Checks that `v` is in the one form its value has when that value is inside `i128`, equals
/// and hashes as the value built directly, and lies strictly between its neighbors.
fn check(what: &str, v: &Num, want: &BigInt) {
    assert_eq!(value(v), *want, "{what}");
    let direct = Num::from(want.clone());
    assert_eq!(*v, direct, "{what}: {v} against {want}");
    assert_eq!(hash_of(v), hash_of(&direct), "{what}: hash of {v}");
    assert_eq!(
        v.to_i128(),
        i128::try_from(want).ok(),
        "{what}: form of {v}"
    );
    assert_eq!(v.to_i64(), i64::try_from(want).ok(), "{what}: form of {v}");
    let (below, above) = (Num::from(want - 1), Num::from(want + 1));
    assert!(
        below < *v && *v < above,
        "{what}: {v} between its neighbors"
    );
    assert!(
        *v > below && above > *v,
        "{what}: {v} between its neighbors"
    );
}

/// The values next to each edge: `2^63`, `2^127` and their negations, each with the two values
/// on either side.
fn edges() -> Vec<BigInt> {
    let mut out = Vec::new();
    for k in [63, 127] {
        for d in -2..=2 {
            out.push(two_to(k) + d);
            out.push(-two_to(k) + d);
        }
    }
    out
}

/// The forms in which a test builds `v`: written out, parsed, through `Int`, and as a kept sum
/// that comes back to `v`, `2^200 + v - 2^200`. Negations and absolute values of these are
/// checked too.
fn forms(v: &BigInt) -> Vec<(String, Num)> {
    let far = pow2(200);
    let mut out = vec![
        ("written out".to_string(), Num::from(v.clone())),
        (
            "parsed".to_string(),
            v.to_string().parse::<Num>().expect("decimal"),
        ),
        ("through Int".to_string(), Num::from(&Int::from(v.clone()))),
        (
            "a kept sum".to_string(),
            &(&far + &Num::from(v.clone())) - &far,
        ),
    ];
    if v.magnitude().bits() > 127 || *v == two_to(127) {
        // At and past 2^127 a power of 2 plus a small value is kept.
        let sign = if *v < BigInt::ZERO { -1 } else { 1 };
        let d = v - sign * two_to(127);
        let kept = &pow2(127) * &Num::from(sign);
        out.push(("2^127 kept, plus d".to_string(), &kept + &Num::from(d)));
    }
    out
}

#[test]
fn every_form_of_a_value_at_an_edge_hashes_and_compares_as_the_value() {
    for v in edges() {
        for (name, f) in forms(&v) {
            check(&format!("{v} {name}"), &f, &v);
            check(&format!("-({v} {name})"), &-&f, &-&v);
            let abs = BigInt::from_biguint(num_bigint::Sign::Plus, v.magnitude().clone());
            check(&format!("abs({v} {name})"), &f.abs(), &abs);
            check(&format!("{v} {name} - 0"), &(&f - &Num::ZERO), &v);
            check(&format!("{v} {name} * 1"), &(&f * &Num::ONE), &v);
            check(&format!("{v} {name} * -1"), &(&f * &Num::from(-1)), &-&v);
            check(&format!("-1 * {v} {name}"), &(&Num::from(-1) * &f), &-&v);
        }
    }
}

#[test]
fn products_quotients_and_powers_that_land_on_an_edge_have_its_one_form() {
    let min = -two_to(127);
    let past = two_to(127);
    let kept128 = pow2(128);
    let cases: Vec<(&str, Num, BigInt)> = vec![
        // Negation of the kept 2^127 is i128::MIN; of i128::MIN, the kept or big 2^127.
        ("-(2^127 kept)", -&pow2(127), min.clone()),
        ("-(i128::MIN)", -&Num::from(i128::MIN), past.clone()),
        ("-(-(2^127 kept))", -&-&pow2(127), past.clone()),
        // Products.
        (
            "2^63 * -2^64",
            &Num::from(two_to(63)) * &Num::from(-two_to(64)),
            min.clone(),
        ),
        (
            "-2^63 * -2^64",
            &Num::from(-two_to(63)) * &Num::from(-two_to(64)),
            past.clone(),
        ),
        (
            "i128::MIN * -1",
            &Num::from(i128::MIN) * &Num::from(-1),
            past.clone(),
        ),
        (
            "i64::MIN * -1",
            &Num::from(i64::MIN) * &Num::from(-1),
            two_to(63),
        ),
        (
            "(2^127 kept) * -1",
            &pow2(127) * &Num::from(-1),
            min.clone(),
        ),
        // Powers.
        ("(-2) ** 127", Num::from(-2).pow(127), min.clone()),
        ("2 ** 127", Num::from(2).pow(127), past.clone()),
        ("(-2) ** 63", Num::from(-2).pow(63), -two_to(63)),
        ("2 ** 63", Num::from(2).pow(63), two_to(63)),
        ("pow2(127)", Num::pow2(&Num::from(127)), past.clone()),
        (
            "(-(2^63)) ** 2 * 2",
            &Num::from(-two_to(63)).pow(2) * &Num::from(2),
            past.clone(),
        ),
        // Quotients: a kept value over a negative divisor is negated first.
        (
            "2^128 kept / 2",
            kept128.div_floor(&Num::from(2)),
            past.clone(),
        ),
        (
            "2^128 kept / -2",
            kept128.div_floor(&Num::from(-2)),
            min.clone(),
        ),
        (
            "(2^128 kept + 1) / -2",
            (&kept128 + &Num::ONE).div_floor(&Num::from(-2)),
            min.clone() - 1,
        ),
        (
            "(2^128 kept - 1) / -2",
            (&kept128 - &Num::ONE).div_floor(&Num::from(-2)),
            min.clone(),
        ),
        (
            "i128::MIN / -1",
            Num::from(i128::MIN).div_floor(&Num::from(-1)),
            past.clone(),
        ),
        (
            "i128::MIN div_euclid -1",
            Num::from(i128::MIN).div_euclid(&Num::from(-1)),
            past.clone(),
        ),
        (
            "2^128 kept div_euclid -2",
            kept128.div_euclid(&Num::from(-2)),
            min.clone(),
        ),
        // A shift right of a kept power by a kept power of 2.
        (
            "2^254 / 2^127",
            pow2(254).div_floor(&pow2(127)),
            past.clone(),
        ),
        (
            "-2^254 / 2^127",
            (-&pow2(254)).div_floor(&pow2(127)),
            min.clone(),
        ),
        // Remainders.
        (
            "(2^128 kept + 5) mod -(2^127 kept)",
            (&kept128 + &Num::from(5)).mod_floor(&-&pow2(127)),
            BigInt::from(5) - two_to(127),
        ),
        (
            "-(2^127 kept) mod 2^200 kept",
            (-&pow2(127)).mod_floor(&pow2(200)),
            two_to(200) - two_to(127),
        ),
        // Greatest common divisors.
        (
            "gcd(i128::MIN, i128::MIN)",
            Num::from(i128::MIN).gcd(&Num::from(i128::MIN)),
            past.clone(),
        ),
        (
            "gcd(2^128 kept, i128::MIN)",
            kept128.gcd(&Num::from(i128::MIN)),
            past.clone(),
        ),
        // Roots.
        (
            "floor_root(2^254, 2)",
            pow2(254).floor_root(2),
            past.clone(),
        ),
        (
            "ceil_root(2^254 - 1, 2)",
            (&pow2(254) - &Num::ONE).ceil_root(2),
            past.clone(),
        ),
        (
            "floor_root(2^254 - 1, 2)",
            (&pow2(254) - &Num::ONE).floor_root(2),
            past.clone() - 1,
        ),
        // Conversions from the kernel's integers, kept as powers of their primes.
        (
            "Rat 2 ** 127",
            Num::from(
                &zed_kernel::num::Rat::int(BigInt::from(2))
                    .pow(&127u32.into())
                    .expect("small"),
            ),
            past.clone(),
        ),
        (
            "Rat (-2) ** 127",
            Num::from(
                &zed_kernel::num::Rat::int(BigInt::from(-2))
                    .pow(&127u32.into())
                    .expect("small"),
            ),
            min.clone(),
        ),
        // Interval ends: the successor and predecessor across each edge.
        (
            "succ(i128::MAX)",
            fin(End::Fin(Num::from(i128::MAX)).succ()),
            past.clone(),
        ),
        (
            "pred(2^127 kept)",
            fin(End::Fin(pow2(127)).pred()),
            past.clone() - 1,
        ),
        (
            "pred(i128::MIN)",
            fin(End::Fin(Num::from(i128::MIN)).pred()),
            min.clone() - 1,
        ),
        (
            "succ(-(2^127 kept) - 1)",
            fin(End::Fin(&-&pow2(127) - &Num::ONE).succ()),
            min.clone(),
        ),
    ];
    for (what, v, want) in &cases {
        check(what, v, want);
    }
    // Every one is found in a hash set built from the values written out.
    let set: HashSet<Num> = cases.iter().map(|(_, _, w)| Num::from(w.clone())).collect();
    for (what, v, _) in &cases {
        assert!(set.contains(v), "{what}: {v} in the set");
    }
}

fn fin(e: End) -> Num {
    match e {
        End::Fin(v) => v,
        End::NegInf | End::PosInf => panic!("a finite end"),
    }
}

#[test]
fn integers_at_the_edge_of_i128_have_one_form() {
    let min = Int::from(i128::MIN);
    let past = &Int::from(i128::MAX) + &Int::ONE;
    let cases: Vec<(&str, Int, BigInt)> = vec![
        ("-(i128::MIN)", -&min, two_to(127)),
        ("-(2^127)", -&past, -two_to(127)),
        ("abs(i128::MIN)", min.abs(), two_to(127)),
        ("i128::MIN * -1", &min * &Int::from(-1), two_to(127)),
        ("2^127 * -1", &past * &Int::from(-1), -two_to(127)),
        ("2^127 - 1", &past - &Int::ONE, two_to(127) - 1),
        (
            "i128::MIN - 1 + 1",
            &(&min - &Int::ONE) + &Int::ONE,
            -two_to(127),
        ),
        ("gcd(i128::MIN, 0)", min.gcd(&Int::ZERO), two_to(127)),
        (
            "2^128 / 2",
            Int::from(two_to(128)).div_floor(&Int::from(2)),
            two_to(127),
        ),
        (
            "2^127 mod 2^127 + 1",
            past.mod_floor(&(&past + &Int::ONE)),
            two_to(127),
        ),
        ("through Num", Int::from(&-&pow2(127)), -two_to(127)),
    ];
    for (what, v, want) in &cases {
        let direct = Int::from(want.clone());
        assert_eq!(*v, direct, "{what}");
        assert_eq!(hash_of(v), hash_of(&direct), "{what}: hash");
        assert_eq!(v.to_i128(), i128::try_from(want).ok(), "{what}: form");
        assert_eq!(v.to_string(), want.to_string(), "{what}");
    }
}

/// `±2^k + d` in one of four forms, with its value written out: written out, a kept sum that
/// comes back to it, a kept or big `±2^k` plus `d`, and the negation of `-(±2^k + d)` written
/// out.
fn near_edge(k: u32, negative: bool, d: i64, form: usize) -> (Num, BigInt) {
    let sign = if negative { -1 } else { 1 };
    let want: BigInt = sign * two_to(k) + d;
    let v = match form {
        0 => Num::from(want.clone()),
        1 => {
            let far = pow2(130 + k);
            &(&far + &Num::from(want.clone())) - &far
        }
        2 => &(&pow2(k) * &Num::from(sign)) + &Num::from(d),
        _ => -&Num::from(-&want),
    };
    (v, want)
}

/// One random operation that keeps a value near an edge, on the value and on its value written
/// out.
fn step(rng: &mut Rng, v: &Num, want: &BigInt) -> (Num, BigInt) {
    match rng.below(6) {
        // Negation, the operation at the edge of i128, twice as often as each other.
        0 | 1 => (-v, -want),
        2 => {
            let d = rng.int(-2, 2);
            (v + &Num::from(d), want + d)
        }
        3 => (v * &Num::from(-1), -want),
        4 => (
            v.abs(),
            BigInt::from_biguint(num_bigint::Sign::Plus, want.magnitude().clone()),
        ),
        _ => {
            let (x, _) = near_edge(127 + rng.below(3) as u32, rng.below(2) == 0, 0, 1);
            (&(v + &x) - &x, want.clone())
        }
    }
}

#[test]
fn random_values_near_the_edges_hash_alike_exactly_when_equal() {
    let mut rng = Rng::new(127);
    let mut seen: Vec<(Num, BigInt)> = Vec::new();
    // Every start, in every form, then three random walks of one to four operations from it,
    // each result checked.
    for k in [63, 64, 127, 128] {
        for negative in [false, true] {
            for d in -2..=2 {
                for form in 0..4 {
                    let start = near_edge(k, negative, d, form);
                    check("a start", &start.0, &start.1);
                    for _ in 0..3 {
                        let (mut v, mut want) = start.clone();
                        for _ in 0..1 + rng.below(4) {
                            (v, want) = step(&mut rng, &v, &want);
                            check("a random walk", &v, &want);
                            seen.push((v.clone(), want.clone()));
                        }
                    }
                }
            }
        }
    }
    // Over every pair: equal values hash alike, and the order agrees with the values.
    for (a, wa) in &seen {
        for (b, wb) in &seen {
            assert_eq!(a.cmp(b), wa.cmp(wb), "{a} against {b}");
            if a == b {
                assert_eq!(hash_of(a), hash_of(b), "{a} against {b}");
            }
        }
    }
    let set: HashSet<Num> = seen.iter().map(|(v, _)| v.clone()).collect();
    let distinct: HashSet<BigInt> = seen.iter().map(|(_, w)| w.clone()).collect();
    assert_eq!(set.len(), distinct.len(), "one entry per value");
}

/// The negation of a kept value of `n` terms, checked against the edge `2^127`, costs the
/// terms, not their product or the digits of the value.
#[test]
fn negating_a_kept_sum_scales_with_its_terms() {
    /// `b ** 200` over the odd `b` from `3 + 2 * lo` to below `3 + 2 * hi`, added in halves so
    /// that building it costs `n log n` term operations.
    fn sum(lo: usize, hi: usize) -> Num {
        if hi - lo == 1 {
            return Num::from(3 + 2 * lo as i64).pow(200);
        }
        let mid = lo + (hi - lo) / 2;
        &sum(lo, mid) + &sum(mid, hi)
    }
    let sums = [sum(0, 200), sum(0, 1600)];
    scaling::check("negating a kept sum of n powers", 200, |n| {
        let s = &sums[usize::from(n != 200)];
        let neg = -s;
        assert!(neg.signum() < 0);
    });
    // A quotient by a negative divisor negates both first, then takes residues of the terms.
    scaling::check("a kept sum of n powers over a negative divisor", 200, |n| {
        let s = &sums[usize::from(n != 200)];
        let q = s.div_floor(&Num::from(-7));
        assert!(q.signum() < 0);
    });
}
