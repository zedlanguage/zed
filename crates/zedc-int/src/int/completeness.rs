//! Completeness tests for [`Int`] and the root, strip and remainder helpers (row
//! TEST-complete-crates, author P189). Each test walks a table of small cases; each assertion
//! names its case. Expected results are the integers' own arithmetic (DESIGN.md sec:domains,
//! "exact, over unbounded integers"), computed here with num-bigint or written out. The case
//! list is crates/zedc-int/COMPLETENESS.md.

use std::collections::HashSet;

use super::*;

/// `2^k` as an [`Int`].
fn pow2(k: u32) -> Int {
    Int::from(BigInt::from(1) << k)
}

/// Values at every end of the two forms: zero, the units, the ends of `i64` and `i128` and one
/// past each, and values past 128 bits, each with both signs.
fn ends() -> Vec<BigInt> {
    let mut v: Vec<BigInt> = [
        BigInt::from(1),
        BigInt::from(2),
        BigInt::from(3),
        BigInt::from(6),
        BigInt::from(i64::MAX),
        BigInt::from(i64::MAX) + 1,
        BigInt::from(i128::MAX) - 1,
        BigInt::from(i128::MAX),
        BigInt::from(i128::MAX) + 1,
        BigInt::from(i128::MAX) + 2,
        BigInt::from(1) << 200u32,
        (BigInt::from(1) << 200u32) + 1,
        BigInt::from(3).pow(100u32),
    ]
    .to_vec();
    v.extend(v.clone().into_iter().map(|x| -x));
    v.push(BigInt::zero());
    v
}

#[test]
fn every_constructor_gives_one_form_per_value() {
    // Each machine type, at its ends, equals the value made from a BigInt, hashes alike and
    // reads back by to_i128.
    let cases: Vec<(&str, Int, i128)> = vec![
        ("default", Int::default(), 0),
        ("ZERO", Int::ZERO, 0),
        ("ONE", Int::ONE, 1),
        ("i32 min", Int::from(i32::MIN), i32::MIN.into()),
        ("i32 max", Int::from(i32::MAX), i32::MAX.into()),
        ("i64 min", Int::from(i64::MIN), i64::MIN.into()),
        ("i64 max", Int::from(i64::MAX), i64::MAX.into()),
        ("usize 0", Int::from(0usize), 0),
        ("usize max", Int::from(usize::MAX), usize::MAX as i128),
        ("i128 min", Int::from(i128::MIN), i128::MIN),
        ("i128 max", Int::from(i128::MAX), i128::MAX),
    ];
    for (case, x, v) in cases {
        let from_big = Int::from(BigInt::from(v));
        assert_eq!(x, from_big, "{case}");
        assert_eq!(x.to_i128(), Some(v), "{case}");
        let set: HashSet<Int> = [x.clone(), from_big].into_iter().collect();
        assert_eq!(set.len(), 1, "{case}: equal values hash alike");
        assert_eq!(x.to_string(), v.to_string(), "{case}: decimal text");
    }
    // A BigInt past i128 has no machine value, and a sum that comes back into i128 has the
    // machine form again: equal to, and hashing as, the value made directly.
    for (case, b) in [
        ("i128 max + 1", BigInt::from(i128::MAX) + 1),
        ("i128 min - 1", BigInt::from(i128::MIN) - 1),
        ("2^200", BigInt::from(1) << 200u32),
        ("-2^200", -(BigInt::from(1) << 200u32)),
    ] {
        let x = Int::from(b.clone());
        assert_eq!(x.to_i128(), None, "{case}");
        assert_eq!(x.to_string(), b.to_string(), "{case}: decimal text");
        let back = &x - &Int::from(b.clone() - 5);
        assert_eq!(back, Int::from(5), "{case} minus (itself - 5)");
        let set: HashSet<Int> = [back, Int::from(5)].into_iter().collect();
        assert_eq!(
            set.len(),
            1,
            "{case}: a value back in i128 hashes as itself"
        );
    }
}

#[test]
fn sign_parity_and_unit_tests_on_both_forms() {
    // (case, value, negative, positive, zero, odd, unit)
    let big = BigInt::from(1) << 200u32;
    let cases: Vec<(&str, Int, [bool; 5])> = vec![
        ("0", Int::ZERO, [false, false, true, false, false]),
        ("1", Int::ONE, [false, true, false, true, true]),
        ("-1", Int::from(-1), [true, false, false, true, true]),
        ("2", Int::from(2), [false, true, false, false, false]),
        ("-2", Int::from(-2), [true, false, false, false, false]),
        ("-3", Int::from(-3), [true, false, false, true, false]),
        (
            "i128 min",
            Int::from(i128::MIN),
            [true, false, false, false, false],
        ),
        (
            "i128 max",
            Int::from(i128::MAX),
            [false, true, false, true, false],
        ),
        (
            "2^200",
            Int::from(big.clone()),
            [false, true, false, false, false],
        ),
        (
            "2^200 + 1",
            Int::from(&big + 1),
            [false, true, false, true, false],
        ),
        (
            "-2^200",
            Int::from(-&big),
            [true, false, false, false, false],
        ),
        (
            "-2^200 - 1",
            Int::from(-&big - 1),
            [true, false, false, true, false],
        ),
    ];
    for (case, x, want) in cases {
        let got = [
            x.is_negative(),
            x.is_positive(),
            x.is_zero(),
            x.is_odd(),
            x.is_unit(),
        ];
        assert_eq!(got, want, "{case}: negative, positive, zero, odd, unit");
    }
}

#[test]
fn abs_and_negation_cross_the_end_of_i128_both_ways() {
    let past = &Int::from(i128::MAX) + &Int::ONE; // 2^127
    let cases: Vec<(&str, Int, Int, Int)> = vec![
        // (case, x, -x, |x|)
        ("0", Int::ZERO, Int::ZERO, Int::ZERO),
        ("5", Int::from(5), Int::from(-5), Int::from(5)),
        ("-5", Int::from(-5), Int::from(5), Int::from(5)),
        (
            "i128 max",
            Int::from(i128::MAX),
            Int::from(-i128::MAX),
            Int::from(i128::MAX),
        ),
        ("i128 min", Int::from(i128::MIN), past.clone(), past.clone()),
        ("2^127", past.clone(), Int::from(i128::MIN), past.clone()),
        ("2^200", pow2(200), -&pow2(200), pow2(200)),
        ("-2^200", -&pow2(200), pow2(200), pow2(200)),
    ];
    for (case, x, neg, abs) in cases {
        assert_eq!(-&x, neg, "{case}: negation");
        assert_eq!(x.abs(), abs, "{case}: absolute value");
        assert_eq!(-&(-&x), x, "{case}: negated twice");
    }
    // -2^127 made by negation is the machine value: it reads back as i128::MIN.
    assert_eq!((-&past).to_i128(), Some(i128::MIN));
}

#[test]
fn sums_differences_and_products_agree_with_num_bigint_on_every_path() {
    // Each pair of ends: both machine values with no overflow, overflow into the wide form,
    // the wide form coming back into i128, both wide; products of 64-bit values (one
    // instruction), of 128-bit values that fit, and that overflow.
    let ends = ends();
    for a in &ends {
        for b in &ends {
            let (x, y) = (Int::from(a.clone()), Int::from(b.clone()));
            assert_eq!(&x + &y, Int::from(a + b), "{a} + {b}");
            assert_eq!(&x - &y, Int::from(a - b), "{a} - {b}");
            assert_eq!(&x * &y, Int::from(a * b), "{a} * {b}");
            assert_eq!(x.cmp(&y), a.cmp(b), "{a} against {b}");
            assert_eq!(x == y, a == b, "{a} == {b}");
        }
    }
}

#[test]
fn order_puts_each_wide_value_outside_every_machine_value() {
    let small = [i128::MIN, -1, 0, 1, i128::MAX].map(Int::from);
    let above = pow2(127);
    let below = -&(&pow2(127) + &Int::ONE);
    for s in &small {
        assert!(s < &above && &above > s, "{s} below 2^127");
        assert!(s > &below && &below < s, "{s} above -2^127 - 1");
    }
    assert!(below < above);
    // Sorting mixes the forms and keeps the order of the values.
    let mut v: Vec<Int> = vec![
        above.clone(),
        Int::ZERO,
        below.clone(),
        pow2(200),
        -&pow2(200),
    ];
    v.sort();
    assert_eq!(v, vec![-&pow2(200), below, Int::ZERO, above, pow2(200)]);
}

#[test]
fn the_gcd_on_every_path_is_the_nonnegative_gcd() {
    // Pairs that reach each arm of `gcd`: two machine values in 64 bits and in 128; a gcd of
    // 2^127, which does not fit; zero against a wide value either side; a unit against a wide
    // value; a machine value against a wide one whose odd part is 1, one word, or past a word;
    // two wide values.
    let wide: BigInt = BigInt::from(3).pow(90u32) * BigInt::from(2).pow(80u32) * 7;
    let cases: Vec<(&str, BigInt, BigInt)> = vec![
        ("0, 0", BigInt::zero(), BigInt::zero()),
        ("64-bit", BigInt::from(-84), BigInt::from(36)),
        (
            "128-bit",
            BigInt::from(i128::MAX - 1),
            BigInt::from(i128::MAX / 3 * 2),
        ),
        (
            "i128 min with itself",
            BigInt::from(i128::MIN),
            BigInt::from(i128::MIN),
        ),
        ("0 against wide", BigInt::zero(), -wide.clone()),
        ("wide against 0", -wide.clone(), BigInt::zero()),
        ("1 against wide", BigInt::from(1), wide.clone()),
        ("wide against -1", wide.clone(), BigInt::from(-1)),
        (
            "power of 2 against wide",
            BigInt::from(1) << 100u32,
            wide.clone(),
        ),
        (
            "power of 2 past wide's twos",
            BigInt::from(1) << 120u32,
            wide.clone(),
        ),
        ("odd word against wide", BigInt::from(21), wide.clone()),
        ("odd word sharing nothing", BigInt::from(11), wide.clone()),
        (
            "odd part past a word",
            (BigInt::from(1) << 100u32) + 1,
            wide.clone(),
        ),
        (
            "odd part past a word, shared",
            BigInt::from(3).pow(70u32),
            wide.clone(),
        ),
        (
            "wide against wide",
            wide.clone(),
            BigInt::from(6).pow(85u32),
        ),
    ];
    for (case, a, b) in cases {
        let want = Int::from(Integer::gcd(&a, &b));
        for (sa, sb) in [(1, 1), (-1, 1), (1, -1), (-1, -1)] {
            let (x, y) = (Int::from(&a * sa), Int::from(&b * sb));
            assert_eq!(x.gcd(&y), want, "{case}, signs {sa} {sb}: gcd");
            assert_eq!(y.gcd(&x), want, "{case}, signs {sa} {sb}: gcd swapped");
        }
    }
}

#[test]
fn the_extended_gcd_gives_bezout_coefficients_for_every_sign() {
    let ends = ends();
    for a in &ends {
        for b in &ends {
            let (x, y) = (Int::from(a.clone()), Int::from(b.clone()));
            let (g, s, t) = x.extended_gcd(&y).expect("an extended gcd exists");
            assert_eq!(g, Int::from(Integer::gcd(a, b)), "gcd of {a} and {b}");
            assert_eq!(&(&s * &x) + &(&t * &y), g, "{s}·{a} + {t}·{b}");
        }
    }
}

#[test]
fn floor_and_ceiling_division_agree_with_num_integer_for_every_sign() {
    // Machine and wide divisors, every sign, exact and inexact quotients, a dividend below the
    // divisor (quotient 0 or -1), and zero.
    let ends = ends();
    for a in &ends {
        for m in ends.iter().filter(|m| !m.is_zero()) {
            let (x, y) = (Int::from(a.clone()), Int::from(m.clone()));
            let want = (Int::from(a.div_floor(m)), Int::from(a.mod_floor(m)));
            assert_eq!((x.div_floor(&y), x.mod_floor(&y)), want, "{a} by {m}");
            assert_eq!(
                x.div_ceil(&y),
                Int::from(Integer::div_ceil(a, m)),
                "{a} by {m}, ceil"
            );
            // The symmetric remainder: congruent, at most half of |m|, odd in `a`.
            let h = x.mod_hat(&y);
            assert!((&x - &h).mod_floor(&y).is_zero(), "{a} mod^ {m}");
            assert!(&h.abs() + &h.abs() <= y.abs(), "{a} mod^ {m} = {h}");
            assert_eq!((-&x).mod_hat(&y), -&h, "-{a} mod^ {m}");
        }
    }
    // Exact multiples of a wide divisor have remainder zero for every sign.
    let m = BigInt::from(3).pow(100u32);
    for k in [-3, -1, 1, 3] {
        let a = Int::from(&m * k);
        for d in [m.clone(), -m.clone()] {
            let r = a.mod_floor(&Int::from(d.clone()));
            assert!(r.is_zero(), "{k}·3^100 mod {d}");
        }
    }
}

/// The tie of the symmetric remainder: at exactly half of `|m|` the value takes the sign
/// opposite to the dividend, so `mod_hat` is odd (REPORT-dryA1 row 2: the copy in
/// `presburger::exact::projection` gave `-1 mod^ 2 == -1 == 1 mod^ 2`).
#[test]
fn the_symmetric_remainder_at_half_the_modulus_is_odd() {
    let wide = pow2(200);
    for (a, m) in [
        (Int::from(1), Int::from(2)),
        (Int::from(3), Int::from(6)),
        (Int::from(5), Int::from(-2)),
        // 3·2^200 mod 2^201 is 2^200, half the modulus.
        (&(&wide + &wide) + &wide, &wide + &wide),
    ] {
        assert_eq!((-&a).mod_hat(&m), -&a.mod_hat(&m), "{a} mod^ {m}");
        assert_eq!(
            &a.mod_hat(&m).abs() + &a.mod_hat(&m).abs(),
            m.abs(),
            "{a} mod^ {m}"
        );
    }
    assert_eq!(Int::from(1).mod_hat(&Int::from(2)), Int::from(-1));
    assert_eq!(Int::from(-1).mod_hat(&Int::from(2)), Int::from(1));
}

/// The checked `i128` divisions agree with num-integer's on every sign, give every quotient
/// that fits (also for `MIN`, where `-((-n) div d)` overflows), and answer `None` for a zero
/// divisor and for `MIN / -1`.
#[test]
fn checked_i128_floor_and_ceiling_divisions_cover_every_sign_and_end() {
    let ends: Vec<i128> = [
        0,
        1,
        2,
        3,
        6,
        7,
        i128::from(i64::MAX),
        i128::MAX - 1,
        i128::MAX,
    ]
    .into_iter()
    .flat_map(|x| [x, -x])
    .chain([i128::MIN, i128::MIN + 1])
    .collect();
    for &n in &ends {
        for &d in &ends {
            let (nb, db) = (BigInt::from(n), BigInt::from(d));
            let fit = |q: BigInt| i128::try_from(q).ok();
            let (floor, ceil) = if d == 0 {
                (None, None)
            } else {
                (fit(nb.div_floor(&db)), fit(Integer::div_ceil(&nb, &db)))
            };
            assert_eq!(i128_div_floor(n, d), floor, "floor({n} / {d})");
            assert_eq!(i128_div_ceil(n, d), ceil, "ceil({n} / {d})");
        }
    }
}

/// The value nearest zero in a range: 0 inside, the nearer end outside, a missing end
/// unbounded, and `hi` (or 0) on an empty range, as the solver's copies it replaced
/// gave on every range that is not empty.
#[test]
fn the_value_nearest_zero_in_a_range() {
    let n = |x: i64| Some(Int::from(x));
    let cases: [(Option<Int>, Option<Int>, i64); 10] = [
        (None, None, 0),
        (n(-3), n(4), 0),
        (n(2), n(9), 2),
        (n(-9), n(-2), -2),
        (n(5), None, 5),
        (n(-5), None, 0),
        (None, n(-5), -5),
        (None, n(5), 0),
        (n(7), n(3), 3),
        (n(-3), n(-7), -7),
    ];
    for (lo, hi, want) in cases {
        let got = Int::nearest_zero(lo.as_ref(), hi.as_ref());
        assert_eq!(got, Int::from(want), "nearest zero in [{lo:?}, {hi:?}]");
    }
    let w = pow2(200);
    assert_eq!(Int::nearest_zero(Some(&w), None), w);
    assert_eq!(Int::nearest_zero(None, Some(&-&w)), -&w);
}

/// `row_range(a, k, eq)` holds exactly the `x` in `-40..=40` with `a·x + k >= 0` (or `== 0`),
/// for every `a` in `-7..=7` but 0 and `k` in `-30..=30`, the flag set exactly when an
/// equality has no integer root; `meet_range` and `range_meet` agree with the intersection
/// of the sets, and `range_is_empty` with its emptiness. Every root is within `|x| <= 30`, so
/// the window holds both sides of each bound.
#[test]
fn ranges_of_single_atom_rows_and_their_meets_are_exact() {
    let holds = |r: &IntRange, x: i64| {
        r.0.as_ref().is_none_or(|l| *l <= Int::from(x))
            && r.1.as_ref().is_none_or(|h| Int::from(x) <= *h)
    };
    let mut seen: Vec<(IntRange, Vec<i64>)> = Vec::new();
    for a in (-7i64..=7).filter(|a| *a != 0) {
        for k in -30i64..=30 {
            for eq in [false, true] {
                let (r, bad) = row_range(&Int::from(a), &Int::from(k), eq);
                let want: Vec<i64> = (-40..=40)
                    .filter(|x| if eq { a * x + k == 0 } else { a * x + k >= 0 })
                    .collect();
                assert_eq!(bad, eq && k % a != 0, "a = {a}, k = {k}");
                if !bad {
                    let got: Vec<i64> = (-40..=40).filter(|x| holds(&r, *x)).collect();
                    assert_eq!(got, want, "a = {a}, k = {k}, eq = {eq}");
                    if seen.len() < 60 && (a + k).rem_euclid(7) == 0 {
                        seen.push((r, want));
                    }
                }
            }
        }
    }
    for (r, rs) in &seen {
        for (s, ss) in &seen {
            let both: Vec<i64> = rs.iter().filter(|x| ss.contains(x)).copied().collect();
            let m = range_meet(r, s);
            let mut cur = r.clone();
            let empty = meet_range(&mut cur, s.clone());
            assert_eq!(cur, m);
            assert_eq!(empty, range_is_empty(&m));
            let got: Vec<i64> = (-40..=40).filter(|x| holds(&m, *x)).collect();
            assert_eq!(got, both, "{r:?} meet {s:?}");
            assert!(!empty || both.is_empty(), "{r:?} meet {s:?}");
        }
    }
}

/// `ceil_log2` and `pow2` at the ends: `pow2(ceil_log2(x))` is the least power of two at
/// least `x`, for `x` at and around each power, in a machine word and past it.
#[test]
fn ceiling_log2_and_powers_of_two_meet_at_every_power() {
    assert_eq!(Int::from(-5).ceil_log2(), 0);
    assert_eq!(Int::ZERO.ceil_log2(), 0);
    assert_eq!(Int::ONE.ceil_log2(), 0);
    for k in [1u32, 2, 62, 63, 64, 125, 126, 127, 128, 200] {
        let p = pow2(k);
        assert_eq!(Int::pow2(u64::from(k)), p, "2^{k}");
        assert_eq!(p.ceil_log2(), u64::from(k), "ceil log2 2^{k}");
        assert_eq!(
            (&p - &Int::ONE).ceil_log2(),
            u64::from(k) - u64::from(k == 1),
            "2^{k} - 1"
        );
        assert_eq!((&p + &Int::ONE).ceil_log2(), u64::from(k) + 1, "2^{k} + 1");
    }
    assert_eq!(Int::pow2(0), Int::ONE);
}

#[test]
fn bitwise_and_of_zero_and_of_minus_one_with_wide_values() {
    let w = &pow2(200) + &Int::from(9);
    let cases: Vec<(&str, Int, Int, Int)> = vec![
        ("0 & wide", Int::ZERO, w.clone(), Int::ZERO),
        ("wide & 0", w.clone(), Int::ZERO, Int::ZERO),
        ("wide & itself", w.clone(), w.clone(), w.clone()),
        ("wide & -wide", w.clone(), -&w, Int::ONE),
        ("-1 & -wide", Int::from(-1), -&w, -&w),
        // Back in i128: the and of a wide value and a small mask is small.
        ("wide & 15", w.clone(), Int::from(15), Int::from(9)),
    ];
    for (case, a, b, want) in cases {
        assert_eq!(&a & &b, want, "{case}");
    }
}

#[test]
fn decimal_text_of_wide_values_of_both_signs() {
    for b in ends() {
        assert_eq!(Int::from(b.clone()).to_string(), b.to_string(), "{b}");
    }
}

/// The primes of the cheap root check are what their comment says: prime, and the largest
/// below `2^64`, `2^63` and `2^62`.
#[test]
fn the_root_check_primes_are_the_largest_below_their_powers_of_two() {
    for (q, k) in ROOT_CHECK_PRIMES.into_iter().zip([64u32, 63, 62]) {
        assert!(is_prime(q), "{q}");
        // `2^(k-1) <= q < 2^k`, and the next prime is at least `2^k` (none below `2^64`).
        assert_eq!(q.ilog2(), k - 1, "{q}");
        let next = next_prime(q);
        assert!(next.is_none_or(|n| n.ilog2() >= k), "{q}: next {next:?}");
    }
}

#[test]
fn word_arithmetic_helpers_on_their_ends() {
    // pow_mod_2_64, pow_mod and inverse_mod_2_64 are tested in zed-numtheory.
    // pow_mod_pow2 against num-bigint, exponents 0, 1 and many, moduli of one bit and past a
    // word.
    let x = BigUint::from(3u32).pow(50u32) + 1u32;
    for (e, k) in [
        (0u64, 1u32),
        (1, 1),
        (1, 200),
        (5, 64),
        (17, 65),
        (100, 300),
    ] {
        let unit = BigUint::from(1u32) << k;
        let mask = &unit - 1u32;
        assert_eq!(
            pow_mod_pow2(&x, e, &mask),
            x.modpow(&BigUint::from(e), &unit),
            "x ^ {e} mod 2^{k}"
        );
    }
}

#[test]
fn expand_pow_writes_out_each_power() {
    for (b, e) in [
        (1u32, 0u32),
        (7, 0),
        (0, 3),
        (1, 50),
        (2, 1),
        (3, 64),
        (10, 33),
        (12_345, 17),
    ] {
        assert_eq!(
            expand_pow(&BigUint::from(b), &BigUint::from(e)),
            BigUint::from(b).pow(e),
            "{b} ^ {e}"
        );
    }
}

#[test]
fn least_roots_of_the_smallest_bases_and_of_mixed_powers() {
    // 2 and 3 are below the loop's bit bound; 4, 8, 9 the least squares and cubes; 2^a 3^b
    // with a gcd of exponents; an odd power of an even base; a 6th power reached by a square
    // root and then a cube root; a 15th power reached by a cube then a 5th root.
    let cases: [(u64, u64, u64); 12] = [
        (2, 2, 1),
        (3, 3, 1),
        (4, 2, 2),
        (8, 2, 3),
        (9, 3, 2),
        (12, 12, 1),
        (36, 6, 2),
        (72, 72, 1),
        (6u64.pow(6), 6, 6),
        (10u64.pow(9), 10, 9),
        (2u64.pow(15), 2, 15),
        (5u64.pow(15), 5, 15),
    ];
    for (b, r, m) in cases {
        assert_eq!(
            least_root(BigUint::from(b)),
            (BigUint::from(r), BigUint::from(m)),
            "{b}"
        );
    }
}

#[test]
fn a_root_by_odd_part_rejects_each_way_a_candidate_fails() {
    // (case, base, index, root)
    let wide = BigUint::from(3u32).pow(100u32) + 2u32; // odd, no power
    let cases: Vec<(&str, BigUint, u64, Option<BigUint>)> = vec![
        // The power of 2 is not a multiple of the index.
        ("2^4 * 27, index 3", BigUint::from(16u32 * 27), 3, None),
        // The odd part is 1: the root is a power of 2.
        (
            "2^9, index 3",
            BigUint::from(512u32),
            3,
            Some(BigUint::from(8u32)),
        ),
        // A one-word root, found and checked.
        (
            "2^3 * 7^3, index 3",
            BigUint::from(8u32 * 343),
            3,
            Some(BigUint::from(14u32)),
        ),
        // A one-word candidate of the wrong bit count, and one off by the test primes.
        ("7^3 + 2, index 3", BigUint::from(345u32), 3, None),
        (
            "3^40 + 2, index 5",
            BigUint::from(3u32).pow(40u32) + 2u32,
            5,
            None,
        ),
        // A wide root, found; a wide odd part that is no power, refused.
        (
            "(3^100 + 2)^3, index 3",
            wide.pow(3u32),
            3,
            Some(wide.clone()),
        ),
        ("(3^100 + 2)^3 + 2, index 3", wide.pow(3u32) + 2u32, 3, None),
        ("3^100 + 2, index 3", wide.clone(), 3, None),
    ];
    for (case, b, p, want) in cases {
        assert_eq!(OddPart::of(&b).root(p), want, "{case}");
    }
}

#[test]
fn the_residue_filter_passes_powers_and_ignores_indices_it_holds_no_prime_for() {
    // 3^(3·5·7·11·13) is a power for each of those indices, and passes each of them, wide
    // ones included; an index past the filter's wide primes passes on the small primes alone.
    let o = BigUint::from(3u32).pow(3 * 5 * 7 * 11 * 13);
    let odd = OddPart::of(&o);
    for p in [3u64, 5, 7, 11, 13] {
        assert!(odd.passes(p), "index {p}");
    }
    // 521 is past the wide indices (those below 23,798 / 64 bits) and has no prime 1 modulo it
    // below 1024, so no residue applies: it passes, though 521 does not divide 15,015. The
    // filter is a necessary condition only; the root decides.
    let top = odd
        .filter()
        .wide
        .last()
        .map(|&(p, _, _)| p)
        .expect("wide indices");
    assert!(top < 521, "the widest index {top}");
    assert!(odd.passes(521), "index 521, no residue applies");
    assert_eq!(odd.root(521), None, "3^15015 is no 521st power");
    // A number that is no cube fails a small prime 1 modulo 3: 3 is not a cube modulo 7.
    assert!(!OddPart::of(&BigUint::from(3u32)).passes(3), "3, index 3");
    // A number with a factor of each small filter prime passes every index: every residue is 0.
    let mut all = BigUint::from(1u32);
    for &(q, _) in &OddPart::of(&BigUint::from(3u32)).filter().small {
        all *= q;
    }
    let all = OddPart::of(&all);
    for p in [3u64, 5, 7, 11, 13, 101] {
        assert!(all.passes(p), "every residue 0, index {p}");
    }
}

#[test]
fn a_remainder_tree_of_one_modulus_and_of_moduli_past_the_value() {
    let x = BigUint::from(10u32).pow(30u32) + 7u32;
    for ms in [
        vec![],
        vec![2u64],
        vec![u64::MAX],
        vec![1, 1, 1],
        vec![3, 5],
        vec![3, 5, 7],
    ] {
        let want: Vec<u64> = ms
            .iter()
            .map(|&m| u64::try_from(&x % m).expect("below m"))
            .collect();
        assert_eq!(remainders(&x, &ms), want, "{ms:?}");
    }
    // Zero has remainder 0 everywhere.
    assert_eq!(remainders(&BigUint::ZERO, &[3, 5, 7, 11]), [0, 0, 0, 0]);
}

#[test]
fn stripping_a_power_of_2_by_a_power_of_2() {
    // (rest, c, multiplicity, left): fewer zeros than c has, zeros not a multiple of c's.
    for (rest, c, k, left) in [
        (3u64, 2u64, 0u64, 3u64),
        (8, 16, 0, 8),
        (32, 4, 2, 2),
        (48, 4, 2, 3),
        (1, 8, 0, 1),
    ] {
        let mut r = BigUint::from(rest);
        assert_eq!(strip(&mut r, &BigUint::from(c)), k, "{rest} by {c}");
        assert_eq!(r, BigUint::from(left), "{rest} by {c}: left");
    }
    // An odd c that does not divide: 0, rest unchanged; rest equal to c: 1, rest 1.
    let mut r = BigUint::from(10u32);
    assert_eq!(strip(&mut r, &BigUint::from(3u32)), 0);
    assert_eq!(r, BigUint::from(10u32));
    let mut r = BigUint::from(9u32);
    assert_eq!(strip(&mut r, &BigUint::from(9u32)), 1);
    assert!(r.is_one());
}

/// Whether the base is pairwise coprime, every element at least 2, and every `x` a product
/// of powers of its elements.
fn is_coprime_base_of(base: &[BigUint], xs: &[BigUint]) -> bool {
    let coprime = base
        .iter()
        .enumerate()
        .all(|(i, a)| a > &BigUint::one() && base[i + 1..].iter().all(|b| gcd_uint(a, b).is_one()));
    let spanned = xs.iter().all(|x| {
        let mut rest = x.clone();
        for c in base {
            strip(&mut rest, c);
        }
        rest.is_one()
    });
    coprime && spanned
}

#[test]
fn a_coprime_base_of_each_shape_of_input() {
    let n = |v: &[u64]| v.iter().map(|&x| BigUint::from(x)).collect::<Vec<_>>();
    // (case, inputs, the base as a sorted set)
    let cases: Vec<(&str, Vec<BigUint>, Vec<u64>)> = vec![
        ("empty", vec![], vec![]),
        ("ones only", n(&[1, 1]), vec![]),
        ("one prime", n(&[5]), vec![5]),
        ("a composite alone", n(&[6]), vec![6]),
        ("4 and 8", n(&[4, 8]), vec![2]),
        ("6, 2 and 3", n(&[6, 2, 3]), vec![2, 3]),
        ("coprime already", n(&[4, 9, 25]), vec![4, 9, 25]),
        ("equal inputs", n(&[12, 12]), vec![12]),
        ("12 and 18", n(&[12, 18]), vec![2, 3]),
        ("2^20 * 3 and 2", n(&[(1 << 20) * 3, 2]), vec![2, 3]),
        ("10, 15 and 6", n(&[10, 15, 6]), vec![2, 3, 5]),
        ("30 and 1", n(&[30, 1]), vec![30]),
    ];
    for (case, xs, want) in cases {
        let mut base = coprime_base(xs.iter());
        assert!(is_coprime_base_of(&base, &xs), "{case}: {base:?}");
        base.sort();
        assert_eq!(base, n(&want), "{case}");
    }
    // Wide inputs sharing a wide factor.
    let p = BigUint::from(10u32).pow(30u32) + 57u32;
    let xs = vec![&p * 6u32, &p * &p * 35u32, BigUint::from(14u32)];
    let base = coprime_base(xs.iter());
    assert!(is_coprime_base_of(&base, &xs), "wide: {base:?}");
}

#[test]
fn exponents_over_a_coprime_base_rebuild_each_product() {
    let n = |x: u64| BigUint::from(x);
    // (case, powers b ^ e)
    let cases: Vec<(&str, Vec<(BigUint, BigUint)>)> = vec![
        ("no powers", vec![]),
        ("one power", vec![(n(12), n(3))]),
        (
            "shared factors",
            vec![(n(4), n(5)), (n(6), n(2)), (n(9), n(1))],
        ),
        ("exponent 0", vec![(n(10), n(0)), (n(15), n(4))]),
        (
            "wide exponent",
            vec![(n(18), BigUint::from(1u32) << 100u32), (n(12), n(7))],
        ),
    ];
    for (case, powers) in cases {
        let base = coprime_base(powers.iter().map(|(b, _)| b));
        let exps = exponents_over(&base, powers.iter().map(|(b, e)| (b, e)));
        assert_eq!(exps.len(), base.len(), "{case}");
        // Each base element's exponent is the sum over the powers of its multiplicity in b
        // times e.
        for (c, x) in base.iter().zip(&exps) {
            let want: BigUint = powers
                .iter()
                .map(|(b, e)| {
                    let mut rest = b.clone();
                    e * strip(&mut rest, c)
                })
                .sum();
            assert_eq!(x, &want, "{case}: exponent of {c}");
        }
    }
    // Two products equal as values have equal exponents over a common base: 4^3 · 9 = 8^2 · 3^2.
    let l = [(n(4), n(3)), (n(9), n(1))];
    let r = [(n(8), n(2)), (n(3), n(2))];
    let base = coprime_base(l.iter().chain(&r).map(|(b, _)| b));
    assert_eq!(
        exponents_over(&base, l.iter().map(|(b, e)| (b, e))),
        exponents_over(&base, r.iter().map(|(b, e)| (b, e)))
    );
}
