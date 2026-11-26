//! Tests of the affine forms: each caller's use, and random draws against the simplest
//! correct form of each routine, written out here as the oracle.

use std::collections::BTreeMap;

use zedc_int::int::{Int, Num};

use super::*;

fn int(v: i64) -> Int {
    Int::from(v)
}

fn terms(pairs: &[(u8, i64)]) -> BTreeMap<u8, Int> {
    pairs.iter().map(|&(x, c)| (x, int(c))).collect()
}

#[test]
fn a_sum_of_zero_removes_the_entry_and_a_new_key_is_made() {
    let mut t = terms(&[(1, 2), (3, -1)]);
    add_term(&mut t, &1, &int(-2));
    assert_eq!(t, terms(&[(3, -1)]));
    add_term(&mut t, &2, &int(5));
    assert_eq!(t, terms(&[(2, 5), (3, -1)]));
    add_term(&mut t, &4, &int(0));
    assert_eq!(
        t,
        terms(&[(2, 5), (3, -1)]),
        "a zero coefficient makes no entry"
    );
}

#[test]
fn scaling_by_zero_is_empty_and_add_scaled_cancels() {
    let t = terms(&[(1, 3), (2, -4)]);
    assert!(scaled(&t, &int(0)).is_empty());
    assert_eq!(scaled(&t, &int(-2)), terms(&[(1, -6), (2, 8)]));
    let mut u = scaled(&t, &int(2));
    add_scaled(&mut u, &t, &int(-2));
    assert!(u.is_empty(), "u - 2t of u = 2t keeps no zero entry");
}

#[test]
fn content_is_zero_for_no_terms_and_never_negative() {
    assert_eq!(content::<Int>([]), int(0));
    assert_eq!(content(&[int(-6), int(9)]), int(3));
    assert_eq!(content(&[int(-4)]), int(4));
    assert_eq!(content(&[int(5), int(1), int(10)]), int(1));
}

#[test]
fn row_divisor_cases() {
    let t = terms(&[(1, 4), (2, -6)]);
    assert_eq!(row_divisor(t.values(), &int(3), false), Divisor::By(int(2)));
    assert_eq!(row_divisor(t.values(), &int(3), true), Divisor::Infeasible);
    assert_eq!(row_divisor(t.values(), &int(-4), true), Divisor::By(int(2)));
    assert_eq!(
        row_divisor(terms(&[(1, 3), (2, 1)]).values(), &int(7), true),
        Divisor::Keep
    );
    assert_eq!(
        row_divisor::<Int>([], &int(-1), true),
        Divisor::Keep,
        "no term"
    );
    // `2x - 1 >= 0` is `x - 1 >= 0`: the constant rounds down.
    let (mut t, mut k) = (terms(&[(1, 2)]), int(-1));
    divide_row(&mut t, &mut k, &int(2));
    assert_eq!((t, k), (terms(&[(1, 1)]), int(-1)));
}

#[test]
fn primitive_forms_of_multiples_agree() {
    let a = primitive_form(&terms(&[(1, 2), (2, -4)])).expect("terms");
    let b = primitive_form(&terms(&[(1, -3), (2, 6)])).expect("terms");
    assert_eq!(a.form, b.form);
    assert_eq!(a.form, vec![(1, int(1)), (2, int(-2))]);
    assert_eq!((a.flipped, a.g), (false, int(2)));
    assert_eq!((b.flipped, b.g), (true, int(3)));
    assert!(primitive_form::<u8, Int>(&BTreeMap::new()).is_none());
}

#[test]
fn num_coefficients_merge_as_ints_do() {
    let mut t: BTreeMap<u8, Num> = BTreeMap::from([(1, Num::from(3)), (2, Num::from(-3))]);
    add_term(&mut t, &2, &Num::from(3));
    assert_eq!(t, BTreeMap::from([(1, Num::from(3))]));
    assert!(Coef::is_negative(&Num::from(-1)) && !Coef::is_negative(&Num::ZERO));
    assert!(Coef::is_unit(&Num::from(-1)) && !Coef::is_unit(&Num::from(2)));
    assert_eq!(
        scaled(&t, &Num::from(-2)),
        BTreeMap::from([(1, Num::from(-6))])
    );
}

/// The merge against a map of `i64` sums with the zeros filtered out at the end, on random
/// updates over few keys, so that sums of zero and keys made again are frequent.
#[test]
fn the_merge_agrees_with_sums_filtered_at_the_end() {
    let (mut rng, _) = crate::seed::Rng::fresh("the_merge_agrees_with_sums_filtered_at_the_end");
    for _ in 0..200 {
        let mut t: BTreeMap<u8, Int> = BTreeMap::new();
        let mut oracle: BTreeMap<u8, i64> = BTreeMap::new();
        for _ in 0..rng.below(40) {
            let x = rng.below(5) as u8;
            let c = rng.int(-3, 3);
            if rng.below(2) == 0 {
                add_term(&mut t, &x, &int(c));
                *oracle.entry(x).or_insert(0) += c;
            } else {
                let f = rng.int(-2, 2);
                let other = terms(&[(x, c), ((x + 1) % 5, -c)]);
                add_scaled(&mut t, &other, &int(f));
                *oracle.entry(x).or_insert(0) += f * c;
                *oracle.entry((x + 1) % 5).or_insert(0) -= f * c;
            }
            let want: BTreeMap<u8, Int> = (oracle.iter())
                .filter(|(_, c)| **c != 0)
                .map(|(x, c)| (*x, int(*c)))
                .collect();
            assert_eq!(t, want);
        }
    }
}

/// Dividing a random row of two variables keeps its integer points in the box `[-6, 6]²`, and an
/// equation called infeasible has none there; the oracle is the row evaluated at each point.
/// It cannot catch a fault seen only at points outside the box.
#[test]
fn row_division_keeps_the_integer_points() {
    let (mut rng, _) = crate::seed::Rng::fresh("row_division_keeps_the_integer_points");
    let holds = |a: i64, b: i64, k: i64, eq: bool, x: i64, y: i64| {
        let v = a * x + b * y + k;
        if eq { v == 0 } else { v >= 0 }
    };
    for _ in 0..300 {
        let g = rng.int(1, 4);
        let (a, b, k) = (g * rng.int(-3, 3), g * rng.int(-3, 3), rng.int(-20, 20));
        let eq = rng.below(2) == 0;
        let mut t = terms(&[(0, a), (1, b)]);
        t.retain(|_, c| !c.is_zero());
        let mut kk = int(k);
        let (a2, b2, k2) = match row_divisor(t.values(), &kk, eq) {
            Divisor::Keep => (a, b, k),
            Divisor::Infeasible => {
                for (x, y) in (-6..=6).flat_map(|x| (-6..=6).map(move |y| (x, y))) {
                    assert!(
                        !holds(a, b, k, eq, x, y),
                        "{a}x + {b}y + {k} == 0 at {x},{y}"
                    );
                }
                continue;
            }
            Divisor::By(g) => {
                divide_row(&mut t, &mut kk, &g);
                let small = |c: &Int| i64::try_from(c.to_i128().expect("small")).expect("small");
                let get = |x: u8| t.get(&x).map_or(0, small);
                (get(0), get(1), small(&kk))
            }
        };
        for (x, y) in (-6..=6).flat_map(|x| (-6..=6).map(move |y| (x, y))) {
            assert_eq!(
                holds(a, b, k, eq, x, y),
                holds(a2, b2, k2, eq, x, y),
                "at {x},{y}"
            );
        }
    }
}

/// The primitive form of a random list of terms, times its sign and gcd, gives the terms back,
/// and is the same for every nonzero multiple of them.
#[test]
fn a_primitive_form_gives_its_terms_back() {
    let (mut rng, _) = crate::seed::Rng::fresh("a_primitive_form_gives_its_terms_back");
    for _ in 0..300 {
        let mut t: BTreeMap<u8, Int> = BTreeMap::new();
        for x in 0..rng.below(5) as u8 {
            add_term(&mut t, &x, &int(rng.int(-9, 9)));
        }
        let Some(p) = primitive_form(&t) else {
            assert!(t.is_empty());
            continue;
        };
        assert!(!p.g.is_zero() && !p.g.is_negative());
        assert!(!p.form[0].1.is_negative());
        let s = if p.flipped { int(-1) } else { int(1) };
        let back: BTreeMap<u8, Int> = (p.form.iter())
            .map(|(x, c)| (*x, &(c * &p.g) * &s))
            .collect();
        assert_eq!(back, t);
        let m = int(rng.pick(&[-3, -1, 2, 5]));
        assert_eq!(primitive_form(&scaled(&t, &m)).expect("terms").form, p.form);
    }
}

mod shadow {
    use crate::shadow::*;
    use zedc_int::int::Int;

    fn int(v: i64) -> Int {
        Int::from(v)
    }

    /// The uses of the two-pin reading and the row-sums plane: a row with no `x` that holds or
    /// does not, a lower and an upper end met with what is there, and a value past `i128`,
    /// which leaves the ends as they were (the box reading of zedc-preimage's loops relies on
    /// that).
    #[test]
    fn meet_puts_each_end_and_leaves_them_past_i128() {
        let (mut lo, mut hi) = (None, None);
        assert_eq!(i128_meet(0, -1, &mut lo, &mut hi), Some(false));
        assert_eq!(i128_meet(0, 0, &mut lo, &mut hi), Some(true));
        assert_eq!((lo, hi), (None, None));
        // `2x - 3 >= 0`: x >= 2; `-3x + 7 >= 0`: x <= 2; `x + 5 >= 0` changes nothing.
        assert_eq!(i128_meet(2, -3, &mut lo, &mut hi), Some(true));
        assert_eq!(i128_meet(-3, 7, &mut lo, &mut hi), Some(true));
        assert_eq!(i128_meet(1, 5, &mut lo, &mut hi), Some(true));
        assert_eq!((lo, hi), (Some(2), Some(2)));
        assert_eq!(i128_meet(1, i128::MIN, &mut lo, &mut hi), None);
        assert_eq!(i128_meet(i128::MIN, 0, &mut lo, &mut hi), None);
        assert_eq!((lo, hi), (Some(2), Some(2)), "None leaves the ends");
        assert_eq!(i128_row_bound(0, 4), None);
        assert_eq!(i128_row_bound(-2, -3), Some(-2), "-2x - 3 >= 0: x <= -1.5");
    }

    /// The end [`i128_row_bound`] gives is the least (or greatest) integer where the row holds,
    /// against the row evaluated at each integer of `[-40, 40]`.
    #[test]
    fn the_row_bound_is_the_last_point_of_the_row() {
        let (mut rng, _) = crate::seed::Rng::fresh("the_row_bound_is_the_last_point_of_the_row");
        for _ in 0..500 {
            let p = rng.int(-6, 6);
            let q = rng.int(-30, 30);
            let Some(end) = i128_row_bound(i128::from(p), i128::from(q)) else {
                assert_eq!(p, 0);
                continue;
            };
            let end = i64::try_from(end).expect("small");
            let holds: Vec<i64> = (-40..=40).filter(|x| p * x + q >= 0).collect();
            let want = if p > 0 { holds.first() } else { holds.last() };
            assert_eq!(Some(&end), want, "{p}x + {q} >= 0");
        }
    }

    /// The pair the shadows of the two-pin reading and the row-sums plane are made of, on random
    /// bounds `xl·x + yl·y + cl >= 0` (`yl > 0`) and `xu·x + yu·y + cu >= 0` (`yu < 0`), at each
    /// integer `x` of `[-12, 12]`: the real shadow holds exactly where some rational `y` holds
    /// both, that is where `-(xl·x + cl) / yl <= (xu·x + cu) / -yu`, compared by
    /// cross-multiplying; the dark shadow holds only where an integer `y` does (when one does,
    /// the least, `⌈-(xl·x + cl) / yl⌉`, has size at most 102, so the search over `[-200, 200]`
    /// finds it); and with a unit coefficient of `y` the two are the same row.
    #[test]
    fn the_shadows_of_a_pair_have_the_points_they_claim() {
        let (mut rng, _) =
            crate::seed::Rng::fresh("the_shadows_of_a_pair_have_the_points_they_claim");
        for _ in 0..400 {
            let (xl, yl, cl) = (rng.int(-6, 6), rng.int(1, 5), rng.int(-30, 30));
            let (xu, yu, cu) = (rng.int(-6, 6), rng.int(-5, -1), rng.int(-30, 30));
            let wide = |v: i64| i128::from(v);
            let l = (wide(xl), wide(yl), wide(cl));
            let u = (wide(xu), wide(yu), wide(cu));
            let (pr, qr) = i128_pair(l, u, false).expect("small");
            let (pd, qd) = i128_pair(l, u, true).expect("small");
            if yl == 1 || yu == -1 {
                assert_eq!((pr, qr), (pd, qd), "a unit makes the shadows one");
            }
            for x in -12..=12i64 {
                let (real, dark) = (pr * wide(x) + qr >= 0, pd * wide(x) + qd >= 0);
                // A rational `y` with `yl·y >= -(xl·x + cl)` and `-yu·y <= xu·x + cu`.
                let rational = (-yu) * -(xl * x + cl) <= yl * (xu * x + cu);
                assert_eq!(real, rational, "real shadow at x = {x}");
                let integer =
                    (-200..=200).any(|y| xl * x + yl * y + cl >= 0 && xu * x + yu * y + cu >= 0);
                assert!(
                    !dark || integer,
                    "dark shadow at x = {x} without an integer y"
                );
            }
        }
    }

    /// The use of `lossless_pair` and `dark_is_real`: a gap of 0 is exact at once, a row with no
    /// terms by its constant alone, and a unit gcd with a gap of 1 or more is not exact.
    #[test]
    fn dark_exact_cases() {
        assert!(dark_exact(&int(-5), &int(0), &[int(1)]));
        assert!(dark_exact(&int(-1), &int(3), []), "no terms: k < 0");
        assert!(dark_exact(&int(3), &int(3), []), "no terms: k >= d");
        assert!(!dark_exact(&int(2), &int(3), []));
        assert!(!dark_exact(&int(9), &int(1), &[int(4), int(1)]));
        // `4t + 7` against `4t + 4`: 7 mod 4 = 3 >= 3.
        assert!(dark_exact(&int(7), &int(3), &[int(8), int(-4)]));
        assert!(!dark_exact(&int(6), &int(3), &[int(8), int(-4)]));
        assert_eq!(dark_gap(&int(1), &int(9)), int(0));
        assert_eq!(dark_gap(&int(3), &int(4)), int(6));
    }

    /// [`dark_exact`] against the rows themselves: the real row `Σ c·x + k >= 0` and the dark row
    /// with constant `k - d` hold at the same integer points of the box `[-60, 60]²`, on random
    /// rows of at most two terms (`|c| <= 6`, `|k| <= 20`, `d <= 25`). The rows differ only where
    /// the terms sum to a `v` in `[-k, d - k)`, so `|v| <= 45`, and every multiple `v` of the gcd
    /// `g` that small is reached in the box: with one term `c`, at `x = v/c`; with two and a
    /// coefficient of size 1, by that variable alone; otherwise `|c2| >= 2`, `x` is taken in its
    /// class mod `c2/g` with `|x| <= 6`, so `|c1·x| <= 36` and `|y| <= (45 + 36)/2 < 60`.
    #[test]
    fn dark_exact_agrees_with_the_points_of_both_rows() {
        let (mut rng, _) =
            crate::seed::Rng::fresh("dark_exact_agrees_with_the_points_of_both_rows");
        for _ in 0..300 {
            let n = rng.below(3);
            let c: Vec<i64> = (0..n)
                .map(|_| rng.pick(&[-6, -4, -3, -2, 2, 3, 4, 6, 1, -1]))
                .collect();
            let (k, d) = (
                rng.int(-20, 20),
                rng.pick(&[0, 1, 2, 3, 4, 6, 9, 12, 20, 25]),
            );
            let coeffs: Vec<Int> = c.iter().map(|&v| int(v)).collect();
            let got = dark_exact(&int(k), &int(d), &coeffs);
            let value = |x: i64, y: i64| match c[..] {
                [] => 0,
                [a] => a * x,
                [a, b] => a * x + b * y,
                _ => unreachable!(),
            };
            let same = (-60..=60i64)
                .flat_map(|x| (-60..=60i64).map(move |y| (x, y)))
                .all(|(x, y)| (value(x, y) + k >= 0) == (value(x, y) + k - d >= 0));
            assert_eq!(got, same, "coefficients {c:?}, k {k}, d {d}");
        }
    }
}
