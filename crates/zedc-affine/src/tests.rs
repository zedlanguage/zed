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

mod plane {
    use std::cmp::Ordering;

    use crate::plane::*;
    use zedc_int::int::Int;

    /// The angle of `v` in `[0, 2π)` from the first axis, by `atan2`, and the direction of `v`
    /// divided by the gcd of its coordinates: two directions of small coordinates have one angle
    /// exactly when their primitive directions are equal, and two that differ are at least
    /// about `1 / (2·20²)` apart, far above the error of `atan2`.
    fn angle(v: (i64, i64)) -> f64 {
        let a = (v.1 as f64).atan2(v.0 as f64);
        if a < 0.0 {
            a + std::f64::consts::TAU
        } else {
            a
        }
    }

    fn primitive(v: (i64, i64)) -> (i64, i64) {
        let g = zed_numtheory::gcd_u128(v.0.unsigned_abs().into(), v.1.unsigned_abs().into());
        let g = i64::try_from(g).expect("small");
        (v.0 / g, v.1 / g)
    }

    /// The order of `atan2`, equal on equal primitive directions.
    fn by_atan2(u: (i64, i64), v: (i64, i64)) -> Ordering {
        if primitive(u) == primitive(v) {
            return Ordering::Equal;
        }
        angle(u).total_cmp(&angle(v))
    }

    fn nonzero(rng: &mut crate::seed::Rng, r: i64) -> (i64, i64) {
        loop {
            let v = (rng.int(-r, r), rng.int(-r, r));
            if v != (0, 0) {
                return v;
            }
        }
    }

    fn i(v: i64) -> i128 {
        i128::from(v)
    }

    /// [`angle_cmp`] and [`angle_cmp_from`] against the order of `atan2`, on `i128` and on
    /// [`Int`] alike, with [`cross`] and [`dot`] against their sums.
    #[test]
    fn the_angle_order_is_the_order_of_atan2() {
        let (mut rng, seed) = crate::seed::Rng::fresh("the_angle_order_is_the_order_of_atan2");
        // Seed 16148036221008483195: `atan2` put `(-18, 1)` just under a half-turn from
        // `(18, -1)`; the opposite direction is out of the first half.
        assert_eq!(first_half((&18i128, &-1), (&-18, &1)), Some(false));
        for _ in 0..3000 {
            let (u, v, base) = (
                nonzero(&mut rng, 20),
                nonzero(&mut rng, 20),
                nonzero(&mut rng, 20),
            );
            let (iu, iv) = ((i(u.0), i(u.1)), (i(v.0), i(v.1)));
            let ib = (i(base.0), i(base.1));
            assert_eq!(
                cross((&iu.0, &iu.1), (&iv.0, &iv.1)),
                Some(i(u.0 * v.1 - u.1 * v.0))
            );
            assert_eq!(
                dot((&iu.0, &iu.1), (&iv.0, &iv.1)),
                Some(i(u.0 * v.0 + u.1 * v.1))
            );
            let want = by_atan2(u, v);
            let got = angle_cmp((&iu.0, &iu.1), (&iv.0, &iv.1));
            assert_eq!(got, Some(want), "seed {seed}: {u:?} {v:?}");
            let (bu, bv) = (Int::from(u.0), Int::from(u.1));
            let (cu, cv) = (Int::from(v.0), Int::from(v.1));
            assert_eq!(angle_cmp((&bu, &bv), (&cu, &cv)), Some(want));
            // From `base`: the angles less the angle of `base`, in `[0, 2π)`.
            let from = |w: (i64, i64)| {
                let a = angle(w) - angle(base);
                if a < 0.0 {
                    a + std::f64::consts::TAU
                } else {
                    a
                }
            };
            let want = if primitive(u) == primitive(v) {
                Ordering::Equal
            } else if primitive(u) == primitive(base) {
                Ordering::Less
            } else if primitive(v) == primitive(base) {
                Ordering::Greater
            } else {
                from(u).total_cmp(&from(v))
            };
            let got = angle_cmp_from((&ib.0, &ib.1), (&iu.0, &iu.1), (&iv.0, &iv.1));
            assert_eq!(got, Some(want), "seed {seed}: base {base:?}, {u:?} {v:?}");
            let half = first_half((&ib.0, &ib.1), (&iu.0, &iu.1));
            // Exactly opposite `base` is out, though `from` may round it below π.
            let opposite = primitive(u) == (-primitive(base).0, -primitive(base).1);
            let in_first =
                primitive(u) == primitive(base) || (!opposite && from(u) < std::f64::consts::PI);
            assert_eq!(half, Some(in_first), "seed {seed}: base {base:?}, {u:?}");
        }
    }

    /// Past `i128` the products answer `None`, and the angle order still orders two directions
    /// in two halves, which needs no product.
    #[test]
    fn the_products_answer_none_past_i128() {
        let big = (i128::MAX, 2);
        assert_eq!(cross((&big.0, &big.1), (&1, &3)), None);
        assert_eq!(dot((&big.0, &big.1), (&2, &0)), None);
        assert_eq!(
            angle_cmp((&big.0, &big.1), (&i128::MAX, &-2)),
            Some(Ordering::Less)
        );
        assert_eq!(angle_cmp((&big.0, &big.1), (&i128::MAX, &3)), None);
        assert!(Basis::new(4i128, 6).is_none());
    }

    /// [`cramer`]'s point lies on both lines, and is `None` exactly on parallel lines.
    #[test]
    fn cramer_gives_the_point_on_both_lines() {
        let (mut rng, seed) = crate::seed::Rng::fresh("cramer_gives_the_point_on_both_lines");
        for _ in 0..3000 {
            let f = (i(rng.int(-9, 9)), i(rng.int(-9, 9)), i(rng.int(-30, 30)));
            let g = (i(rng.int(-9, 9)), i(rng.int(-9, 9)), i(rng.int(-30, 30)));
            let got = cramer((&f.0, &f.1, &f.2), (&g.0, &g.1, &g.2));
            let parallel = f.0 * g.1 == f.1 * g.0;
            let Some((x, y, d)) = got else {
                assert!(parallel, "seed {seed}: {f:?} {g:?}");
                continue;
            };
            assert!(!parallel && d > 0, "seed {seed}: {f:?} {g:?}");
            assert_eq!(f.0 * x + f.1 * y, f.2 * d, "seed {seed}: {f:?} {g:?}");
            assert_eq!(g.0 * x + g.1 * y, g.2 * d, "seed {seed}: {f:?} {g:?}");
            let on_int = |v: i128| Int::from(i64::try_from(v).expect("small"));
            let (fi, gi) = (
                (on_int(f.0), on_int(f.1), on_int(f.2)),
                (on_int(g.0), on_int(g.1), on_int(g.2)),
            );
            let want = (on_int(x), on_int(y), on_int(d));
            assert_eq!(
                cramer((&fi.0, &fi.1, &fi.2), (&gi.0, &gi.1, &gi.2)),
                Some(want)
            );
        }
    }

    /// The basis of a primitive direction: `s·a + t·b == 1`; [`Basis::row`] writes `A·x + B·y`
    /// in `u` and `w` with the same value at every point, and [`Basis::back`] undoes it; a
    /// direction that is not primitive has none.
    #[test]
    fn the_basis_keeps_the_value_of_each_row() {
        let (mut rng, seed) = crate::seed::Rng::fresh("the_basis_keeps_the_value_of_each_row");
        for _ in 0..3000 {
            let (a, b) = nonzero(&mut rng, 40);
            let (ia, ib) = (i(a), i(b));
            let Some(basis) = Basis::new(ia, ib) else {
                assert_ne!(primitive((a, b)), (a, b), "seed {seed}: ({a}, {b})");
                continue;
            };
            assert_eq!(primitive((a, b)), (a, b), "seed {seed}");
            assert_eq!(basis.s * ia + basis.t * ib, 1, "seed {seed}: ({a}, {b})");
            let (pa, pb) = (rng.int(-50, 50), rng.int(-50, 50));
            let (big_a, big_b) = (i(pa), i(pb));
            let (e, d) = basis.row(&big_a, &big_b).expect("small");
            assert_eq!(basis.back(&e, &d), Some((big_a, big_b)), "seed {seed}");
            let (x, y) = (i(rng.int(-50, 50)), i(rng.int(-50, 50)));
            let (u, w) = (ia * x + ib * y, -basis.t * x + basis.s * y);
            assert_eq!(
                big_a * x + big_b * y,
                e * u + d * w,
                "seed {seed}: ({a}, {b})"
            );
            // On `Int`, whose cofactors may be others: the same two checks.
            let bi = Basis::new(Int::from(a), Int::from(b)).expect("primitive");
            let one = &(&bi.s * &Int::from(a)) + &(&bi.t * &Int::from(b));
            assert_eq!(one, Int::ONE, "seed {seed}: ({a}, {b})");
            let (ai, bi2) = (Int::from(pa), Int::from(pb));
            let (ei, di) = bi.row(&ai, &bi2).expect("Int");
            assert_eq!(bi.back(&ei, &di), Some((ai, bi2)), "seed {seed}");
        }
    }
}
