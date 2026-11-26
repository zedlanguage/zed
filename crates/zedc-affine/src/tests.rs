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
