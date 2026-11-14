//! Congruences, affine coefficients and power exponents at and past the 64-bit range (TD-cong).
//! A class's modulus and residue, an affine bound's coefficients and the exponent of `x ^ k`
//! are unbounded integers, so a fact about values near `i64::MAX`, near `-2^127` or far past
//! them is exact: a class is not widened to every integer, a coefficient is not dropped, and
//! a power with an exponent past `u32` is not bounded outward.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use zed_kernel::term::build::var;
use zed_tests::scaling;
use zedc::canon::{Def, Domain, address};
use zedc::store::affine::{Affine, Sym};
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::lattice::{Congruence, FiniteSet, Lattice};
use zedc::store::revision::{Exponent, Op, backward, forward, reduce_congruence};

const MAX: i128 = i64::MAX as i128;
const MIN: i128 = i64::MIN as i128;

fn n(v: i128) -> Num {
    Num::from(v)
}

/// `2^k`, kept as a power past `i128`.
fn two(k: u32) -> Num {
    Num::from(2).pow(k)
}

/// `2^k` written out, a value of the same size in the other form.
fn two_big(k: u32) -> Num {
    Num::from(BigInt::from(2).pow(k))
}

/// The values at the edges of `i64` and `i128` and past them, in both forms past `i128`.
fn edges() -> Vec<Num> {
    vec![
        n(MAX),
        n(MAX + 1),
        n(MIN),
        n(MIN - 1),
        n(i128::MAX),
        n(i128::MIN),
        two(127),
        -&two(127),
        &n(i128::MIN) - &Num::ONE,
        two(200),
        -&two_big(200),
        &two(200) + &n(7),
    ]
}

/// The class `r mod m`, with the residue checked against its definition.
fn class(m: &Num, r: &Num) -> Congruence {
    let c = Congruence::new(m.clone(), r.clone());
    let Congruence::Class { modulus, residue } = &c else {
        unreachable!()
    };
    assert_eq!(modulus, &m.abs());
    if !m.is_zero() {
        assert!(residue.signum() >= 0 && *residue < m.abs(), "{c}");
        assert!((r - residue).rem_euclid(m).is_zero(), "{c}");
    }
    c
}

#[test]
fn two_offsets_past_the_64_bit_range_share_their_least_class() {
    // A pointer's offsets seen at two sites: the class holding both is their difference's
    // multiples through the first, never every integer.
    for a in edges() {
        for b in edges() {
            let j = Congruence::single(a.clone()).join(&Congruence::single(b.clone()));
            let d = (&a - &b).abs();
            assert_eq!(j, class(&d, &a), "{a} ⊔ {b}");
            assert!(j.contains(&a) && j.contains(&b), "{a} ⊔ {b} = {j}");
            if d > Num::ONE {
                // The least class: the value one past `a` is not in it.
                assert!(!j.contains(&(&a + &Num::ONE)), "{a} ⊔ {b} = {j}");
                assert!(j.contains(&(&a + &d)) && j.contains(&(&a - &d)));
            }
        }
    }
}

#[test]
fn a_meet_of_classes_past_the_64_bit_range_is_their_chinese_remainder() {
    // A buffer address aligned to 2^64 (residue `i64::MAX`) and a slot index modulo 3^41
    // (residue -2^127): one class modulo 2^64 · 3^41, past `i128`, which the old 64-bit class
    // could not hold and answered with the coarser operand.
    let (m, n3) = (two_big(64), Num::from(3).pow(41));
    let (r, s) = (n(MAX), n(i128::MIN));
    let meet = class(&m, &r).meet(&class(&n3, &s));
    let l = &m * &n3;
    let Congruence::Class { modulus, residue } = &meet else {
        panic!("{meet}")
    };
    assert_eq!(*modulus, l);
    assert_eq!(residue.rem_euclid(&m), r.rem_euclid(&m));
    assert_eq!(residue.rem_euclid(&n3), s.rem_euclid(&n3));
    assert!(meet.contains(&(residue + &l)) && !meet.contains(&(residue + &Num::ONE)));
    // Moduli sharing the factor 2^70: solvable exactly when the residues agree modulo it.
    let (a, b) = (&two(70) * &n(3), &two(70) * &n(5));
    let r = &two(127) + &n(11);
    let agree = class(&a, &r).meet(&class(&b, &(&r + &(&two(70) * &n(4)))));
    assert_eq!(
        agree,
        class(&(&two(70) * &n(15)), &(&r + &(&two(70) * &n(9))))
    );
    let differ = class(&a, &r).meet(&class(&b, &(&r + &Num::ONE)));
    assert_eq!(differ, Congruence::Bottom);
    // A single value past `i128` meets a class that holds it, and not one that does not.
    let v = -&two(200);
    assert_eq!(
        Congruence::single(v.clone()).meet(&class(&two(64), &Num::ZERO)),
        Congruence::single(v.clone())
    );
    assert_eq!(
        Congruence::single(v).meet(&class(&n(3), &Num::ZERO)),
        Congruence::Bottom
    );
}

#[test]
fn the_normal_form_of_offsets_past_the_64_bit_range_keeps_their_class() {
    // Three offsets 2^64 apart from `i64::MAX`: the least class is `i64::MAX mod 2^64`, where
    // the 64-bit class gave every integer.
    let step = two_big(64);
    let pts: Vec<Num> = (0..3).map(|k| &n(MAX) + &(&step * &n(k))).collect();
    let d = Domain {
        ints: IntervalSet::from_pieces(
            pts.iter()
                .map(|p| (End::Fin(p.clone()), End::Fin(p.clone())))
                .collect(),
        ),
        class: Congruence::top(),
        finite: FiniteSet::Top,
    };
    assert_eq!(d.normal().class, class(&step, &n(MAX)));
    // Below `-2^127`: the same.
    let pts: Vec<Num> = (0..3).map(|k| &n(i128::MIN) - &(&step * &n(k))).collect();
    let d = Domain {
        ints: IntervalSet::from_pieces(
            pts.iter()
                .rev()
                .map(|p| (End::Fin(p.clone()), End::Fin(p.clone())))
                .collect(),
        ),
        class: Congruence::top(),
        finite: FiniteSet::Top,
    };
    assert_eq!(d.normal().class, class(&step, &n(i128::MIN)));
}

fn def(class: Congruence) -> Def {
    Def {
        name: "slot".into(),
        domain: Some(Domain {
            ints: IntervalSet::top(),
            class,
            finite: FiniteSet::Top,
        }),
        facets: vec![],
        body: var("i"),
    }
}

#[test]
fn a_class_past_the_64_bit_range_has_one_address() {
    // The same class written with two residues has one address; classes that differ past the
    // 64-bit range have different ones, and a class inside it keeps its 64-bit encoding.
    let none = |_: &str| None;
    let m = &two(64) * &n(3);
    let a = address(&def(class(&m, &n(5))), &none).expect("memory for the address");
    assert_eq!(
        a,
        address(&def(class(&m, &(&m + &n(5)))), &none).expect("memory for the address")
    );
    assert_ne!(
        a,
        address(&def(class(&m, &n(6))), &none).expect("memory for the address")
    );
    assert_ne!(
        a,
        address(&def(class(&two(64), &n(5))), &none).expect("memory for the address")
    );
    assert_ne!(
        address(&def(class(&n(MAX), &n(5))), &none).expect("memory for the address"),
        address(&def(class(&n(MAX + 1), &n(5))), &none).expect("memory for the address")
    );
}

#[test]
fn an_interval_past_the_64_bit_range_moves_onto_its_class() {
    // `x mod 2^64 == 1` with `x` in `2^127 - 10..=2^127 + 10`: the one member is `2^127 + 1`,
    // and the class becomes that value, where the 64-bit residue left the class as it was.
    let x = IntervalSet::range(End::Fin(&two(127) - &n(10)), End::Fin(&two(127) + &n(10)));
    let (x2, c2) = reduce_congruence(&x, &class(&two_big(64), &Num::ONE));
    let v = &two(127) + &Num::ONE;
    assert_eq!(x2, IntervalSet::point(v.clone()));
    assert_eq!(c2, Congruence::single(v));
    // At `i64::MIN`: `x mod 3 == 1` in `i64::MIN - 4..=i64::MIN + 4`.
    let x = IntervalSet::range(End::Fin(n(MIN - 4)), End::Fin(n(MIN + 4)));
    let (x2, c2) = reduce_congruence(&x, &class(&n(3), &Num::ONE));
    let first = (MIN - 4..).find(|v| v.rem_euclid(3) == 1).unwrap();
    let last = (MIN - 4..=MIN + 4)
        .rev()
        .find(|v| v.rem_euclid(3) == 1)
        .unwrap();
    assert_eq!(
        x2,
        IntervalSet::range(End::Fin(n(first)), End::Fin(n(last)))
    );
    assert_eq!(c2, class(&n(3), &Num::ONE));
    // A single value of the class past `-2^127` keeps it.
    let v = &n(i128::MIN) - &two_big(64);
    let (x2, c2) = reduce_congruence(&IntervalSet::top(), &Congruence::single(v.clone()));
    assert_eq!(
        (x2, c2),
        (IntervalSet::point(v.clone()), Congruence::single(v))
    );
}

#[test]
fn an_affine_bound_scaled_past_the_64_bit_range_is_exact() {
    // `k * n` for a stride `k` at and past the 64-bit range: the coefficient is exact and the
    // bound's value at `n = 3` is `3 k`.
    let at = |_: &Sym| 3i64;
    for k in edges() {
        let a = Affine::sym("n").plus(1).times(k.clone());
        assert_eq!(a.terms[&Sym("n".into())], k);
        assert_eq!(a.constant, k);
        assert_eq!(a.eval(&at), &k * &n(4));
        let shown = a.to_string();
        let (name, coeff) = if k.signum() < 0 {
            (format!("-{} * n", k.abs()), format!(" - {}", k.abs()))
        } else {
            (format!("{k} * n"), format!(" + {k}"))
        };
        assert_eq!(shown, format!("{name}{coeff}"), "{k}");
    }
    // Scaling twice by `-2^127` reaches `2^254`, and by 0 gives the constant 0.
    let a = Affine::sym("n").times(n(i128::MIN)).times(n(i128::MIN));
    assert_eq!(a.terms[&Sym("n".into())], two(254));
    assert_eq!(
        Affine::sym("n").times(two(200)).times(0),
        Affine::constant(0)
    );
    // By 1 and -1: the bound and its negation.
    assert_eq!(Affine::sym("n").times(1).to_string(), "n");
    assert_eq!(Affine::sym("n").times(-1).to_string(), "-n");
}

fn pow(k: impl Into<Num>) -> Op {
    Op::Pow(Exponent::Num(k.into()))
}

fn point(v: Num) -> IntervalSet {
    IntervalSet::point(v)
}

#[test]
fn powers_past_u32_are_exact() {
    // `3 ^ 2^32`, past `u32`: the square of `3 ^ 2^31`, found without the exponent.
    let k = 1i128 << 32;
    let want = Num::from(9).pow(1 << 31);
    assert_eq!(forward(&pow(k), &point(n(3)), &point(n(3))), point(want));
    // `(-2) ^ i64::MAX`: odd, so negative; and `2 ^ (2^127 - 1)`, `2 ^ -2^127`'s magnitude.
    let neg = forward(&pow(n(MAX)), &point(n(-2)), &point(n(-2)));
    assert_eq!(neg, point(-&Num::pow2(&n(MAX))));
    let big = forward(&pow(n(i128::MAX)), &point(n(2)), &point(n(2)));
    assert_eq!(big, point(Num::pow2(&n(i128::MAX))));
    // An exponent past `i128` written out: `2 ^ 2^200` and `(-1) ^ (2^200 + 1)`.
    let e = two_big(200);
    assert_eq!(
        forward(&pow(e.clone()), &point(n(2)), &point(n(2))),
        point(Num::pow2(&e))
    );
    assert_eq!(
        forward(&pow(&e + &Num::ONE), &point(n(-1)), &point(n(-1))),
        point(n(-1))
    );
    // A kept power raised past `u32`: its exponents multiply.
    let x = forward(&pow(k), &point(two(200)), &point(two(200)));
    assert_eq!(x, point(Num::pow2(&n(200 * k))));
    // Over a range: `x ^ (2^32 + 1)` is increasing.
    let r = IntervalSet::of(-2, 3);
    assert_eq!(
        forward(&pow(k + 1), &r, &r),
        IntervalSet::range(
            End::Fin(-&Num::pow2(&n(k + 1))),
            End::Fin(Num::from(3).pow_by(&n(k + 1)).unwrap())
        )
    );
}

#[test]
fn roots_past_u32_are_exact() {
    // `x ^ 2^32 <= 3 ^ 2^32 - 1` holds for `x` in `-2..=2`; the bound for `u32::MAX` gave
    // `-3..=3`.
    let k = 1i128 << 32;
    let top = &Num::from(3).pow_by(&n(k)).unwrap() - &Num::ONE;
    let z = IntervalSet::range(End::of(0), End::Fin(top.clone()));
    let all = IntervalSet::top();
    assert_eq!(backward(&pow(k), 0, &all, &all, &z), IntervalSet::of(-2, 2));
    // `x ^ (2^32 + 1) >= 2 ^ (2^32 + 1)`: `x >= 2`.
    let z = IntervalSet::range(End::Fin(Num::pow2(&n(k + 1))), End::PosInf);
    assert_eq!(
        backward(&pow(k + 1), 0, &all, &all, &z),
        IntervalSet::range(End::of(2), End::PosInf)
    );
    // `x ^ (2^32 + 1) == 2 * 3 ^ (2^32 + 1)`: no integer, the root lying between 3 and 4.
    let v = &Num::from(3).pow_by(&n(k + 1)).unwrap() * &n(2);
    let r = backward(&pow(k + 1), 0, &all, &all, &point(v));
    assert!(r.is_empty(), "{r}");
    // `x ^ (2^32 + 1) == 3 ^ (2^32 + 1) + 1`, a sum: no integer. The prime factors of `2^32 + 1`
    // are 641 and 6700417, so the residue test first applies at the prime 1283.
    let v = &Num::from(3).pow_by(&n(k + 1)).unwrap() + &Num::ONE;
    let r = backward(&pow(k + 1), 0, &all, &all, &point(v));
    assert!(r.is_empty(), "{r}");
}

#[test]
fn an_exponent_with_no_exact_form_bounds_outward() {
    // Corner cases. A sum past `i128` raised past `u32` has no kept form: the bound is
    // `2 ^ u32::MAX` toward 0 and infinite away from it, and it is sound.
    let s = &two(200) + &Num::ONE;
    let k = 1i128 << 32;
    let x = forward(&pow(k), &point(s.clone()), &point(s));
    assert_eq!(
        x,
        IntervalSet::range(End::Fin(Num::from(2).pow(u32::MAX)), End::PosInf)
    );
    // A kept exponent, `2 ^ 200` from a power: the same bound; the bases -1, 0 and 1 are
    // exact by its parity.
    let e = two(200);
    let x = forward(&pow(e.clone()), &point(n(5)), &point(n(5)));
    assert_eq!(
        x,
        IntervalSet::range(End::Fin(Num::from(2).pow(u32::MAX)), End::PosInf)
    );
    for b in [-1, 0, 1] {
        let want = if b == -1 { 1 } else { b };
        assert_eq!(
            forward(&pow(e.clone()), &point(n(b)), &point(n(b))),
            point(n(want))
        );
    }
    // The exponent 0 past `u32`'s parity reading: `x ^ 0` is 1, and the class of the empty
    // join is the bottom.
    assert_eq!(
        forward(&pow(0), &IntervalSet::of(-5, 5), &IntervalSet::of(-5, 5)),
        point(Num::ONE)
    );
    assert_eq!(
        Congruence::Bottom.join(&Congruence::Bottom),
        Congruence::Bottom
    );
}

mod bench;
