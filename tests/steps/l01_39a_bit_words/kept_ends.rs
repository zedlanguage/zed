//! Bit words on interval ends kept as powers (ledger BIT-kept-ends): the bits and trailing
//! zeros of a kept end, a shift right of one and a power of 2 by a kept exponent are found from
//! the kept form, without the value's digits. Each is checked against the value written out,
//! at sizes where writing it out is cheap, and the bit words' rules on widths near `i64::MAX`,
//! whose ends `2 ** w - 1` have about `2^63` digits, finish at once.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_integer::Integer;
use zed_kernel::Prim;
use zed_tests::scaling;
use zedc::store::interval::{
    End::{self, Fin, PosInf},
    IntervalSet, Num, bit_word,
};

/// The value written out.
fn written(n: &Num) -> BigInt {
    n.to_string()
        .parse()
        .expect("a value prints as decimal digits")
}

fn pow2(k: i64) -> Num {
    Num::pow2(&Num::from(k))
}

/// Kept values and their neighbors near the edges of `i128` and past them: powers of 2 and
/// their neighbors, powers of bases that are not powers of 2 (12 has two trailing zeros),
/// sums of unrelated powers, multiples of powers of 2, a product of powers of two integers, a
/// quotient by a value that is not kept (a kept form with a denominator), and the negation of
/// each.
fn values() -> Vec<(String, Num)> {
    let one = Num::ONE;
    let mut out: Vec<(String, Num)> = Vec::new();
    for k in [126, 127, 128, 129, 200, 1000, 4097] {
        let p = pow2(k);
        out.push((format!("2 ** {k}"), p.clone()));
        out.push((format!("2 ** {k} - 1"), &p - &one));
        out.push((format!("2 ** {k} + 1"), &p + &one));
        out.push((format!("2 ** {k} - 2 ** {}", k - 1), &p - &pow2(k - 1)));
        out.push((
            format!("3 * 2 ** {k} + 5"),
            &(&p * &Num::from(3)) + &Num::from(5),
        ));
        out.push((format!("2 ** {k} + 2 ** {}", k - 100), &p + &pow2(k - 100)));
        out.push((
            format!("(2 ** {k} + 6) div 2"),
            (&p + &Num::from(6)).div_floor(&Num::from(2)),
        ));
    }
    for e in [80u32, 81, 82, 300, 1001] {
        let three = Num::from(3).pow(e);
        let five = Num::from(5).pow(e);
        let twelve = Num::from(12).pow(e);
        out.push((format!("3 ** {e}"), three.clone()));
        out.push((format!("3 ** {e} - 1"), &three - &one));
        out.push((format!("12 ** {e}"), twelve.clone()));
        out.push((format!("3 ** {e} + 5 ** {e}"), &three + &five));
        out.push((
            format!("3 ** {e} - 2 ** {}", e + 1),
            &three - &pow2(i64::from(e) + 1),
        ));
        out.push((
            format!("12 ** {e} * 5 ** {e} + 2 ** {e}"),
            &(&twelve * &Num::from(5).pow(e + 1)) + &pow2(i64::from(e)),
        ));
    }
    let negated: Vec<(String, Num)> = out.iter().map(|(s, n)| (format!("-({s})"), -n)).collect();
    out.extend(negated);
    out
}

#[test]
fn bits_and_trailing_zeros_of_kept_ends_are_those_written_out() {
    for (what, n) in values() {
        let v = written(&n);
        assert_eq!(
            written(&n.bits()),
            BigInt::from(v.bits()),
            "the bits of {what}"
        );
        assert_eq!(
            written(&n.trailing_zeros()),
            BigInt::from(v.trailing_zeros().expect("not 0")),
            "the trailing zeros of {what}"
        );
    }
}

#[test]
fn the_trailing_zeros_of_a_kept_root_are_those_written_out() {
    // floor(3 ** (k / 2)) for odd k is kept as a root, whose digits the low bits need.
    for k in [301u32, 1001] {
        let r = Num::from(3).pow(k).floor_root(2);
        let v = written(&r);
        assert_eq!(written(&r.bits()), BigInt::from(v.bits()));
        assert_eq!(
            written(&r.trailing_zeros()),
            BigInt::from(v.trailing_zeros().expect("not 0"))
        );
    }
}

#[test]
fn a_shift_right_of_a_kept_end_keeps_its_form() {
    let one = Num::ONE;
    for w in [300i64, 1000] {
        let p = pow2(w);
        let xs = [
            &p - &one,
            &(&p * &Num::from(3)) + &Num::from(5),
            &p + &Num::from(3).pow(150),
            -&(&p + &one),
            &(-&p) + &Num::from(7),
        ];
        for x in &xs {
            for k in [127, 128, 150, w - 1, w] {
                let q = x.div_floor(&pow2(k));
                let expected = written(x).div_floor(&(BigInt::from(1) << k));
                assert_eq!(written(&q), expected, "floor(({x}) / 2 ** {k})");
                let out = bit_word(
                    Prim::Shr,
                    &[IntervalSet::point(x.clone()), IntervalSet::single(k)],
                );
                assert_eq!(out, IntervalSet::point(q), "shr({x}, {k})");
            }
        }
    }
}

#[test]
fn a_power_of_2_by_a_kept_exponent_stays_kept() {
    // 2 ** (2 ** 200): its bits are 2 ** 200 + 1 and its trailing zeros 2 ** 200, from the
    // exponent alone; written out it would take 2^200 bits.
    let e = pow2(200);
    let p = Num::pow2(&e);
    assert_eq!(p.bits(), &e + &Num::ONE);
    assert_eq!(p.trailing_zeros(), e);
    assert_eq!((&p - &Num::ONE).bits(), e);
    assert_eq!((&p - &Num::ONE).trailing_zeros(), Num::ZERO);
}

#[test]
fn single_kept_operands_give_the_value() {
    let p = pow2(200);
    let point = |n: &Num| IntervalSet::point(n.clone());
    assert_eq!(
        bit_word(Prim::Shl, &[point(&p), IntervalSet::single(3)]),
        point(&pow2(203))
    );
    assert_eq!(
        bit_word(Prim::PopCount, &[point(&(&p - &Num::ONE))]),
        IntervalSet::single(200)
    );
    assert_eq!(
        bit_word(Prim::TrailingZeros, &[point(&p), IntervalSet::single(201)]),
        IntervalSet::single(200)
    );
}

#[test]
fn the_rules_on_widths_near_i64_max_read_the_bits_of_kept_ends() {
    // x in [0..] with a width near i64::MAX is met with [0..=2 ** w - 1], an end of about 2^63
    // digits, whose bits each rule reads.
    let w = i64::MAX;
    let x = IntervalSet::range(End::of(1), PosInf);
    let width = IntervalSet::single(w);
    assert_eq!(
        bit_word(Prim::LeadingZeros, &[x.clone(), width.clone()]),
        IntervalSet::of(0, w - 1)
    );
    assert_eq!(
        bit_word(Prim::TrailingZeros, &[x.clone(), width.clone()]),
        IntervalSet::of(0, w - 1)
    );
    assert_eq!(
        bit_word(Prim::BitNot, &[x, width]),
        IntervalSet::range(End::of(0), Fin(&pow2(w) - &Num::from(2)))
    );
}

/// Kept ends at the exponent `k`, each with the power of 2 that a shift right divides it by
/// when its terms are multiples of that power (a shift of `3 ** k` writes it out; see
/// `Num::div_floor`).
fn ends(k: i64) -> Vec<(Num, Option<Num>)> {
    let one = Num::ONE;
    let p = pow2(k);
    let e = u32::try_from(k).expect("an exponent of a scaling test");
    let three = Num::from(3).pow(e);
    vec![
        (p.clone(), Some(pow2(k / 2))),
        (&p - &one, Some(pow2(k / 2))),
        (-&(&p + &one), Some(pow2(k - 1))),
        (&(&p * &Num::from(3)) + &Num::from(5), Some(pow2(k / 3))),
        (three.clone(), None),
        (&three + &Num::from(5).pow(e), None),
        (Num::from(12).pow(e), None),
        (&three - &pow2(k + 1), None),
    ]
}

#[test]
fn bits_and_trailing_zeros_of_kept_ends_do_not_grow_with_the_exponent() {
    // The bits, trailing zeros and shift right of kept ends of exponents k and 8k, and the
    // rules that read the bits of 2 ** k - 1. Written out, each grows with the digits, 8
    // times or more.
    let n = 1 << 20;
    let built: HashMap<usize, Vec<(Num, Option<Num>)>> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, ends(m as i64)))
        .collect();
    scaling::check_order(
        "bits, trailing zeros and shr of kept ends of exponent k",
        n,
        0,
        |m| {
            let width = IntervalSet::single(m as i64);
            let x = IntervalSet::range(End::of(1), PosInf);
            for (v, p) in &built[&m] {
                std::hint::black_box(v.bits());
                std::hint::black_box(v.trailing_zeros());
                if let Some(p) = p {
                    std::hint::black_box(v.div_floor(p));
                }
            }
            std::hint::black_box(bit_word(Prim::LeadingZeros, &[x.clone(), width.clone()]));
            std::hint::black_box(bit_word(Prim::TrailingZeros, &[x, width]));
        },
    );
}
