//! The forward transfer of the bit words on intervals: sound on 100,000 random interval pairs
//! (each sampled member's value lies in the result), exact on single values, and the cases
//! DESIGN.md step L1.39a names, `shl(1, 30)` inside `i32` and `shl(1, 31)` outside it, and
//! `x.bitAnd(255)` with `x : int[0..]` in `int[0..=255]`.

use zed_kernel::{Prim, Value};
use zed_tests::instances::Rng;
use zedc::store::interval::{
    End::{self, Fin, NegInf, PosInf},
    IntervalSet, Num, bit_word,
};

/// Whether the value `v` lies in `s`, at any size.
fn holds(s: &IntervalSet, v: &Value) -> bool {
    match v {
        Value::Int(n) => s.contains(*n),
        Value::Big(n) => s.contains_end(&Fin(Num::from(&**n))),
        _ => false,
    }
}

/// A random end: small values often, the `i64` edges and the infinities sometimes.
fn end(rng: &mut Rng, around: i64) -> i64 {
    match rng.below(8) {
        0 => i64::MAX - rng.int(0, 3),
        1 => i64::MIN + rng.int(0, 3),
        2 => around + rng.int(-300, 300),
        _ => rng.int(-70, 70),
    }
}

/// A random set of one or two pieces, sometimes unbounded.
fn set(rng: &mut Rng) -> IntervalSet {
    let mut pieces = Vec::new();
    for _ in 0..1 + rng.below(2) {
        let a = end(rng, 0);
        let b = a.saturating_add(rng.int(0, 40));
        let lo = if rng.below(10) == 0 {
            NegInf
        } else {
            End::of(a)
        };
        let hi = if rng.below(10) == 0 {
            PosInf
        } else {
            End::of(b)
        };
        pieces.push((lo, hi));
    }
    IntervalSet::from_pieces(pieces)
}

/// A random member of the non-empty `s`, near one of its ends or inside a piece.
fn member(rng: &mut Rng, s: &IntervalSet) -> i64 {
    let (lo, hi) = s
        .pieces()
        .nth(rng.below(s.len()))
        .expect("a piece below the count");
    let (lo, hi) = (lo.to_i64(), hi.to_i64());
    let lo = match lo {
        Some(v) => v,
        _ => match hi {
            Some(h) => h.saturating_sub(rng.int(0, 1 << 20)),
            _ => rng.int(-100, 100),
        },
    };
    let hi = match hi {
        Some(v) => v,
        _ => lo.saturating_add(rng.int(0, 1 << 20)),
    };
    let span = (hi as i128 - lo as i128) as u128;
    let off = match rng.below(3) {
        0 => 0,
        1 => span,
        _ => u128::from(rng.next_u64()) % (span + 1),
    };
    (lo as i128 + off as i128) as i64
}

const WORDS: [Prim; 11] = [
    Prim::BitAnd,
    Prim::BitOr,
    Prim::BitXor,
    Prim::BitNot,
    Prim::Shl,
    Prim::Shr,
    Prim::PopCount,
    Prim::LeadingZeros,
    Prim::TrailingZeros,
    Prim::Rotl,
    Prim::Rotr,
];

#[test]
fn the_transfer_is_sound_on_random_interval_pairs() {
    let mut rng = Rng::new(0x1_39a);
    let mut checked = 0usize;
    for i in 0..100_000 {
        let p = WORDS[i % WORDS.len()];
        let n = p.arity().expect("a bit word has a fixed arity");
        let sets: Vec<IntervalSet> = (0..n).map(|_| set(&mut rng)).collect();
        let out = bit_word(p, &sets);
        for _ in 0..8 {
            let args: Vec<Value> = sets
                .iter()
                .map(|s| Value::Int(member(&mut rng, s)))
                .collect();
            // A tuple outside the word's domain has no value to hold.
            let Ok(v) = zed_kernel::bits::word(p, &args) else {
                continue;
            };
            checked += 1;
            assert!(
                holds(&out, &v),
                "{p:?} of {sets:?} gives {out}, which lacks {v}, the value at {args:?}"
            );
        }
    }
    assert!(
        checked > 200_000,
        "only {checked} tuples were in the domain"
    );
}

#[test]
fn single_values_give_the_value() {
    let one = |v: i64| IntervalSet::single(v);
    assert_eq!(bit_word(Prim::BitNot, &[one(5), one(3)]), one(2));
    assert_eq!(bit_word(Prim::Rotl, &[one(8), one(1), one(4)]), one(1));
    assert_eq!(bit_word(Prim::TrailingZeros, &[one(0), one(8)]), one(8));
    assert_eq!(bit_word(Prim::Shr, &[one(-17), one(2)]), one(-5));
    // Outside the domain: no value.
    assert_eq!(
        bit_word(Prim::BitAnd, &[one(-1), one(1)]),
        IntervalSet::empty()
    );
    assert_eq!(
        bit_word(Prim::BitNot, &[one(8), one(3)]),
        IntervalSet::empty()
    );
}

#[test]
fn a_shift_inside_and_outside_i32() {
    let i32s = IntervalSet::of(i64::from(i32::MIN), i64::from(i32::MAX));
    let one = IntervalSet::single(1);
    let inside = bit_word(Prim::Shl, &[one.clone(), IntervalSet::single(30)]);
    assert_eq!(inside, IntervalSet::single(1 << 30));
    assert!(inside.is_subset(&i32s));
    let outside = bit_word(Prim::Shl, &[one, IntervalSet::single(31)]);
    assert_eq!(outside, IntervalSet::single(1 << 31));
    assert!(!outside.is_subset(&i32s));
}

#[test]
fn masking_a_non_negative_int_with_255() {
    let x = IntervalSet::range(End::of(0), PosInf);
    let out = bit_word(Prim::BitAnd, &[x, IntervalSet::single(255)]);
    assert_eq!(out, IntervalSet::of(0, 255));
    assert_eq!(out.to_string(), "[0..=255]");
}

#[test]
fn the_rules_on_ranges() {
    let r = |lo: i64, hi: i64| IntervalSet::of(lo, hi);
    let from = |lo: i64| IntervalSet::range(End::of(lo), PosInf);
    assert_eq!(bit_word(Prim::BitOr, &[r(4, 9), r(0, 3)]), r(4, 15));
    assert_eq!(bit_word(Prim::BitXor, &[r(0, 16), r(0, 3)]), r(0, 31));
    assert_eq!(bit_word(Prim::PopCount, &[r(1, 255)]), r(1, 8));
    assert_eq!(bit_word(Prim::PopCount, &[from(0)]), from(0));
    assert_eq!(bit_word(Prim::BitNot, &[r(0, 3), r(8, 8)]), r(252, 255));
    assert_eq!(bit_word(Prim::LeadingZeros, &[r(1, 255), r(8, 8)]), r(0, 7));
    assert_eq!(
        bit_word(Prim::TrailingZeros, &[r(0, 255), r(8, 8)]),
        r(0, 8)
    );
    assert_eq!(bit_word(Prim::TrailingZeros, &[r(1, 7), r(8, 8)]), r(0, 2));
    assert_eq!(
        bit_word(Prim::Rotl, &[r(1, 15), r(0, 9), r(4, 4)]),
        r(1, 15)
    );
    assert_eq!(
        bit_word(Prim::Shl, &[r(-3, 3), r(1, 2)]),
        IntervalSet::from_pieces(vec![
            (End::of(-12), End::of(-2)),
            (End::of(0), End::of(0)),
            (End::of(2), End::of(12))
        ])
    );
    assert_eq!(bit_word(Prim::Shr, &[r(-8, 8), r(1, 2)]), r(-4, 4));
    // Every int: the domain leaves the non-negative part.
    let all = IntervalSet::top();
    assert_eq!(bit_word(Prim::BitAnd, &[all.clone(), r(0, 7)]), r(0, 7));
    assert_eq!(bit_word(Prim::Shr, &[r(5, 5), from(0)]), r(0, 5));
    assert_eq!(
        bit_word(Prim::Shl, &[r(1, 1), from(0)]),
        IntervalSet::range(End::of(1), PosInf)
    );
    assert_eq!(
        bit_word(Prim::F64Bits, &[all]),
        IntervalSet::range(End::of(0), End::from((1i128 << 64) - 1))
    );
    // A product past `i64` is exact.
    let past = bit_word(Prim::Shl, &[r(1, 1), r(70, 80)]);
    assert_eq!(
        past,
        IntervalSet::range(End::from(1i128 << 70), End::from(1i128 << 80))
    );
}
