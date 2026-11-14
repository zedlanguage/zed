//! The forward transfer of the machine operations on intervals: sound on random operand
//! intervals at widths up to 128 (each sampled member's value lies in the result), exact on
//! single values, and as tight as DESIGN.md step L1.39f states: `mulHi` and `bitReverse` and
//! `byteSwap` below `2 ^ w`, `pdep` at most `mask`, `pext` below `2 ^ popCount(mask)` and
//! at most `x`. DESIGN gives no bound for the funnel shifts; they take the hull below `2 ^ w`.

use num_bigint::BigInt;
use zed_kernel::{Prim, Value};
use zed_tests::instances::Rng;
use zedc::store::interval::{
    End::{self, Fin, PosInf},
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

fn end(n: u128) -> End {
    End::from(i128::try_from(n).expect("below 2^127"))
}

/// `[lo..=hi]`, at any size below `2 ^ 127`.
fn range(lo: u128, hi: u128) -> IntervalSet {
    IntervalSet::range(end(lo), end(hi))
}

/// A random value of at most `w` binary digits, its length itself random.
fn below(rng: &mut Rng, w: u32) -> u128 {
    let len = rng.below(w as usize + 1) as u32;
    let bits = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
    if len == 0 {
        0
    } else {
        bits & (u128::MAX >> (128 - len))
    }
}

/// A random interval of values of at most `w` digits, sometimes one value, and a random member.
fn interval(rng: &mut Rng, w: u32) -> (u128, u128) {
    let (a, b) = (below(rng, w), below(rng, w));
    match rng.below(4) {
        0 => (a, a),
        _ => (a.min(b), a.max(b)),
    }
}

fn member(rng: &mut Rng, (lo, hi): (u128, u128)) -> u128 {
    match rng.below(3) {
        0 => lo,
        1 => hi,
        _ => {
            lo + (((u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64())) % (hi - lo + 1))
        }
    }
}

const WORDS: [Prim; 7] = [
    Prim::MulHi,
    Prim::BitReverse,
    Prim::ByteSwap,
    Prim::Pdep,
    Prim::Pext,
    Prim::FunnelShl,
    Prim::FunnelShr,
];

#[test]
fn the_transfer_is_sound_on_random_intervals() {
    let mut rng = Rng::new(0x1_39f);
    let mut checked = 0usize;
    for i in 0..70_000 {
        let p = WORDS[i % WORDS.len()];
        let w = 1 + rng.below(126) as u32;
        let width = |rng: &mut Rng| {
            let w = if p == Prim::ByteSwap { w / 8 * 8 } else { w };
            match rng.below(3) {
                0 => (u128::from(w), u128::from(w)),
                _ => (u128::from(w), u128::from(w) + rng.below(4) as u128),
            }
        };
        // The operands, in parameter order: an int below `2 ^ w`, a mask, a count below `w`.
        let ivs: Vec<(u128, u128)> = match p {
            Prim::MulHi => vec![
                interval(&mut rng, w),
                interval(&mut rng, w),
                width(&mut rng),
            ],
            Prim::BitReverse | Prim::ByteSwap => vec![interval(&mut rng, w), width(&mut rng)],
            Prim::Pdep | Prim::Pext => vec![interval(&mut rng, 127), interval(&mut rng, w)],
            _ => {
                let k = rng.below(w as usize) as u128;
                let k_hi = k + rng.below(3) as u128;
                vec![
                    interval(&mut rng, w),
                    interval(&mut rng, w),
                    (k, k_hi),
                    width(&mut rng),
                ]
            }
        };
        let sets: Vec<IntervalSet> = ivs.iter().map(|&(lo, hi)| range(lo, hi)).collect();
        let out = bit_word(p, &sets);
        for _ in 0..8 {
            let args: Vec<Value> = ivs
                .iter()
                .map(|&iv| Value::int(BigInt::from(member(&mut rng, iv))))
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
        checked > 300_000,
        "only {checked} tuples were in the domain"
    );
}

#[test]
fn single_values_give_the_value() {
    let one = IntervalSet::single;
    assert_eq!(
        bit_word(Prim::MulHi, &[one(1 << 62), one(4), one(64)]),
        one(1)
    );
    assert_eq!(bit_word(Prim::BitReverse, &[one(1), one(8)]), one(128));
    assert_eq!(
        bit_word(Prim::ByteSwap, &[one(0x0102), one(16)]),
        one(0x0201)
    );
    assert_eq!(
        bit_word(Prim::Pdep, &[one(0b101), one(0b11010)]),
        one(0b10010)
    );
    assert_eq!(
        bit_word(Prim::Pext, &[one(0b10010), one(0b11010)]),
        one(0b101)
    );
    assert_eq!(
        bit_word(Prim::FunnelShl, &[one(1), one(0), one(0), one(8)]),
        one(1)
    );
    // Outside the domain: no value.
    let none = IntervalSet::empty();
    assert_eq!(bit_word(Prim::ByteSwap, &[one(1), one(12)]), none);
    assert_eq!(
        bit_word(Prim::FunnelShl, &[one(1), one(2), one(8), one(8)]),
        none
    );
    assert_eq!(bit_word(Prim::MulHi, &[one(256), one(1), one(8)]), none);
}

#[test]
fn the_bounds_design_states() {
    let r = |lo: i64, hi: i64| IntervalSet::of(lo, hi);
    let all = IntervalSet::top();
    let from = |lo: i64| IntervalSet::range(End::of(lo), PosInf);
    // `mulHi` by the corners: `(20 * 40) div 2^8 ..= (30 * 50) div 2^8`, and below `2 ^ w`.
    assert_eq!(
        bit_word(Prim::MulHi, &[r(20, 30), r(40, 50), r(8, 8)]),
        r(3, 5)
    );
    assert_eq!(
        bit_word(Prim::MulHi, &[all.clone(), all.clone(), r(8, 8)]),
        r(0, 254)
    );
    assert_eq!(
        bit_word(Prim::MulHi, &[all.clone(), all.clone(), r(64, 64)]),
        range(0, (1u128 << 64) - 2)
    );
    // A wider width lowers the low end and caps the high end.
    assert_eq!(
        bit_word(Prim::MulHi, &[r(16, 16), r(16, 16), r(4, 8)]),
        r(1, 16)
    );
    // `bitReverse` and `byteSwap` below `2 ^ w`, from 1 when 0 is not a member.
    assert_eq!(
        bit_word(Prim::BitReverse, &[all.clone(), r(8, 8)]),
        r(0, 255)
    );
    assert_eq!(bit_word(Prim::BitReverse, &[r(1, 3), r(8, 8)]), r(1, 255));
    assert_eq!(bit_word(Prim::BitReverse, &[r(0, 0), from(0)]), r(0, 0));
    assert_eq!(
        bit_word(Prim::ByteSwap, &[all.clone(), r(16, 16)]),
        r(0, 65535)
    );
    // `pdep` at most `mask`; `pext` at most `x` and below `2 ^ m`, `m` the most one digits of
    // a mask in the hull: 4 in 0 ..= 26 (15 and 23).
    assert_eq!(
        bit_word(Prim::Pdep, &[all.clone(), r(0, 0b11010)]),
        r(0, 0b11010)
    );
    assert_eq!(
        bit_word(Prim::Pext, &[all.clone(), r(0, 0b11010)]),
        r(0, 15)
    );
    assert_eq!(bit_word(Prim::Pext, &[r(0, 6), r(0, 0b11010)]), r(0, 6));
    assert_eq!(bit_word(Prim::Pext, &[all.clone(), from(0)]), from(0));
    // The funnel shifts: the hull below `2 ^ w`, 0 when both halves are.
    assert_eq!(
        bit_word(
            Prim::FunnelShl,
            &[all.clone(), all.clone(), all.clone(), r(8, 8)]
        ),
        r(0, 255)
    );
    assert_eq!(
        bit_word(Prim::FunnelShr, &[r(0, 0), r(0, 0), all.clone(), r(8, 8)]),
        r(0, 0)
    );
    // The count is met with `0 ..< w`: a count range wholly at or past `w` leaves no value.
    assert_eq!(
        bit_word(Prim::FunnelShl, &[r(1, 1), r(1, 1), from(8), r(8, 8)]),
        IntervalSet::empty()
    );
    // Every int as the width: no bound but the operands'.
    assert_eq!(bit_word(Prim::Pdep, &[all.clone(), all.clone()]), from(0));
    assert_eq!(bit_word(Prim::BitReverse, &[r(1, 1), all]), from(1));
}
