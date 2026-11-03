//! The corners: 0 and the largest value of a width, shifts and rotations by 0 and by
//! `width - 1`, and width 1, at every width from 1 to 128; then width 0, where only 0 fits.

use num_bigint::BigInt;
use num_traits::One;
use zed_kernel::{Prim, Value};

use super::{word, x};

fn v(n: BigInt) -> Value {
    Value::int(n)
}

fn run(p: Prim, args: &[Value]) -> Value {
    zed_kernel::bits::word(p, args).unwrap_or_else(|e| panic!("{p:?} {args:?}: {e}"))
}

#[test]
fn zero_and_the_largest_value_of_every_width() {
    for w in 1..=128u32 {
        let top: BigInt = (BigInt::one() << w) - 1;
        let (zero, max, wv) = (v(BigInt::from(0)), v(top.clone()), v(BigInt::from(w)));
        let wn = |n: u32| v(BigInt::from(n));
        assert_eq!(run(Prim::BitNot, &[zero.clone(), wv.clone()]), max, "w {w}");
        assert_eq!(run(Prim::BitNot, &[max.clone(), wv.clone()]), zero, "w {w}");
        assert_eq!(run(Prim::PopCount, std::slice::from_ref(&max)), wn(w));
        assert_eq!(run(Prim::LeadingZeros, &[zero.clone(), wv.clone()]), wn(w));
        assert_eq!(run(Prim::LeadingZeros, &[max.clone(), wv.clone()]), wn(0));
        assert_eq!(run(Prim::TrailingZeros, &[zero.clone(), wv.clone()]), wn(w));
        assert_eq!(run(Prim::TrailingZeros, &[max.clone(), wv.clone()]), wn(0));
        assert_eq!(run(Prim::BitAnd, &[max.clone(), zero.clone()]), zero);
        assert_eq!(run(Prim::BitOr, &[max.clone(), zero.clone()]), max);
        assert_eq!(run(Prim::BitXor, &[max.clone(), max.clone()]), zero);
        for k in [0, w - 1] {
            let kv = wn(k);
            assert_eq!(run(Prim::Rotl, &[max.clone(), kv.clone(), wv.clone()]), max);
            assert_eq!(
                run(Prim::Rotr, &[zero.clone(), kv.clone(), wv.clone()]),
                zero
            );
            let one = v(BigInt::one());
            let high = v(BigInt::one() << k);
            assert_eq!(
                run(Prim::Rotl, &[one.clone(), kv.clone(), wv.clone()]),
                high
            );
            assert_eq!(
                run(Prim::Rotr, &[high.clone(), kv.clone(), wv.clone()]),
                one
            );
            assert_eq!(run(Prim::Shl, &[one.clone(), kv.clone()]), high);
            assert_eq!(run(Prim::Shr, &[high.clone(), kv.clone()]), one);
            assert_eq!(run(Prim::Shl, &[max.clone(), wn(0)]), max);
            assert_eq!(run(Prim::Shr, &[max.clone(), wn(0)]), max);
        }
        // The top digit shifted out by `width - 1` places of `shr`.
        assert_eq!(
            run(Prim::Shr, &[max.clone(), wn(w - 1)]),
            v(BigInt::one()),
            "w {w}"
        );
    }
}

#[test]
fn width_one() {
    for (p, args, out) in [
        (Prim::BitNot, &[0, 1][..], 1),
        (Prim::BitNot, &[1, 1], 0),
        (Prim::LeadingZeros, &[0, 1], 1),
        (Prim::LeadingZeros, &[1, 1], 0),
        (Prim::TrailingZeros, &[0, 1], 1),
        (Prim::TrailingZeros, &[1, 1], 0),
        (Prim::Rotl, &[1, 5, 1], 1),
        (Prim::Rotr, &[1, 0, 1], 1),
        (Prim::Rotl, &[0, 1, 1], 0),
    ] {
        assert_eq!(word(p, args), Value::Int(out), "{p:?} {args:?}");
    }
}

#[test]
fn width_zero_holds_only_zero() {
    assert_eq!(word(Prim::BitNot, &[0, 0]), Value::Int(0));
    assert_eq!(word(Prim::LeadingZeros, &[0, 0]), Value::Int(0));
    assert_eq!(word(Prim::TrailingZeros, &[0, 0]), Value::Int(0));
    assert_eq!(word(Prim::Rotl, &[0, 7, 0]), Value::Int(0));
    assert_eq!(x("rotr(0, 3, width: 0)"), "0");
}

#[test]
fn the_machine_edge() {
    let max = i64::MAX;
    assert_eq!(word(Prim::PopCount, &[max]), Value::Int(63));
    assert_eq!(word(Prim::BitNot, &[max, 63]), Value::Int(0));
    assert_eq!(
        word(Prim::BitNot, &[0, 64]),
        Value::int(BigInt::from(u64::MAX))
    );
    assert_eq!(
        word(Prim::Shl, &[max, 1]),
        Value::int(BigInt::from(max) * 2)
    );
    assert_eq!(
        word(Prim::Shl, &[i64::MIN, 1]),
        Value::int(BigInt::from(i64::MIN) * 2)
    );
    assert_eq!(word(Prim::Shr, &[i64::MIN, 63]), Value::Int(-1));
    assert_eq!(word(Prim::Shr, &[i64::MIN, 64]), Value::Int(-1));
    assert_eq!(
        word(Prim::Rotl, &[max, 1, 64]),
        Value::int(BigInt::from(u64::MAX - 1))
    );
}
