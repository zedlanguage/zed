//! Each word against a reference written on `u128` and `i128`, on random values at every width
//! from 1 to 128, so the operands cross `i64` and the kernel's exact path runs as well as its
//! machine path.

use num_bigint::BigInt;
use zed_kernel::{Prim, Value};
use zed_tests::instances::Rng;

/// The int `n` as a value.
fn v(n: u128) -> Value {
    Value::int(BigInt::from(n))
}

fn vi(n: i128) -> Value {
    Value::int(BigInt::from(n))
}

fn run(p: Prim, args: &[Value]) -> Value {
    zed_kernel::bits::word(p, args).unwrap_or_else(|e| panic!("{p:?} {args:?}: {e}"))
}

/// The `w` low ones.
fn mask(w: u32) -> u128 {
    if w == 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    }
}

/// A random value of at most `w` binary digits, its length itself random, so small values
/// are as likely as wide ones.
fn below(rng: &mut Rng, w: u32) -> u128 {
    let len = 1 + rng.below(w as usize) as u32;
    let bits = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
    bits & mask(len)
}

#[test]
fn every_word_against_the_reference_at_every_width() {
    let mut rng = Rng::new(0x39a);
    for w in 1..=128u32 {
        let wv = v(u128::from(w));
        for _ in 0..64 {
            let (a, b) = (below(&mut rng, w), below(&mut rng, w));
            let k = rng.below(2 * w as usize) as u32;
            let what = format!("w {w}, a {a}, b {b}, k {k}");
            assert_eq!(run(Prim::BitAnd, &[v(a), v(b)]), v(a & b), "{what}");
            assert_eq!(run(Prim::BitOr, &[v(a), v(b)]), v(a | b), "{what}");
            assert_eq!(run(Prim::BitXor, &[v(a), v(b)]), v(a ^ b), "{what}");
            assert_eq!(
                run(Prim::BitNot, &[v(a), wv.clone()]),
                v(!a & mask(w)),
                "{what}"
            );
            assert_eq!(
                run(Prim::PopCount, &[v(a)]),
                v(u128::from(a.count_ones())),
                "{what}"
            );
            assert_eq!(
                run(Prim::LeadingZeros, &[v(a), wv.clone()]),
                v(u128::from(w - (128 - a.leading_zeros()))),
                "{what}"
            );
            let tz = if a == 0 { w } else { a.trailing_zeros() };
            assert_eq!(
                run(Prim::TrailingZeros, &[v(a), wv.clone()]),
                v(u128::from(tz)),
                "{what}"
            );
            let r = k % w;
            let rotl = if r == 0 {
                a
            } else {
                ((a << r) | (a >> (w - r))) & mask(w)
            };
            let rotr = if r == 0 {
                a
            } else {
                ((a >> r) | (a << (w - r))) & mask(w)
            };
            let kv = v(u128::from(k));
            assert_eq!(
                run(Prim::Rotl, &[v(a), kv.clone(), wv.clone()]),
                v(rotl),
                "{what}"
            );
            assert_eq!(
                run(Prim::Rotr, &[v(a), kv.clone(), wv.clone()]),
                v(rotr),
                "{what}"
            );
            // The shifts, on a signed `x` of at most 63 digits and a count that keeps the
            // product inside `i128`.
            let x = (a & mask(63)) as i128 * if rng.below(2) == 0 { 1 } else { -1 };
            let k = rng.below(64) as u32;
            assert_eq!(
                run(Prim::Shl, &[vi(x), kv_of(k)]),
                vi(x << k),
                "{what}, x {x}"
            );
            let k = rng.below(140) as u32;
            let shr = if k >= 127 {
                if x < 0 { -1 } else { 0 }
            } else {
                x >> k
            };
            assert_eq!(run(Prim::Shr, &[vi(x), kv_of(k)]), vi(shr), "{what}, x {x}");
        }
    }
}

fn kv_of(k: u32) -> Value {
    Value::Int(i64::from(k))
}

#[test]
fn f64_bits_is_the_ieee_754_encoding() {
    let mut rng = Rng::new(64);
    for _ in 0..10_000 {
        let f = f64::from_bits(rng.next_u64());
        if f.is_nan() {
            continue;
        }
        assert_eq!(
            run(Prim::F64Bits, &[Value::float(f)]),
            v(u128::from(f.to_bits())),
            "{f}"
        );
    }
    for f in [
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::MIN_POSITIVE,
        f64::MAX,
        -0.0,
    ] {
        assert_eq!(
            run(Prim::F64Bits, &[Value::float(f)]),
            v(u128::from(f.to_bits()))
        );
    }
}
