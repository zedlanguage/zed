//! The words' time against the number of calls and against the digits of their operands (the
//! rule of low complexity, DESIGN.md Part G). Each word over n and 8n random `u64` values at
//! width 64 is O(n); `pdep` and `pext` on a mask of n and 8n digits are O(n), one step per digit
//! of the mask by their definitions; the other words at width n and 8n are O(n) but `mulHi`,
//! whose cost at a wide width is that of `*`. Every operand is built before the timing.

use num_bigint::{BigInt, BigUint};
use zed_kernel::{Prim, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;

fn run(p: Prim, args: &[Value]) -> Value {
    zed_kernel::bits::word(p, args).unwrap_or_else(|e| panic!("{p:?}: {e}"))
}

fn u64s(rng: &mut Rng, n: usize) -> Vec<Value> {
    (0..n)
        .map(|_| Value::int(BigInt::from(rng.next_u64())))
        .collect()
}

#[test]
fn each_word_is_linear_in_the_number_of_u64_values() {
    let n = 1 << 14;
    let ops = scaling::inputs(n, |m| {
        let mut rng = Rng::new(m as u64);
        let (a, b) = (u64s(&mut rng, m), u64s(&mut rng, m));
        let ks: Vec<Value> = (0..m).map(|_| Value::Int(rng.int(0, 63))).collect();
        (a, b, ks)
    });
    let w = Value::Int(64);
    scaling::check_order(
        "mulHi, bitReverse, byteSwap, pdep, pext, funnelShl, funnelShr over u64 values",
        n,
        1,
        |m| {
            let (a, b, ks) = &ops[&m];
            for ((a, b), k) in a.iter().zip(b).zip(ks) {
                run(Prim::MulHi, &[a.clone(), b.clone(), w.clone()]);
                run(Prim::BitReverse, &[a.clone(), w.clone()]);
                run(Prim::ByteSwap, &[a.clone(), w.clone()]);
                run(Prim::Pdep, &[a.clone(), b.clone()]);
                run(Prim::Pext, &[a.clone(), b.clone()]);
                let args = [a.clone(), b.clone(), k.clone(), w.clone()];
                run(Prim::FunnelShl, &args);
                run(Prim::FunnelShr, &args);
            }
        },
    );
}

#[test]
fn pdep_and_pext_are_linear_in_the_digits_of_the_mask() {
    let n = 1 << 22;
    let ops = scaling::inputs(n, |m| {
        let mut rng = Rng::new(m as u64);
        let digits = |rng: &mut Rng| {
            let words: Vec<u32> = (0..m.div_ceil(32)).map(|_| rng.next_u64() as u32).collect();
            Value::int(BigInt::from(BigUint::new(words)))
        };
        (digits(&mut rng), digits(&mut rng))
    });
    scaling::check_order("pdep and pext on a mask of n digits", n, 1, |m| {
        let (x, mask) = &ops[&m];
        for _ in 0..20 {
            run(Prim::Pdep, &[x.clone(), mask.clone()]);
            run(Prim::Pext, &[x.clone(), mask.clone()]);
        }
    });
}

#[test]
fn the_width_words_are_linear_in_the_width() {
    // `bitReverse` and `byteSwap` build the digits of `x`; the funnel shifts are products and
    // quotients by powers of two: each grows with the digits of the width. `mulHi` is left out:
    // at width n it multiplies two n-digit ints, which costs what `*` does on them.
    let n = 1 << 22;
    let ops = scaling::inputs(n, |m| {
        let mut rng = Rng::new(m as u64);
        let wide = |rng: &mut Rng| {
            let words: Vec<u32> = (0..m / 32).map(|_| rng.next_u64() as u32).collect();
            Value::int(BigInt::from(BigUint::new(words)))
        };
        let k = Value::Int(m as i64 / 3);
        (wide(&mut rng), wide(&mut rng), k, Value::Int(m as i64))
    });
    scaling::check_order(
        "bitReverse, byteSwap, funnelShl, funnelShr at width n",
        n,
        1,
        |m| {
            let (a, b, k, w) = &ops[&m];
            for _ in 0..20 {
                run(Prim::BitReverse, &[a.clone(), w.clone()]);
                run(Prim::ByteSwap, &[a.clone(), w.clone()]);
                let args = [a.clone(), b.clone(), k.clone(), w.clone()];
                run(Prim::FunnelShl, &args);
                run(Prim::FunnelShr, &args);
            }
        },
    );
}
