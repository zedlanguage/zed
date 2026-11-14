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

#[test]
fn the_pext_transfer_is_linear_in_the_digits_of_the_mask_hull() {
    // The bound of `pext` on a mask in `lo ..= hi` counts the most one digits of the hull in one
    // pass over the words of both ends and the trailing ones of `hi` (`Num::most_ones_from`):
    // O(n) for n digits.
    use zedc::store::interval::{End, IntervalSet, Num, bit_word};
    let n = 1 << 22;
    // The longest pass: the ends share their high n/2 digits and differ at digit n/2, below
    // which `hi` is all ones, so both the pass from the highest word and the trailing ones of
    // `hi` read every word.
    let ops = scaling::inputs(n, |m| {
        let mut rng = Rng::new(m as u64);
        let words: Vec<u32> = (0..m / 64).map(|_| rng.next_u64() as u32).collect();
        let half = BigInt::from(1u32) << (m / 2);
        let hi =
            ((BigInt::from(BigUint::new(words)) | BigInt::from(1u32)) << (m / 2)) | (&half - 1);
        let lo = &hi - &half;
        let mask = IntervalSet::range(End::Fin(Num::from(&lo)), End::Fin(Num::from(&hi)));
        (IntervalSet::range(End::of(0), End::PosInf), mask)
    });
    scaling::check_order("the pext transfer on a mask hull of n digits", n, 1, |m| {
        let (x, mask) = &ops[&m];
        for _ in 0..2000 {
            bit_word(Prim::Pext, &[x.clone(), mask.clone()]);
        }
    });
}

#[test]
fn a_curried_word_is_checked_in_time_linear_in_its_calls() {
    // Each call of a function a bit word curried with `...` gives checks the word's domains
    // once, with the operands kept by the curried call's span: one hash lookup and the check of
    // a direct call, O(1) for the fixed operands, so O(n) for n curried words, each called once.
    let n = 300;
    let srcs = scaling::inputs(n, |m| {
        let body: String = (0..m)
            .map(|i| {
                format!(
                    "r{i} = bitReverse({}, ...);\nx{i} = r{i}(width: 8);\n",
                    i % 256
                )
            })
            .collect();
        format!("{body}main(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n")
    });
    scaling::check("n bit words curried with `...`, each called once", n, |m| {
        assert!(zedc::run::load(srcs[&m].as_bytes()).is_ok());
    });
}
