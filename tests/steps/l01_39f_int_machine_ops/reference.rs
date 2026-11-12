//! Each word against a reference written from its definition in DESIGN.md sec:linalg, digit by
//! digit or on `BigUint`: on every operand of up to 8 digits, and on random operands at every
//! width from 8 to 128, so the operands cross `i64` and the kernel's exact path runs as well as
//! its machine path. The words take non-negative operands only (the domain of the bit words),
//! so there is no signed form to test; a negative operand is a type error (errors.rs).

use num_bigint::{BigInt, BigUint};
use zed_kernel::{Prim, Value};
use zed_tests::instances::Rng;

/// The int `n` as a value.
fn v(n: u128) -> Value {
    Value::int(BigInt::from(n))
}

fn big(n: BigUint) -> Value {
    Value::int(BigInt::from(n))
}

fn run(p: Prim, args: &[Value]) -> Value {
    zed_kernel::bits::word(p, args).unwrap_or_else(|e| panic!("{p:?} {args:?}: {e}"))
}

/// The `w` low ones.
fn ones(w: u32) -> u128 {
    if w == 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    }
}

/// Digit `i` of `x`.
fn digit(x: u128, i: u32) -> u128 {
    (x >> i) & 1
}

/// `shr(a * b, w)`.
fn mul_hi(a: u128, b: u128, w: u32) -> BigUint {
    (BigUint::from(a) * BigUint::from(b)) >> w
}

/// Digit `i` of `x` placed at `w - 1 - i`, for each `i < w`.
fn bit_reverse(x: u128, w: u32) -> u128 {
    (0..w).map(|i| digit(x, i) << (w - 1 - i)).sum()
}

/// Byte `j` of `x` placed at `w / 8 - 1 - j`, for each `j < w / 8`.
fn byte_swap(x: u128, w: u32) -> u128 {
    let n = w / 8;
    (0..n)
        .map(|j| ((x >> (8 * j)) & 0xFF) << (8 * (n - 1 - j)))
        .sum()
}

/// The `j`-th low digit of `x` at the `j`-th lowest one digit of `mask`.
fn pdep(x: u128, mask: u128) -> u128 {
    let mut j = 0;
    let mut out = 0;
    for i in 0..128 {
        if digit(mask, i) == 1 {
            out |= digit(x, j) << i;
            j += 1;
        }
    }
    out
}

/// The digit of `x` at the `j`-th lowest one digit of `mask` at digit `j`.
fn pext(x: u128, mask: u128) -> u128 {
    let mut j = 0;
    let mut out = 0;
    for i in 0..128 {
        if digit(mask, i) == 1 {
            out |= digit(x, i) << j;
            j += 1;
        }
    }
    out
}

/// The high `w` digits of the `2w` digits `hi * 2^w + lo` shifted `k` places up, and the low
/// `w` digits of it shifted `k` places down.
fn funnel(hi: u128, lo: u128, k: u32, w: u32) -> (BigUint, BigUint) {
    let joined = (BigUint::from(hi) << w) + BigUint::from(lo);
    let all = (BigUint::from(1u8) << w) - 1u8;
    (((&joined << k) >> w) & &all, (joined >> k) & all)
}

/// Checks every word at width `w` on the operands `a`, `b`, the count `k < w` and the mask `m`.
fn check(w: u32, a: u128, b: u128, k: u32, m: u128) {
    let what = format!("w {w}, a {a}, b {b}, k {k}, m {m}");
    let wv = v(u128::from(w));
    assert_eq!(
        run(Prim::MulHi, &[v(a), v(b), wv.clone()]),
        big(mul_hi(a, b, w)),
        "mulHi {what}"
    );
    assert_eq!(
        run(Prim::BitReverse, &[v(a), wv.clone()]),
        v(bit_reverse(a, w)),
        "bitReverse {what}"
    );
    if w.is_multiple_of(8) {
        assert_eq!(
            run(Prim::ByteSwap, &[v(a), wv.clone()]),
            v(byte_swap(a, w)),
            "byteSwap {what}"
        );
    }
    assert_eq!(run(Prim::Pdep, &[v(a), v(m)]), v(pdep(a, m)), "pdep {what}");
    assert_eq!(run(Prim::Pext, &[v(a), v(m)]), v(pext(a, m)), "pext {what}");
    if w > 0 {
        check_funnel(w, a, b, k);
    }
}

/// Checks `funnelShl` and `funnelShr` at width `w > 0` on `hi`, `lo` and the count `k < w`.
fn check_funnel(w: u32, a: u128, b: u128, k: u32) {
    let what = format!("w {w}, hi {a}, lo {b}, k {k}");
    let (l, r) = funnel(a, b, k, w);
    let args = [v(a), v(b), v(u128::from(k)), v(u128::from(w))];
    assert_eq!(run(Prim::FunnelShl, &args), big(l), "funnelShl {what}");
    assert_eq!(run(Prim::FunnelShr, &args), big(r), "funnelShr {what}");
}

#[test]
fn every_operand_of_up_to_eight_digits() {
    for w in 0..=8u32 {
        for a in 0..=ones(w) {
            for b in 0..=ones(w) {
                check(w, a, b, 0, b);
                for k in 1..w {
                    check_funnel(w, a, b, k);
                }
            }
        }
    }
}

/// A random value of at most `w` binary digits, its length itself random, so small values
/// are as likely as wide ones.
fn below(rng: &mut Rng, w: u32) -> u128 {
    let len = 1 + rng.below(w as usize) as u32;
    let bits = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
    bits & ones(len)
}

#[test]
fn random_operands_at_every_width_from_8_to_128() {
    let mut rng = Rng::new(0x39f);
    for w in 8..=128u32 {
        for _ in 0..200 {
            let (a, b, m) = (below(&mut rng, w), below(&mut rng, w), below(&mut rng, w));
            let k = rng.below(w as usize) as u32;
            check(w, a, b, k, m);
        }
    }
}

#[test]
fn random_64_digit_operands() {
    let mut rng = Rng::new(0x64);
    for _ in 0..20_000 {
        let r = |rng: &mut Rng| u128::from(rng.next_u64());
        let (a, b, m) = (r(&mut rng), r(&mut rng), r(&mut rng));
        check(64, a, b, rng.below(64) as u32, m);
    }
}

#[test]
fn the_corners_at_every_width() {
    for w in 1..=128u32 {
        let top = 1u128 << (w - 1);
        let corners = [0, 1, top, ones(w), top | 1];
        for &a in &corners {
            for &b in &corners {
                for k in [0, 1.min(w - 1), w / 2, w - 1] {
                    // Masks of zero and of all ones, and the corners themselves.
                    for m in [0, ones(w), u128::MAX, b] {
                        check(w, a, b, k, m);
                    }
                }
            }
        }
    }
}

#[test]
fn pdep_and_pext_read_only_the_digits_the_mask_reaches() {
    // `pdep` drops the digits of `x` above `popCount(mask)`; `pext` those above the mask's top.
    let x = (BigUint::from(1u8) << 1000) + 0b1011u8;
    let xv = big(x);
    assert_eq!(
        run(Prim::Pdep, &[xv.clone(), v(0b1111_0000)]),
        v(0b1011_0000)
    );
    assert_eq!(run(Prim::Pext, &[xv.clone(), v(0b1010)]), v(0b11));
    // Masks of every width up to 300 digits, all ones: both words keep the masked digits of `x`.
    for d in [1u32, 63, 64, 65, 127, 128, 129, 300] {
        let all = (BigUint::from(1u8) << d) - 1u8;
        let low = (BigUint::from(1u8) << 1000usize) + 0b1011u8;
        let want = &low & &all;
        assert_eq!(
            run(Prim::Pdep, &[xv.clone(), big(all.clone())]),
            big(want.clone()),
            "{d}"
        );
        assert_eq!(run(Prim::Pext, &[xv.clone(), big(all)]), big(want), "{d}");
    }
}

/// Digit `i` of `x`, for a `BigUint`.
fn big_digit(x: &BigUint, i: u64) -> bool {
    x.bit(i)
}

/// `pdep` digit by digit on `BigUint`s.
fn big_pdep(x: &BigUint, mask: &BigUint) -> BigUint {
    let mut out = BigUint::from(0u8);
    let mut j = 0;
    for i in 0..mask.bits() {
        if big_digit(mask, i) {
            out.set_bit(i, big_digit(x, j));
            j += 1;
        }
    }
    out
}

/// `pext` digit by digit on `BigUint`s.
fn big_pext(x: &BigUint, mask: &BigUint) -> BigUint {
    let mut out = BigUint::from(0u8);
    let mut j = 0;
    for i in 0..mask.bits() {
        if big_digit(mask, i) {
            out.set_bit(j, big_digit(x, i));
            j += 1;
        }
    }
    out
}

/// A random `BigUint` of exactly `d` digits (0 for `d = 0`).
fn wide(rng: &mut Rng, d: u64) -> BigUint {
    let mut x = BigUint::from(0u8);
    for i in 0..d {
        x.set_bit(i, i + 1 == d || rng.next_u64() & 1 == 1);
    }
    x
}

#[test]
fn pdep_and_pext_agree_on_wide_and_kept_operands() {
    // Wide operands on either side of a 32-digit word and of each other: `x` shorter than the
    // digits the mask reads, as long, and longer, and masks of every density.
    let mut rng = Rng::new(0x9de9);
    let sizes = [0u64, 1, 31, 32, 33, 63, 64, 65, 200, 1000, 3001];
    for &dx in &sizes {
        for &dm in &sizes {
            let x = wide(&mut rng, dx);
            let dense = wide(&mut rng, dm);
            let sparse = &dense & wide(&mut rng, dm) & wide(&mut rng, dm);
            let all = (BigUint::from(1u8) << dm) - 1u8;
            for mask in [dense, sparse, all] {
                let what = format!("x of {dx} digits, mask of {dm} digits");
                let (xv, mv) = (big(x.clone()), big(mask.clone()));
                assert_eq!(
                    run(Prim::Pdep, &[xv.clone(), mv.clone()]),
                    big(big_pdep(&x, &mask)),
                    "pdep {what}"
                );
                assert_eq!(
                    run(Prim::Pext, &[xv, mv]),
                    big(big_pext(&x, &mask)),
                    "pext {what}"
                );
            }
        }
    }
    // An `x` kept as a power gives what its built digits give, and a huge one is never built.
    let three = zed_kernel::Rat::int(BigInt::from(3));
    let kept = three.pow(&BigUint::from(700u32)).expect("3^700");
    assert!(
        !kept.integer_factors().1.is_empty(),
        "3^700 is kept as a power"
    );
    let built = BigUint::from(3u8).pow(700);
    for dm in [5u64, 64, 1109, 1110, 2000] {
        let mask = wide(&mut rng, dm);
        let mv = big(mask.clone());
        let kv = Value::integer(kept.clone());
        assert_eq!(
            run(Prim::Pdep, &[kv.clone(), mv.clone()]),
            big(big_pdep(&built, &mask)),
            "pdep 3^700, mask of {dm} digits"
        );
        assert_eq!(
            run(Prim::Pext, &[kv, mv]),
            big(big_pext(&built, &mask)),
            "pext 3^700, mask of {dm} digits"
        );
    }
    let huge = zed_kernel::Rat::int(BigInt::from(2))
        .pow(&BigUint::from(10u32).pow(12))
        .expect("2^10^12 kept");
    let hv = Value::integer(huge);
    assert_eq!(run(Prim::Pdep, &[hv.clone(), v(0b1011)]), v(0));
    assert_eq!(run(Prim::Pext, &[hv, v(u128::MAX)]), v(0));
}
