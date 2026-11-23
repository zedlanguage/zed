//! The tests of DESIGN step L1.17b (sec:domains, "Kept powers"; plan row KEPT-power-form) that
//! the kernel's exact numbers answer: equality by exponents with equal hashes, order with no
//! build, the corner cases of the paragraph and the `f64` corner cases. Each allocation bound is
//! measured on this thread with `zed_alloc_count::live`.

use num_bigint::BigInt;
use zed_kernel::Rat;
use zed_kernel::num::LiteralRounding;

fn int(n: i64) -> Rat {
    Rat::int(BigInt::from(n))
}

/// `b ^ e` for an `e` of one word.
fn pow(b: i64, e: u64) -> Rat {
    int(b).pow(&e.into()).expect("a kept power is not built")
}

/// `b ^ e` for an `e` of either sign, as Zed's `^` on a `rat` takes it.
fn pow_int(b: &Rat, e: &Rat) -> Option<Rat> {
    b.pow_int(e).expect("a kept power is not built")
}

const K: u64 = 1 << 40;

#[test]
fn equal_products_of_powers_are_equal_and_hash_alike() {
    let (six, two_three) = zed_alloc_count::live(|| {
        let six = pow(6, K);
        let two_three = pow(2, K).mul(&pow(3, K)).expect("kept");
        (six, two_three)
    })
    .0;
    assert!(six == two_three);
    assert_eq!(six.residues(), two_three.residues());
    let b = int(2).pow(&64u32.into()).unwrap().add(&int(13)).unwrap();
    let square = b.pow(&2u32.into()).unwrap();
    let product = b.mul(&b).unwrap();
    assert!(square == product);
    assert_eq!(square.residues(), product.residues());
}

#[test]
fn powers_far_apart_order_with_no_build() {
    let ((lt, gt), live) = zed_alloc_count::live(|| {
        let (a, b) = (pow(3, K), pow(2, 2 * K));
        (a < b, b > a)
    });
    assert!(lt && gt);
    assert!(live.peak < 1 << 20, "peak heap {} bytes", live.peak);
    // `x < 3 ^ (2 ^ 40)` for `x` of 64 bits.
    let x = int(i64::MAX);
    let (lt, live) = zed_alloc_count::live(|| x < pow(3, K));
    assert!(lt);
    assert!(live.peak < 1 << 20, "peak heap {} bytes", live.peak);
}

#[test]
fn corner_cases_of_the_kept_power_paragraph() {
    // `0 ^ 0` is 1, as an int and as a rat.
    assert!(pow(0, 0) == int(1));
    assert!(pow_int(&int(0), &int(0)).expect("0^0 is defined") == int(1));
    // A negative base by the parity of its exponent, with no build.
    let (signs, live) = zed_alloc_count::live(|| {
        let even = pow(-3, K);
        let odd = pow(-3, K + 1);
        (
            even.is_negative(),
            odd.is_negative(),
            even > int(0),
            odd < int(0),
        )
    });
    assert_eq!(signs, (false, true, true, true));
    assert!(live.peak < 1 << 20, "peak heap {} bytes", live.peak);
    // `2r ^ -(2 ^ 40)`, kept: below 1 and above 0.
    let tiny = pow_int(&int(2), &int(-(K as i64))).expect("2 is not zero");
    assert!(tiny > int(0) && tiny < int(1));
    assert!(tiny == int(1).div(&pow(2, K)).unwrap().expect("not zero"));
    // `0r ^ -1` has no value: Zed's `#divByZero`.
    assert!(pow_int(&int(0), &int(-1)).is_none());
}

#[test]
fn floats_of_kept_powers_round_once() {
    // `2^1024 - 2^970` is the tie above the largest `f64`: it rounds to even, an infinity.
    let top = pow(2, 1024).sub(&pow(2, 970)).unwrap();
    assert_eq!(top.to_f64(), Err(LiteralRounding::Infinite));
    // One below it rounds down to the largest finite `f64`.
    assert_eq!(top.sub(&int(1)).unwrap().to_f64(), Ok(f64::MAX));
    // `2^-1075`, half the least subnormal, a tie, rounds to the even zero.
    let half = pow_int(&int(2), &int(-1075)).unwrap();
    assert_eq!(half.to_f64(), Err(LiteralRounding::Zero));
    // A little above that half rounds up to the least subnormal.
    let above = half.add(&pow_int(&int(2), &int(-1200)).unwrap()).unwrap();
    assert_eq!(above.to_f64(), Ok(f64::from_bits(1)));
}
