//! An exact number past `i64` is addressed by its sign and the 64-bit limbs of its numerator
//! and denominator in lowest terms, not by its decimal digits, which cost more than linear time
//! to convert: the ZIR address and the kernel address of a constant of n bits take time linear
//! in n. A negative number and its absolute value have different addresses, and the binary form reads
//! back to the graph it was written from. A number kept with prime powers, as `2^2^100`, is
//! written as its powers, in time linear in their size (item ENGINE-one), so its address differs
//! from that of the same number written out.

use num_bigint::{BigInt, BigUint, Sign};
use zed_kernel::term::build::lit;
use zed_kernel::{Rat, Term, Value};
use zedc::address::ContentAddress;
use zedc::canon::{self, Def};
use zedc::zir::canon::address;
use zedc::zir::lower::lower;
use zedc::zir::{Region, binary};

/// A number of `bits` bits whose bytes come from a fixed linear congruential generator, so
/// every run and every machine builds the same one.
pub(super) fn wide(bits: usize, sign: Sign) -> BigInt {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let bytes: Vec<u8> = (0..bits / 8)
        .map(|_| {
            x = x
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (x >> 56) as u8 | 1
        })
        .collect();
    BigInt::from_bytes_le(sign, &bytes)
}

/// `2^bits`, kept as a power of 2.
pub(super) fn two_to(bits: usize) -> Rat {
    Rat::int(BigInt::from(2))
        .pow(&BigUint::from(bits))
        .expect("a power of 2 that fits")
}

/// The graph that writes `v` to standard output.
pub(super) fn graph(v: Value) -> Region {
    lower(&Term::Push("stdout".into(), Term::Lit(v).into())).expect("a graph")
}

/// The kernel address of the definition `wide = v`.
fn kernel_address(v: Value) -> ContentAddress {
    let none = |_: &str| None;
    canon::address(&def(v), &none).expect("memory for the address")
}

/// The definition `wide = v`, with no domain and no facets.
pub(super) fn def(v: Value) -> Def {
    Def {
        name: "wide".into(),
        domain: None,
        facets: vec![],
        body: lit(v),
    }
}

#[test]
fn a_wide_number_and_its_negation_have_different_addresses() {
    for bits in [64, 72, 128, 4096] {
        let (pos, neg) = (wide(bits, Sign::Plus), wide(bits, Sign::Minus));
        assert_ne!(
            address(&graph(Value::int(pos.clone()))).expect("memory for the address"),
            address(&graph(Value::int(neg.clone()))).expect("memory for the address"),
            "ZIR, {bits} bits"
        );
        assert_ne!(
            kernel_address(Value::int(pos)),
            kernel_address(Value::int(neg)),
            "kernel, {bits} bits"
        );
    }
    let (half, minus_half) = (
        Rat::new(
            BigInt::from(1),
            two_to(80).to_integer().expect("an integer"),
        )
        .expect("a rat"),
        Rat::new(
            BigInt::from(-1),
            two_to(80).to_integer().expect("an integer"),
        )
        .expect("a rat"),
    );
    assert_ne!(
        address(&graph(Value::rat(half.clone()))).expect("memory for the address"),
        address(&graph(Value::rat(minus_half.clone()))).expect("memory for the address")
    );
    assert_ne!(
        kernel_address(Value::rat(half)),
        kernel_address(Value::rat(minus_half))
    );
}

#[test]
fn numerator_and_denominator_are_not_confused() {
    let big = two_to(70).to_integer().expect("an integer");
    let three = BigInt::from(3);
    let (a, b) = (
        Rat::new(three.clone(), big.clone()).expect("a rat"),
        Rat::new(big, three).expect("a rat"),
    );
    assert_ne!(
        address(&graph(Value::rat(a.clone()))).expect("memory for the address"),
        address(&graph(Value::rat(b.clone()))).expect("memory for the address")
    );
    assert_ne!(kernel_address(Value::rat(a)), kernel_address(Value::rat(b)));
}

#[test]
fn a_number_is_addressed_by_the_form_it_is_kept_in() {
    // A number kept with prime powers is written as its powers, so `2^bits` kept as a power
    // and the same number written out have different addresses (item ENGINE-one); the
    // address is that of the expression, which no machine need write out in full. Two routes
    // to the same kept form have one address.
    for bits in [64, 100, 4096] {
        let kept = Value::integer(two_to(bits));
        let squared = Value::integer(two_to(bits / 2).mul(&two_to(bits / 2)).expect("fits"));
        let written = Value::int(BigInt::from(1) << bits);
        let zir = |v: &Value| address(&graph(v.clone())).expect("memory for the address");
        assert_eq!(zir(&kept), zir(&squared), "{bits} bits");
        assert_ne!(zir(&kept), zir(&written), "{bits} bits");
        assert_eq!(kernel_address(kept.clone()), kernel_address(squared));
        assert_ne!(kernel_address(kept), kernel_address(written));
    }
    // A number written out keeps the address of its numerator and denominator.
    let three = BigInt::from(3);
    let (a, b) = (
        Rat::new(three.clone(), BigInt::from(1) << 90).expect("a nonzero denominator"),
        Rat::new(three, (BigInt::from(1) << 89) * 2).expect("a nonzero denominator"),
    );
    assert_eq!(
        address(&graph(Value::rat(a.clone()))).expect("memory for the address"),
        address(&graph(Value::rat(b.clone()))).expect("memory for the address")
    );
    assert_eq!(kernel_address(Value::rat(a)), kernel_address(Value::rat(b)));
}

/// `2^2^100`, `-2^2^100`, `3^2^80 / 7^2^90` and `1e10^20`: numbers no machine can write out.
fn unwritable() -> Vec<Value> {
    let e = |k: u32| BigUint::from(1u32) << k;
    let two = Rat::int(BigInt::from(2))
        .pow(&e(100))
        .expect("a power kept");
    let frac = Rat::int(BigInt::from(3))
        .pow(&e(80))
        .expect("a power kept")
        .div(&Rat::int(BigInt::from(7)).pow(&e(90)).expect("a power kept"))
        .expect("a power kept")
        .expect("a nonzero divisor");
    let ten = Rat::int(BigInt::from(10))
        .pow(&BigUint::from(10u32).pow(20u32))
        .expect("a power kept");
    vec![
        Value::integer(two.clone()),
        Value::integer(two.neg()),
        Value::rat(frac.clone()),
        Value::rat(frac.neg()),
        Value::integer(ten),
    ]
}

#[test]
fn a_kept_power_is_written_as_its_powers() {
    let values = unwritable();
    let mut zir = Vec::new();
    let mut kernel = Vec::new();
    for v in &values {
        let g = graph(v.clone());
        let bytes = binary::encode(&g).expect("the powers, not the digits");
        assert!(bytes.len() < 1000, "{} bytes", bytes.len());
        let back = binary::decode(&bytes).expect("a graph");
        assert_eq!(back, g);
        assert_eq!(binary::encode(&back).expect("the powers"), bytes);
        zir.push(address(&g).expect("the powers, not the digits"));
        kernel.push(kernel_address(v.clone()));
    }
    // Distinct numbers, a number and its negation included, have distinct addresses.
    for (i, j) in (0..values.len()).flat_map(|i| (i + 1..values.len()).map(move |j| (i, j))) {
        assert_ne!(zir[i], zir[j], "{i} {j}");
        assert_ne!(kernel[i], kernel[j], "{i} {j}");
    }
}

/// The binary form of `2^2^100` with the byte at `at` replaced by `by`, or `None` when `at`
/// is past its end.
fn changed(at: usize, by: u8) -> Option<Vec<u8>> {
    let mut bytes = binary::encode(&graph(unwritable().remove(0))).expect("the powers");
    *bytes.get_mut(at)? = by;
    Some(bytes)
}

#[test]
fn a_kept_power_out_of_its_form_is_an_error() {
    // Every cut of the bytes is an error, and no change of one byte reads back to a number
    // out of the form it is kept in: each either fails or reads back to a graph that writes
    // back to the same bytes.
    let bytes = binary::encode(&graph(unwritable().remove(0))).expect("the powers");
    for cut in 1..bytes.len() {
        assert!(
            binary::decode(&bytes[..bytes.len() - cut]).is_err(),
            "cut {cut}"
        );
    }
    for at in 0..bytes.len() {
        for by in [0, 1, 2, 3, 4, 0x7f, 0xff] {
            let b = changed(at, by).expect("inside");
            if let Ok(g) = binary::decode(&b) {
                assert_eq!(
                    binary::encode(&g).expect("the powers"),
                    b,
                    "byte {at} as {by}"
                );
            }
        }
    }
}

#[test]
fn the_binary_form_of_a_wide_number_reads_back() {
    let values = [
        Value::int(wide(64, Sign::Plus)),
        Value::int(wide(4096, Sign::Minus)),
        Value::integer(two_to(1000).neg()),
        Value::rat(Rat::new(wide(200, Sign::Minus), wide(136, Sign::Plus)).expect("a rat")),
    ];
    for v in values {
        let g = graph(v);
        let back =
            binary::decode(&binary::encode(&g).expect("memory for the bytes")).expect("a graph");
        assert_eq!(back, g);
        assert_eq!(
            binary::encode(&back).expect("memory for the bytes"),
            binary::encode(&g).expect("memory for the bytes")
        );
    }
}

#[test]
fn a_cut_count_of_limbs_is_an_error() {
    let bytes =
        binary::encode(&graph(Value::int(wide(256, Sign::Plus)))).expect("memory for the bytes");
    for cut in 1..=16 {
        assert!(
            binary::decode(&bytes[..bytes.len() - cut]).is_err(),
            "cut {cut}"
        );
    }
}

/// The size item CONST-wide-addr was written for: a constant of 2^30 bits, whose decimal digits
/// took about 80 minutes to address (test audit 2026-11-08: the tests above stop at 2^20 bits).
/// Its ZIR and kernel addresses, those of its negation and of `2^(2^30)` kept as a power, and
/// the binary form read back.
#[test]
fn a_constant_of_two_to_the_thirty_bits_is_addressed() {
    const N: usize = 1 << 30;
    let start = std::time::Instant::now();
    let pos = wide(N, Sign::Plus);
    let neg = -&pos;
    let g = graph(Value::int(pos.clone()));
    let built = start.elapsed();
    let a = address(&g).expect("memory for the address");
    assert_ne!(
        a,
        address(&graph(Value::int(neg.clone()))).expect("memory for the address")
    );
    assert_ne!(
        a,
        address(&graph(Value::integer(two_to(N)))).expect("memory for the address")
    );
    assert_ne!(
        kernel_address(Value::int(pos)),
        kernel_address(Value::int(neg))
    );
    let bytes = binary::encode(&g).expect("memory for the bytes");
    assert_eq!(binary::decode(&bytes).expect("a graph"), g);
    eprintln!(
        "a constant of 2^30 bits: built in {built:?}, addressed and read back in {:?}",
        start.elapsed() - built
    );
}

/// The first `n` primes.
pub(super) fn primes(n: usize) -> Vec<u64> {
    (2..)
        .filter(|&p| zed_kernel::num::is_prime(p))
        .take(n)
        .collect()
}

/// The product of `primes`, each to the power 2^100, kept as its powers.
pub(super) fn kept_product(primes: &[u64]) -> Value {
    let e = BigUint::from(1u32) << 100;
    Value::integer(primes.iter().fold(Rat::int(BigInt::from(1)), |r, &p| {
        r.mul(&Rat::int(BigInt::from(p)).pow(&e).expect("a power kept"))
            .expect("kept")
    }))
}

/// A product of a few kept powers is addressed in the ZIR and the kernel and written in binary;
/// the time of each is held linear in the number of powers in `bench/wide_constants.rs`.
#[test]
fn a_product_of_a_few_kept_powers_is_addressed_and_written() {
    let ps = primes(9);
    let none = |_: &str| None;
    for n in [1, 2, 9] {
        let v = kept_product(&ps[..n]);
        let g = graph(v.clone());
        address(&g).expect("the powers");
        let bytes = binary::encode(&g).expect("the powers");
        assert_eq!(binary::decode(&bytes).expect("a graph"), g);
        canon::address(&def(v), &none).expect("the powers");
    }
}

/// Random and negative numbers of a few bits, and `2^n` kept as a power, are addressed in the ZIR
/// and the kernel; the time is held linear in the bits in `bench/wide_constants.rs`.
#[test]
fn a_few_numbers_of_a_few_bits_are_addressed() {
    for bits in [8, 64, 1024] {
        for sign in [Sign::Plus, Sign::Minus] {
            address(&graph(Value::int(wide(bits, sign)))).expect("memory for the address");
            kernel_address(Value::int(wide(bits, sign)));
        }
        address(&graph(Value::integer(two_to(bits)))).expect("memory for the address");
    }
}
