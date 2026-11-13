//! An exact number past `i64` is addressed by its sign and the 64-bit limbs of its numerator
//! and denominator in lowest terms, not by its decimal digits, which cost more than linear time
//! to convert: the ZIR address and the kernel address of a constant of n bits take time linear
//! in n. A negative number and its absolute value have different addresses, two forms of one
//! value have the same address, and the binary form reads back to the graph it was written from.

use num_bigint::{BigInt, BigUint, Sign};
use zed_kernel::term::build::lit;
use zed_kernel::{Rat, Term, Value};
use zed_tests::scaling::check_order;
use zedc::address::ContentAddress;
use zedc::canon::{self, Def};
use zedc::zir::canon::address;
use zedc::zir::lower::lower;
use zedc::zir::{Region, binary};

/// A number of `bits` bits whose bytes come from a fixed linear congruential generator, so
/// every run and every machine builds the same one.
fn wide(bits: usize, sign: Sign) -> BigInt {
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
fn two_to(bits: usize) -> Rat {
    Rat::int(BigInt::from(2))
        .pow(&BigUint::from(bits))
        .expect("a power of 2 that fits")
}

/// The graph that writes `v` to standard output.
fn graph(v: Value) -> Region {
    lower(&Term::Push("stdout".into(), Term::Lit(v).into())).expect("a graph")
}

/// The kernel address of the definition `wide = v`.
fn kernel_address(v: Value) -> ContentAddress {
    let none = |_: &str| None;
    canon::address(&def(v), &none).expect("memory for the address")
}

/// The definition `wide = v`, with no domain and no facets.
fn def(v: Value) -> Def {
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
fn a_power_kept_and_the_same_number_written_out_have_one_address() {
    for bits in [64, 100, 4096] {
        let kept = Value::integer(two_to(bits));
        let written = Value::int(BigInt::from(1) << bits);
        assert_eq!(
            address(&graph(kept.clone())).expect("memory for the address"),
            address(&graph(written.clone())).expect("memory for the address")
        );
        assert_eq!(kernel_address(kept), kernel_address(written));
    }
    let kept = Rat::int(BigInt::from(3))
        .div(&two_to(90))
        .expect("fits")
        .expect("a nonzero divisor");
    let written = Rat::new(BigInt::from(3), BigInt::from(1) << 90).expect("a nonzero denominator");
    assert_eq!(
        address(&graph(Value::rat(kept.clone()))).expect("memory for the address"),
        address(&graph(Value::rat(written.clone()))).expect("memory for the address")
    );
    assert_eq!(
        kernel_address(Value::rat(kept)),
        kernel_address(Value::rat(written))
    );
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

/// The decimal digits cost about `n^1.5` here, 22.3 times the work at 8n: over the limit of 13,
/// though under the 24 allowed until SCALE-ratio, when a second test held it at 64 times the
/// bits (removed by TESTS-scaling-limit-13).
#[test]
fn addressing_a_wide_constant_is_linear_in_its_bits() {
    const N: usize = 1 << 17;
    let terms = |sign| {
        [
            graph(Value::int(wide(N, sign))),
            graph(Value::int(wide(8 * N, sign))),
        ]
    };
    let (random, negative) = (terms(Sign::Plus), terms(Sign::Minus));
    let powers = [
        graph(Value::integer(two_to(N))),
        graph(Value::integer(two_to(8 * N))),
    ];
    fn pick(gs: &[Region; 2], k: usize) -> &Region {
        &gs[usize::from(k != N)]
    }
    check_order("the ZIR address of a random number of n bits", N, 1, |k| {
        address(pick(&random, k)).expect("memory for the address");
    });
    check_order(
        "the ZIR address of a negative number of n bits",
        N,
        1,
        |k| {
            address(pick(&negative, k)).expect("memory for the address");
        },
    );
    check_order("the ZIR address of 2^n kept as a power", N, 1, |k| {
        address(pick(&powers, k)).expect("memory for the address");
    });
    let defs = [
        def(Value::int(wide(N, Sign::Plus))),
        def(Value::int(wide(8 * N, Sign::Plus))),
    ];
    let none = |_: &str| None;
    check_order(
        "the kernel address of a random number of n bits",
        N,
        1,
        |k| {
            canon::address(&defs[usize::from(k != N)], &none).expect("memory for the address");
        },
    );
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
