//! Item K30-rest (COMPLEXITY.md S33, S36): the canonical serialization writes an interval end
//! or a class past `i64` by its sign and 64-bit limbs, not by its decimal text, so writing one
//! is linear in its bits. A kept value (a power held unexpanded) is written out only once the
//! system gives the memory (`Num::built`): when the memory is short, the address is refused
//! with the memory asked named, where the writing used to build the value and its decimal
//! digits unasked and stop the compiler when the system refused.

use std::collections::HashMap;

use num_bigint::{BigInt, Sign};
use zed_kernel::num::bytes_of;
use zed_kernel::term::build::var;
use zed_tests::scaling::check_order;
use zed_tests::step_helpers::l01_17_value_representation::{in_child_at, lower_limit_by};
use zedc::canon::{Def, Domain, address};
use zedc::store::interval::{IntervalSet, Num};
use zedc::store::lattice::{Congruence, FiniteSet, Lattice};

fn in_child(name: &str) -> bool {
    in_child_at(module_path!(), name)
}

/// `2^k`, kept as a power past `i128`.
fn two(k: u32) -> Num {
    Num::from(2).pow(k)
}

/// `2^k` written out, the same value in the other form.
fn two_big(k: u32) -> Num {
    Num::from(BigInt::from(2).pow(k))
}

/// A definition whose domain is the one value `v`.
fn at(v: Num) -> Def {
    with(IntervalSet::point(v), Congruence::top())
}

/// A definition whose domain is the class `r mod m`.
fn class(m: Num, r: Num) -> Def {
    with(IntervalSet::top(), Congruence::new(m, r))
}

fn with(ints: IntervalSet, class: Congruence) -> Def {
    Def {
        name: "slot".into(),
        domain: Some(Domain {
            ints,
            class,
            finite: FiniteSet::Top,
        }),
        facets: vec![],
        body: var("i"),
    }
}

fn addr(d: &Def) -> zedc::address::ContentAddress {
    address(d, &|_| None).expect("memory for the address")
}

#[test]
fn an_end_past_the_64_bit_range_has_one_address_in_either_form() {
    for k in [64, 127, 128, 200, 4096] {
        assert_eq!(addr(&at(two(k))), addr(&at(two_big(k))), "2^{k}");
        assert_eq!(addr(&at(-&two(k))), addr(&at(-&two_big(k))), "-2^{k}");
        assert_ne!(addr(&at(two(k))), addr(&at(-&two(k))), "the sign of 2^{k}");
        assert_ne!(
            addr(&at(two(k))),
            addr(&at(&two(k) + &Num::ONE)),
            "2^{k} and 2^{k} + 1"
        );
    }
    // Ends at the edges of `i64`, one a word and one limbs, differ.
    let max = Num::from(i64::MAX);
    assert_ne!(addr(&at(max.clone())), addr(&at(&max + &Num::ONE)));
    let min = Num::from(i64::MIN);
    assert_ne!(addr(&at(min.clone())), addr(&at(&min - &Num::ONE)));
}

#[test]
fn a_class_past_the_64_bit_range_has_one_address_in_either_form() {
    for k in [64, 200, 4096] {
        let r = Num::from(5);
        assert_eq!(
            addr(&class(two(k), r.clone())),
            addr(&class(two_big(k), r.clone())),
            "5 mod 2^{k}"
        );
        assert_ne!(
            addr(&class(two(k), r.clone())),
            addr(&class(two(k), Num::from(6))),
            "5 and 6 mod 2^{k}"
        );
        // A residue past `i64` too, in both forms.
        let m = two(k + 1);
        assert_eq!(
            addr(&class(m.clone(), two(k))),
            addr(&class(m, two_big(k))),
            "2^{k} mod 2^{}",
            k + 1
        );
    }
}

/// Addresses the end `2^k`, kept, with four times its bytes more than the child holds. Writing
/// it out asks a byte for each bit of the widest number built, more than that, so the address
/// is refused with the memory asked named. Before, the value was built unasked and its decimal
/// text written, which aborted the child or ran past the test's time.
fn refused_with(k: u32) {
    let d = at(two(k));
    lower_limit_by(4 * u64::from(k / 8));
    let e = address(&d, &|_| None).expect_err("refused under the limit");
    assert!(
        bytes_of(&e.bits) >= k.into(),
        "2^{k}: {} bits named",
        e.bits
    );
}

#[test]
fn a_kept_end_of_4_mib_is_refused_when_memory_is_short() {
    if in_child("a_kept_end_of_4_mib_is_refused_when_memory_is_short") {
        refused_with(1 << 25);
    }
}

#[test]
fn a_kept_end_of_32_mib_is_refused_when_memory_is_short() {
    if in_child("a_kept_end_of_32_mib_is_refused_when_memory_is_short") {
        refused_with(1 << 28);
    }
}

/// With the memory asked, the bytes already written and 64 MiB more, the kept ends are
/// addressed, each as its written-out form is. A point's value is written three times (its
/// two ends and its class, a modulus of 0 and the value as residue), and each ask comes while
/// the bytes of the ends before it are held.
#[test]
fn a_kept_end_is_addressed_when_memory_is_given() {
    if !in_child("a_kept_end_is_addressed_when_memory_is_given") {
        return;
    }
    let ks = [1u32 << 25, 1 << 28];
    let want: Vec<_> = ks.iter().map(|&k| addr(&at(two_big(k)))).collect();
    // The ask for `2^k` is about `2k` bytes (a bound of two bits for each factor 2); the
    // bytes written before the last ask are two ends of `k / 8` bytes and the capacity the
    // writing doubled to, at most `k / 2` bytes.
    let k = u64::from(ks[1]);
    lower_limit_by(2 * k + k / 2 + (64 << 20));
    for (k, w) in ks.iter().zip(want) {
        let a = address(&at(two(*k)), &|_| None).unwrap_or_else(|e| panic!("2^{k}: {e:?}"));
        assert_eq!(a, w, "2^{k}");
    }
}

/// A number of `bytes` bytes, each odd, from a fixed linear congruential generator.
fn wide(bytes: usize) -> Num {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let digits: Vec<u8> = (0..bytes)
        .map(|_| {
            x = x
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (x >> 56) as u8 | 1
        })
        .collect();
    Num::from(BigInt::from_bytes_le(Sign::Plus, &digits))
}

/// Addressing a definition whose end and class hold a number past `i64` is linear in the
/// number's bits; its decimal text took more than linear time. The decimal text cost about
/// `n^1.5`, 22.6 times the work at 8n: over the limit of 13, though under the 24 allowed until
/// SCALE-ratio, when a second test held it at 64 times the bits (removed by
/// TESTS-scaling-limit-13).
#[test]
fn addressing_a_wide_end_and_class_scales() {
    let (n, sizes) = (128usize << 10, [128usize << 10, 1 << 20]);
    let inputs: HashMap<usize, (Def, Def)> = sizes
        .into_iter()
        .map(|b| {
            let v = wide(b);
            (b, (at(v.clone()), class(&v + &v, v)))
        })
        .collect();
    check_order(
        "addressing a wide end and a wide class, by the bytes of the number",
        n,
        1,
        |b| {
            let (end, class) = &inputs[&b];
            addr(end);
            addr(class);
        },
    );
}
