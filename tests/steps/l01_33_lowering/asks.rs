//! Item K30-rest: the lowering orders the nodes of one key by their regions' numbers among
//! the regions it has finished (`zir::canon::Regions`), not by writing their constants again,
//! so the order asks no memory. Two equal lambdas that hold a wide constant are one node when
//! memory is given, and refused with an error naming the memory asked when it is short, where
//! the comparison used to write the constant of each again, two at once, and stop the compiler
//! when the system refused.

use std::collections::HashMap;

use num_bigint::{BigInt, Sign};
use zed_kernel::term::build::{lam, var};
use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling::check_order;
use zed_tests::step_helpers::l01_17_value_representation::{in_child_at, lower_limit_by};
use zedc::zir::lower::lower;

use super::count;

fn in_child(name: &str) -> bool {
    in_child_at(module_path!(), name)
}

/// A number of `bytes` bytes, each odd, from a fixed linear congruential generator.
fn wide(bytes: usize) -> BigInt {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let digits: Vec<u8> = (0..bytes)
        .map(|_| {
            x = x
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (x >> 56) as u8 | 1
        })
        .collect();
    BigInt::from_bytes_le(Sign::Plus, &digits)
}

/// `((m) -> m + c, (m) -> m + c)`, the two lambdas built apart and the constant shared.
fn two_lambdas(c: &Value) -> Term {
    let one = || {
        lam(
            &["m"],
            Term::Prim(Prim::Add, vec![var("m"), Term::Lit(c.clone())]),
        )
    };
    Term::Prim(Prim::Tuple, vec![one(), one()])
}

/// The bytes a refusal of the lowering names.
fn refused_bytes(e: &str) -> u64 {
    let Some((_, rest)) = e.split_once("one of its constants takes ") else {
        panic!("another error: {e}");
    };
    rest.split(' ')
        .next()
        .and_then(|b| b.parse().ok())
        .unwrap_or_else(|| panic!("no byte count in: {e}"))
}

/// Lowers two equal lambdas of a constant of `bytes` bytes with four times the constant's bytes
/// more than the child holds once the constant is built. Writing the constant for a key takes
/// up to three times its bytes for a moment (its bytes written, and their capacity doubled by
/// the write after them), and the lowering holds what it wrote for the first lambda, so the
/// second is refused with the memory asked named. Before, the second was lowered, and the
/// comparison of the two lambdas wrote both constants again at once and aborted the child.
fn refused_with(bytes: usize) {
    let t = two_lambdas(&Value::int(wide(bytes)));
    lower_limit_by(4 * bytes as u64);
    let e = lower(&t).expect_err("refused under the limit");
    let named = refused_bytes(&e);
    assert!(
        named >= bytes as u64 && named <= 2 * bytes as u64 + 256,
        "{bytes} bytes: {e}"
    );
}

#[test]
fn equal_lambdas_of_a_4_mib_constant_are_refused_when_memory_is_short() {
    if in_child("equal_lambdas_of_a_4_mib_constant_are_refused_when_memory_is_short") {
        refused_with(4 << 20);
    }
}

#[test]
fn equal_lambdas_of_a_32_mib_constant_are_refused_when_memory_is_short() {
    if in_child("equal_lambdas_of_a_32_mib_constant_are_refused_when_memory_is_short") {
        refused_with(32 << 20);
    }
}

/// With six times the wider constant and 64 MiB more, both pairs of lambdas are lowered, each
/// pair to one node.
#[test]
fn equal_lambdas_of_a_wide_constant_are_one_when_memory_is_given() {
    if !in_child("equal_lambdas_of_a_wide_constant_are_one_when_memory_is_given") {
        return;
    }
    let all = [4usize << 20, 32 << 20].map(|b| (b, two_lambdas(&Value::int(wide(b)))));
    lower_limit_by(6 * (32 << 20) + (64 << 20));
    for (bytes, t) in &all {
        let g = lower(t).unwrap_or_else(|e| panic!("{bytes} bytes: {e}"));
        assert_eq!(count(&g, "lambda"), 1, "{bytes} bytes");
    }
}

/// Lowering two equal lambdas is linear in the bits of the constant they hold: the second is
/// found by its key and confirmed by the bytes of its own node and its region's number.
#[test]
fn lowering_equal_lambdas_of_a_wide_constant_scales() {
    let (n, sizes) = (1usize << 20, [1usize << 20, 8 << 20]);
    let inputs: HashMap<usize, Term> = sizes
        .into_iter()
        .map(|b| (b, two_lambdas(&Value::int(wide(b)))))
        .collect();
    check_order(
        "lowering two equal lambdas of a wide constant, by its bytes",
        n,
        1,
        |b| {
            let g = lower(&inputs[&b]).expect("memory is given");
            assert_eq!(count(&g, "lambda"), 1);
        },
    );
}
