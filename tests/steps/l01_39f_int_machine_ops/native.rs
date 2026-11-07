//! The interpreter and native code agree on every word: each term is run by the kernel and by
//! the code Cranelift generates, and the values are compared. Until step L24.2a selects
//! instructions, each word lowers to its definition, which the runtime computes in the kernel.

use num_bigint::BigInt;
use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Prim, Term, Value};

use zed_tests::step_helpers::l01_36_cranelift::{kernel, native};

fn agree(t: &Term) -> Value {
    let k = kernel(t).unwrap_or_else(|e| panic!("{t}: {e}"));
    let n = native(t).unwrap_or_else(|e| panic!("{t}: {e}"));
    assert_eq!(n.value, k, "{t}");
    k
}

fn call(p: Prim, args: &[u128]) -> Term {
    prim(
        p,
        args.iter()
            .map(|&a| lit(Value::int(BigInt::from(a))))
            .collect(),
    )
}

#[test]
fn every_word_agrees_on_machine_and_wide_operands() {
    let m = u128::from(u64::MAX);
    for (p, args, want) in [
        (Prim::MulHi, vec![1 << 63, 4, 64], 2),
        (Prim::MulHi, vec![m, m, 64], m - 1),
        (Prim::BitReverse, vec![1, 8], 128),
        (Prim::BitReverse, vec![1, 128], 1 << 127),
        (Prim::ByteSwap, vec![0x0102, 16], 0x0201),
        (Prim::ByteSwap, vec![m, 64], m),
        (Prim::Pdep, vec![0b101, 0b11010], 0b10010),
        (Prim::Pdep, vec![m, 1 << 100], 1 << 100),
        (Prim::Pext, vec![0b10010, 0b11010], 0b101),
        (Prim::Pext, vec![1 << 100, 1 << 100], 1),
        (Prim::FunnelShl, vec![1, 0, 0, 8], 1),
        (Prim::FunnelShl, vec![0, 1 << 63, 1, 64], 1),
        (Prim::FunnelShr, vec![1, 0, 1, 64], 1 << 63),
    ] {
        let t = call(p, &args);
        assert_eq!(agree(&t), Value::int(BigInt::from(want)), "{t}");
    }
}

#[test]
fn outside_the_domain_both_fail() {
    for (p, args) in [
        (Prim::ByteSwap, vec![1, 12]),
        (Prim::FunnelShl, vec![1, 2, 8, 8]),
        (Prim::MulHi, vec![256, 1, 8]),
    ] {
        let t = call(p, &args);
        assert!(kernel(&t).is_err(), "{t}");
        assert!(native(&t).is_err(), "{t}");
    }
}
