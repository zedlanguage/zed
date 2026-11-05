//! Item RAT-checked: `Rat::mul` and `Rat::div` ask the system for their memory before they
//! build anything, so a product or quotient of wide numbers is refused with an error naming
//! its operator and size where it used to abort the process. Each refusal is checked in a
//! child under a lowered limit at two widths, n and 8n; the same products and quotients are
//! exact when their memory is given; and the work of a product by a small factor is O(n).

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use zed_kernel::term::build::lit;
use zed_kernel::{KernelError, Prim, Rat, Term, Value, eval};
use zed_tests::kernel::bin;
use zed_tests::scaling::check_order;

use super::memory_check::{in_child_at, lower_limit, lower_limit_by};

fn in_child(name: &str) -> bool {
    in_child_at(module_path!(), name)
}

/// `2^s + 1`, built.
fn above(s: u64) -> BigInt {
    (BigInt::one() << s) + 1u32
}

fn int(n: impl Into<BigInt>) -> Term {
    lit(Value::int(n.into()))
}

/// `n / d` as a rational value.
fn ratio(n: BigInt, d: u32) -> Term {
    lit(Value::rat(
        Rat::new(n, BigInt::from(d)).expect("d is not zero"),
    ))
}

/// `2^s` kept as a power of 2, not built.
fn two_to(s: u32) -> Rat {
    Rat::int(BigInt::from(2))
        .pow(&BigUint::from(s))
        .expect("a power of 2 is kept")
}

/// The operator and size of the error `eval(t)` gives, which must be
/// [`KernelError::NumberTooLarge`]; anything else is told without printing a number's digits,
/// whose text would itself abort the child.
fn refused(t: &Term) -> (&'static str, BigUint) {
    match eval(t) {
        Err(KernelError::NumberTooLarge { op, bits }) => (op, bits),
        Ok(v) => panic!("answered a value of type {}", v.kind_type()),
        Err(e) => panic!("another error: {e:?}"),
    }
}

/// The products and quotients of `2^s + 1` refused below their asks, with the operator and the
/// size each error names: `*` of two integers asks eight times the product's width, `*` and
/// `/` of rationals and of kept powers, and `shl`, which multiplies by a kept power of 2, ask
/// sixteen times the sum of the four coefficients' widths (the Complexity tradeoffs in
/// `Rat::mul` and `Rat::scaled`).
fn cases(s: u64) -> Vec<(Term, &'static str, BigUint)> {
    let wide = int(above(s));
    let kept = lit(Value::integer(two_to(64)));
    vec![
        // Coefficients of `s + 1` bits each.
        (
            bin(Prim::Mul, wide.clone(), wide.clone()),
            "*",
            BigUint::from(2 * (s + 1)) << 3u32,
        ),
        // `(2^s + 1)/3` (`2^s + 1` is 2 modulo 3 for an even `s`) times `1/3`: `s + 1`, 2, 1
        // and 2 bits.
        (
            bin(Prim::Mul, ratio(above(s), 3), ratio(BigInt::one(), 3)),
            "*",
            BigUint::from(s + 6) << 4u32,
        ),
        // `2^s + 1` times `2^64` kept, a `Big` (a power in the 64-bit range is an `Int`): `s + 1`,
        // 1, 1 and 1 bits.
        (
            bin(Prim::Mul, wide.clone(), kept),
            "*",
            BigUint::from(s + 4) << 4u32,
        ),
        // `(2^s + 1) / 3`: `s + 1`, 1, 1 and 2 bits.
        (
            bin(Prim::Div, ratio(above(s), 1), ratio(BigInt::from(3), 1)),
            "/",
            BigUint::from(s + 5) << 4u32,
        ),
        // `(2^s + 1) shl 5` is `(2^s + 1) * 2^5`, the power kept.
        (
            bin(Prim::Shl, wide, int(5)),
            "shl",
            BigUint::from(s + 4) << 4u32,
        ),
    ]
}

/// Each product and quotient of [`cases`] at widths of `2^27` and `2^30` bits, 16 and 128 MiB,
/// under a limit 64 MiB above what the child holds: each asks for more than that and is
/// refused, at both widths, where an unchecked product built its operands' width again and
/// aborted the child.
#[test]
fn a_product_or_quotient_of_wide_numbers_is_refused_when_memory_is_short() {
    if !in_child("a_product_or_quotient_of_wide_numbers_is_refused_when_memory_is_short") {
        return;
    }
    let all: Vec<_> = [1u64 << 27, 1 << 30]
        .into_iter()
        .flat_map(|s| cases(s).into_iter().map(move |c| (s, c)))
        .collect();
    lower_limit();
    for (s, (t, op, bits)) in &all {
        assert_eq!(refused(t), (*op, bits.clone()), "{op} at 2^{}", s.ilog2());
    }
}

/// The products and quotients of [`cases`] at `2^26` bits, under a limit of the largest ask,
/// sixteen times the widest sum of widths, and 64 MiB more: each is answered, and exact.
#[test]
fn a_product_or_quotient_of_wide_numbers_is_exact_when_its_ask_is_given() {
    if !in_child("a_product_or_quotient_of_wide_numbers_is_exact_when_its_ask_is_given") {
        return;
    }
    let s = 1u64 << 26;
    let all = cases(s);
    let square = (BigInt::one() << (2 * s)) + (BigInt::one() << (s + 1)) + 1u32;
    let want = [
        Rat::int(square),
        Rat::new(above(s), BigInt::from(9)).expect("9 is not zero"),
        Rat::int(above(s))
            .mul(&two_to(64))
            .expect("built before the limit"),
        Rat::new(above(s), BigInt::from(3)).expect("3 is not zero"),
        Rat::int(above(s))
            .mul(&two_to(5))
            .expect("built before the limit"),
    ];
    let ask = all.iter().map(|(_, _, b)| b).max().expect("five cases");
    let bytes = u64::try_from(ask >> 3u32).expect("the ask fits a u64");
    lower_limit_by(bytes + (64 << 20));
    for ((t, op, _), want) in all.iter().zip(&want) {
        let got = match eval(t) {
            Ok(Value::Big(n) | Value::Rat(n)) => n,
            Ok(v) => panic!("{op}: a value of type {}", v.kind_type()),
            Err(e) => panic!("{op}: {e:?}"),
        };
        assert!(*got == *want, "{op}");
    }
}

/// `(2^n + 1) * 3`, `(2^n + 1)/3 * 1/3` and `(2^n + 1) / 3` at n and 8n bits: a product or
/// quotient by a word asks for its memory and builds the result in O(n), the gcd of the
/// rationals by one division by the word.
#[test]
fn a_product_or_quotient_by_a_word_costs_order_n() {
    let n = 1usize << 20;
    let inputs: Vec<(usize, Rat, Rat)> = [n, 8 * n]
        .into_iter()
        .map(|m| {
            let a = above(m as u64);
            let third = Rat::new(a.clone(), BigInt::from(3)).expect("3 is not zero");
            (m, Rat::int(a), third)
        })
        .collect();
    let three = Rat::int(BigInt::from(3));
    let a_third = Rat::new(BigInt::one(), BigInt::from(3)).expect("3 is not zero");
    check_order(
        "(2^n + 1) * 3, (2^n + 1)/3 * 1/3 and (2^n + 1) / 3",
        n,
        1,
        |m| {
            let (_, wide, third) = inputs
                .iter()
                .find(|(k, _, _)| *k == m)
                .expect("each size was built");
            assert!(!wide.mul(&three).expect("memory is given").is_zero());
            assert!(!third.mul(&a_third).expect("memory is given").is_zero());
            let q = wide.div(&three).expect("memory is given");
            assert!(q.is_some_and(|q| !q.is_zero()));
        },
    );
}
