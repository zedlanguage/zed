//! Step L1.17a: arithmetic on a wide integer reads its operands where they are held. `a - b`
//! reads `b` with its sign flipped and builds only the difference; `a mod m` reads `a` from
//! the top with no copy of it, so `wide mod 3` answers under a limit that refuses any copy of
//! `wide`; `a div m` asks the system for the quotient before building it. A type error names
//! the operand's type, `int`, not its digits, so it never builds the operand's text.
//!
//! The memory tests run in a child process under a lowered address-space limit, set up as in
//! the sibling module `memory_check`.

use num_bigint::{BigInt, BigUint};
use num_traits::{Euclid, One, Zero};
use zed_kernel::term::build::{lit, prim};
use zed_kernel::{KernelError, Prim, Rat, Term, Value, eval};
use zed_tests::kernel::{bin, sub};
use zed_tests::scaling::check_order;

use super::memory_check::{WIDE, in_child_at, lower_limit};

fn in_child(name: &str) -> bool {
    in_child_at(module_path!(), name)
}

/// `2^s + 1`, built.
fn above(s: u64) -> BigInt {
    (BigInt::one() << s) + 1u32
}

fn int(n: impl Into<BigInt>) -> Rat {
    Rat::int(n.into())
}

fn num(n: impl Into<BigInt>) -> Term {
    lit(Value::int(n.into()))
}

/// `2^s` kept as a power of 2, not built.
fn two_to(s: u64) -> Rat {
    int(2).pow(&BigUint::from(s)).expect("a power of 2 is kept")
}

/// The error of `t`, which must be [`KernelError::NumberTooLarge`] of `op`, and its size.
fn too_large(t: &Term, op: &str) -> BigUint {
    match eval(t) {
        Err(KernelError::NumberTooLarge { op: o, bits }) if o == op => bits,
        other => panic!("{op}: {other:?}"),
    }
}

/// A balance of `2^30` bits less a fee, a fee less the balance, and the balance plus one:
/// each result is as wide as the balance, which the system can no longer hold a second copy
/// of, so each is refused before it is built.
#[test]
fn a_sum_or_difference_as_wide_as_its_operand_is_refused_when_memory_is_short() {
    if !in_child("a_sum_or_difference_as_wide_as_its_operand_is_refused_when_memory_is_short") {
        return;
    }
    let balance = || num(above(WIDE));
    let refused = BigUint::from(WIDE + 2);
    let cases = [
        (sub(num(1), balance()), "-"),
        (sub(balance(), num(1)), "-"),
        (bin(Prim::Add, balance(), num(1)), "+"),
        (bin(Prim::Add, num(-1), balance()), "+"),
    ];
    lower_limit();
    for (t, op) in &cases {
        assert_eq!(too_large(t, op), refused, "{op}");
    }
}

/// Two shares of a wide amount split in thirds, `(2^n + 1) / 3` less `1 / 3`: the difference of
/// two plain rationals asks for its cross products and their reduction before building them.
#[test]
fn a_wide_rational_difference_is_refused_when_memory_is_short() {
    if !in_child("a_wide_rational_difference_is_refused_when_memory_is_short") {
        return;
    }
    let third = |n: BigInt| lit(Value::rat(Rat::new(n, BigInt::from(3)).unwrap()));
    let t = sub(third(above(WIDE)), third(BigInt::one()));
    lower_limit();
    // Eight times the unreduced width: a numerator of `(n + 1) + 2 + 1` bits, the sum of
    // two cross products, over a denominator of `2 + 2`.
    assert_eq!(too_large(&t, "-"), BigUint::from(WIDE + 8) << 3u32);
}

/// Splitting a wide amount three ways, `wide div 3`, builds a quotient as wide as the amount;
/// it is asked for first and refused. A divisor wider than a word asks for four times the
/// dividend, the peak of num-bigint's long division.
#[test]
fn dividing_a_wide_number_is_refused_when_memory_is_short() {
    if !in_child("dividing_a_wide_number_is_refused_when_memory_is_short") {
        return;
    }
    let wide = || num(above(WIDE));
    let kept = lit(Value::integer(Rat::int(above(WIDE)).mul(&two_to(5))));
    let by_word = bin(Prim::IntDiv, wide(), num(3));
    let by_two_words = bin(Prim::IntDiv, wide(), num(above(64)));
    let kept_by_word = bin(Prim::IntDiv, kept, num(3));
    lower_limit();
    assert_eq!(too_large(&by_word, "div"), BigUint::from(WIDE + 1));
    assert_eq!(
        too_large(&by_two_words, "div"),
        BigUint::from(WIDE + 1) << 2u32
    );
    // `(2^n + 1) 2^5 div 3` is not exact: it builds the remainder and the difference.
    too_large(&kept_by_word, "div");
}

/// The day of the week, the check digit and the residues of a wide number, `wide mod m`, read
/// it where it is held: each answers under a limit that refuses any copy of it, for a divisor
/// of one word, of two, of three, negative, and for a negative or kept-power dividend.
#[test]
fn a_wide_number_modulo_a_small_one_answers_when_memory_is_short() {
    if !in_child("a_wide_number_modulo_a_small_one_answers_when_memory_is_short") {
        return;
    }
    let wide = || num(above(WIDE));
    let minus_wide = num(-above(WIDE));
    let kept = lit(Value::integer(Rat::int(above(WIDE)).mul(&two_to(5))));
    let mersenne = (1u64 << 61) - 1;
    // `2^3 = 1 (mod 7)`, `2^61 = 1 (mod 2^61 - 1)` and `2^64 = -1 (mod 2^64 + 1)`, and `n` is a multiple of 128.
    let cases = [
        (bin(Prim::Mod, wide(), num(3)), BigInt::from(2)),
        (bin(Prim::Mod, wide(), num(-3)), BigInt::from(2)),
        (bin(Prim::Mod, minus_wide, num(3)), BigInt::from(1)),
        (bin(Prim::Mod, wide(), num(7)), BigInt::from(3)),
        (
            bin(Prim::Mod, wide(), num(mersenne)),
            BigInt::from((1u64 << (WIDE % 61)) + 1),
        ),
        (bin(Prim::Mod, wide(), num(above(64))), BigInt::from(2)),
        (bin(Prim::Mod, wide(), num(above(128))), BigInt::from(2)),
        (bin(Prim::Mod, kept.clone(), num(3)), BigInt::from(1)),
        (bin(Prim::Mod, kept, num(above(64))), BigInt::from(64)),
    ];
    lower_limit();
    for (i, (t, want)) in cases.iter().enumerate() {
        assert_eq!(eval(t).unwrap(), Value::int(want.clone()), "case {i}");
    }
}

/// Comparing a wide amount with a price written as a rational, `wide < 0.5`, or negating it
/// with `not`, or giving it as a bit word's operand out of its domain, is a type error that
/// names the type, never the digits, so the message is built under a limit that refuses them.
#[test]
fn a_type_error_on_a_wide_number_names_its_type_when_memory_is_short() {
    if !in_child("a_type_error_on_a_wide_number_names_its_type_when_memory_is_short") {
        return;
    }
    let wide = || num(above(WIDE));
    let half = lit(Value::rat(
        Rat::new(BigInt::from(1), BigInt::from(2)).unwrap(),
    ));
    let cases = [
        (bin(Prim::Lt, wide(), half), "Lt applied to `int`, `rat`"),
        (prim(Prim::Not, vec![wide()]), "Not applied to `int`"),
        (
            prim(Prim::BitNot, vec![num(-above(WIDE)), num(8)]),
            "`bitNot` needs `x` in int[0..], and it is negative",
        ),
        (
            prim(Prim::BitNot, vec![wide(), num(8)]),
            "`bitNot` needs `x` in int[0..<2 ** width], and it is at least 2 ** width",
        ),
    ];
    lower_limit();
    for (t, want) in &cases {
        match eval(t) {
            Err(KernelError::Type(m)) => assert_eq!(m, *want),
            other => panic!("{want}: {other:?}"),
        }
    }
}

/// Each value kind's type as a type error prints it, in the syntax a program writes.
#[test]
fn a_type_error_names_each_kind_of_operand_by_its_written_type() {
    use zed_kernel::Family;
    let wide = Value::int(above(100));
    let cases = [
        (Value::Bool(true), "bool"),
        (Value::Int(3), "int"),
        (wide, "int"),
        (Value::float(0.5), "f64"),
        (Value::str("x"), "String"),
        (Value::atom("none"), "#none"),
        (Value::atom_with("some", vec![Value::Int(1)]), "#some(..)"),
        (Value::tuple(vec![Value::Int(1), Value::Int(2)]), "(..)"),
        (Value::path(vec![Value::Int(1)]), "(..)"),
        (Value::Family(Family::of([(1, 2)])), "_ ->? _"),
    ];
    for (v, want) in cases {
        assert_eq!(v.kind_type(), want);
        let t = prim(Prim::Not, vec![lit(v.clone())]);
        if !matches!(v, Value::Bool(_) | Value::Atom(_)) {
            let Err(KernelError::Type(m)) = eval(&t) else {
                panic!("{want}")
            };
            assert_eq!(m, format!("Not applied to `{want}`"));
        }
    }
}

/// Small and mid-sized integers of both signs, against num-bigint's Euclidean division and
/// its sums: each sign, a divisor of one word, of two and of more, and a dividend smaller than
/// the divisor.
fn integers() -> Vec<BigInt> {
    let mut out = Vec::new();
    for k in [0u64, 1, 3, 31, 32, 61, 63, 64, 65, 127, 128, 129, 200, 4096] {
        for c in [0i32, 1, 3] {
            let x = (BigInt::one() << k) + c;
            out.push(x.clone());
            out.push(-x);
        }
    }
    out.push(BigInt::from(i64::MAX));
    out.push(BigInt::from(i64::MIN));
    out
}

#[test]
fn sums_differences_quotients_and_remainders_agree_with_num_bigint() {
    let xs = integers();
    for a in &xs {
        for b in &xs {
            let (ra, rb) = (int(a.clone()), int(b.clone()));
            assert_eq!(ra.sub(&rb).unwrap(), int(a - b), "{a} - {b}");
            assert_eq!(ra.add(&rb).unwrap(), int(a + b), "{a} + {b}");
            let (va, vb) = (num(a.clone()), num(b.clone()));
            assert_eq!(
                eval(&sub(va.clone(), vb.clone())).unwrap(),
                Value::int(a - b),
                "{a} - {b}"
            );
            if b.is_zero() {
                continue;
            }
            let (q, r) = (Euclid::div_euclid(a, b), Euclid::rem_euclid(a, b));
            assert_eq!(ra.div_euclid(&rb).unwrap(), int(q.clone()), "{a} div {b}");
            assert_eq!(ra.rem_euclid(&rb).unwrap(), int(r.clone()), "{a} mod {b}");
            assert_eq!(
                eval(&bin(Prim::IntDiv, va.clone(), vb.clone())).unwrap(),
                Value::int(q),
                "{a} div {b}"
            );
            assert_eq!(
                eval(&bin(Prim::Mod, va, vb)).unwrap(),
                Value::int(r),
                "{a} mod {b}"
            );
        }
    }
}

/// A dividend holding a kept power, `a * 2^k`, against the same value built, by divisors that
/// divide it, that do not, and that are larger than it.
#[test]
fn kept_power_quotients_and_remainders_agree_with_the_built_value() {
    let divisors = [3i64, -3, 7, 64, -64, 96, (1 << 61) - 1, i64::MAX];
    for a in [above(70), -above(70), above(3), BigInt::from(5)] {
        for k in [1u64, 5, 64, 100] {
            let kept = int(a.clone()).mul(&two_to(k));
            let built: BigInt = &a << k;
            for m in divisors.iter().map(|m| BigInt::from(*m)).chain([
                above(64),
                above(200),
                -above(200),
            ]) {
                let rm = int(m.clone());
                assert_eq!(
                    kept.rem_euclid(&rm).unwrap(),
                    int(Euclid::rem_euclid(&built, &m)),
                    "{a} 2^{k} mod {m}"
                );
                assert_eq!(
                    kept.div_euclid(&rm).unwrap(),
                    int(Euclid::div_euclid(&built, &m)),
                    "{a} 2^{k} div {m}"
                );
                assert_eq!(kept.sub(&rm).unwrap(), int(&built - &m), "{a} 2^{k} - {m}");
                assert_eq!(rm.sub(&kept).unwrap(), int(&m - &built), "{m} - {a} 2^{k}");
            }
        }
    }
    // Zero divided by a kept power is zero, and divides exactly.
    let zero = int(0);
    assert_eq!(zero.rem_euclid(&two_to(80)).unwrap(), zero);
    assert_eq!(zero.div_euclid(&two_to(80)).unwrap(), zero);
    assert_eq!(zero.sub(&two_to(80)).unwrap(), two_to(80).neg());
}

/// Differences of plain rationals with wide and small denominators, against the cross
/// product built by hand.
#[test]
fn rational_differences_agree_with_the_cross_product() {
    let parts = [
        BigInt::from(1),
        BigInt::from(-3),
        BigInt::from(7),
        above(70),
        -above(130),
    ];
    for (a, b) in parts.iter().zip(parts.iter().cycle().skip(1)) {
        for (c, d) in parts.iter().zip(parts.iter().cycle().skip(2)) {
            let x = Rat::new(a.clone(), b.clone()).unwrap();
            let y = Rat::new(c.clone(), d.clone()).unwrap();
            let want = Rat::new(a * d - c * b, b * d).unwrap();
            assert_eq!(x.sub(&y).unwrap(), want, "{a}/{b} - {c}/{d}");
        }
    }
    // The common factor 3 of the denominators is divided out of the difference.
    let (x, y) = (int(1).div(&int(6)).unwrap(), int(1).div(&int(3)).unwrap());
    assert_eq!(
        x.sub(&y).unwrap(),
        Rat::new(BigInt::from(-1), BigInt::from(6)).unwrap()
    );
}

/// `wide mod 3`, `wide mod (2^128 + 1)`, `1 - wide` and `wide div 3` at `n` and `8n` bits: one
/// pass over the digits each, O(n), with the operands built before timing.
#[test]
fn wide_differences_quotients_and_remainders_cost_order_n() {
    let n = 1 << 18;
    let inputs: Vec<(usize, Term, Term, Term, Term)> = [n, 8 * n]
        .into_iter()
        .map(|m| {
            let w = || num(above(m as u64));
            (
                m,
                bin(Prim::Mod, w(), num(3)),
                bin(Prim::Mod, w(), num(above(128))),
                sub(num(1), w()),
                bin(Prim::IntDiv, w(), num(3)),
            )
        })
        .collect();
    let at = |m: usize| {
        inputs
            .iter()
            .find(|(k, ..)| *k == m)
            .expect("each size was built")
    };
    check_order("2^n + 1 mod 3", n, 1, |m| {
        assert_eq!(eval(&at(m).1).unwrap(), Value::Int(2));
    });
    check_order("2^n + 1 mod 2^128 + 1", n, 1, |m| {
        assert!(matches!(eval(&at(m).2).unwrap(), Value::Int(_)));
    });
    check_order("1 - (2^n + 1)", n, 1, |m| {
        assert!(matches!(eval(&at(m).3).unwrap(), Value::Big(_)));
    });
    check_order("2^n + 1 div 3", n, 1, |m| {
        assert!(matches!(eval(&at(m).4).unwrap(), Value::Big(_)));
    });
}
