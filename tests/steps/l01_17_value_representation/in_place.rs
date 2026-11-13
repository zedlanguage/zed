//! Step L1.17a: arithmetic on a wide integer reads its operands where they are held. `a - b`
//! reads `b` with its sign flipped and builds only the difference; `a mod m` reads `a` from
//! the top with no copy of it, so `wide mod 3` answers under a limit that refuses any copy of
//! `wide`; `a div m` asks the system for the quotient before building it. A type error names
//! the operand's type, `int`, not its digits, so it never builds the operand's text.
//!
//! The memory tests run in a child process under a lowered address-space limit, set up as in
//! the sibling module `memory_check`.

use std::sync::Arc;

use num_bigint::{BigInt, BigUint};
use num_traits::{Euclid, One, Zero};
use zed_kernel::term::build::{lit, prim};
use zed_kernel::{KernelError, Prim, Rat, Term, Value, eval};
use zed_tests::kernel::{bin, sub};
use zed_tests::scaling::check_order;

use super::memory_check::{WIDE, in_child_at, lower_limit, lower_limit_by};

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

/// What `eval` gave, told without printing a number's digits: under the lowered limit the
/// decimal text of a wide result would itself abort the process.
fn outcome(r: &Result<Value, KernelError>) -> String {
    match r {
        Ok(Value::Int(i)) => format!("Ok(Int({i}))"),
        Ok(Value::Big(n) | Value::Rat(n)) => {
            let (coef, pows) = n.integer_factors();
            format!(
                "Ok(a number of {} bits and {} kept primes)",
                coef.bits(),
                pows.len()
            )
        }
        Ok(v) => format!("Ok(a value of type {})", v.kind_type()),
        Err(KernelError::NumberTooLarge { op, need }) => {
            format!("Err(NumberTooLarge {{ op: {op}, ask: {} }})", need.ask)
        }
        Err(KernelError::Type(m)) => format!("Err(Type({m}))"),
        Err(_) => "Err(another error)".into(),
    }
}

/// The error of `t`, which must be [`KernelError::NumberTooLarge`] of `op`, and the memory it asked.
fn too_large(t: &Term, op: &str) -> BigUint {
    match eval(t) {
        Err(KernelError::NumberTooLarge { op: o, need }) if o == op => need.ask,
        other => panic!("{op}: {}", outcome(&other)),
    }
}

/// The integer `eval(t)` gives, held as a plain coefficient.
fn integer(t: &Term) -> Arc<Rat> {
    match eval(t) {
        Ok(Value::Big(n)) => n,
        other => panic!("{}", outcome(&other)),
    }
}

/// `b^e mod m`, for `m` below 2^63.
fn pow_mod(b: u64, e: u64, m: u64) -> u64 {
    let (mut b, mut e, mut r) = (u128::from(b % m), e, 1u128);
    let m = u128::from(m);
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % m;
        }
        b = b * b % m;
        e >>= 1;
    }
    u64::try_from(r).expect("below m")
}

/// The Mersenne prime 2^61 - 1, a modulus by which a wide number is checked without a copy.
const MERSENNE: u64 = (1 << 61) - 1;

/// `(2^n + 1 - r) / (2^k + 1) mod 2^61 - 1`, the residue of the quotient of `2^n + 1` by
/// `2^k + 1` that leaves `r`, from the residues of its parts.
fn quotient_residue(n: u64, k: u64, r: u64) -> u64 {
    let m = MERSENNE;
    let a = (pow_mod(2, n, m) + 1 + m - r % m) % m;
    let d = (pow_mod(2, k, m) + 1) % m;
    u64::try_from(u128::from(a) * u128::from(pow_mod(d, m - 2, m)) % u128::from(m))
        .expect("below m")
}

/// The residue of `q` modulo 2^61 - 1, read by [`Rat::rem_euclid`] one word at a time.
fn residue(q: &Rat) -> u64 {
    let r = q.rem_euclid(&int(MERSENNE)).expect("a one-word remainder");
    let (coef, _) = r.integer_factors();
    u64::try_from(coef).expect("below 2^61")
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
    // Sixteen times the unreduced width: a numerator of `(n + 1) + 2 + 1` bits, the sum of
    // two cross products, over a denominator of `2 + 2`.
    assert_eq!(too_large(&t, "-"), BigUint::from(WIDE + 8) << 4u32);
}

/// Splitting a wide amount three ways, `wide div 3`, builds a quotient as wide as the amount;
/// it is asked for first and refused. A divisor wider than a word asks for sixteen times the
/// dividend, a measured bound on the peak of num-bigint's division.
#[test]
fn dividing_a_wide_number_is_refused_when_memory_is_short() {
    if !in_child("dividing_a_wide_number_is_refused_when_memory_is_short") {
        return;
    }
    let wide = || num(above(WIDE));
    let kept = lit(Value::integer(
        Rat::int(above(WIDE)).mul(&two_to(5)).unwrap(),
    ));
    let by_word = bin(Prim::IntDiv, wide(), num(3));
    let by_two_words = bin(Prim::IntDiv, wide(), num(above(64)));
    let kept_by_word = bin(Prim::IntDiv, kept, num(3));
    lower_limit();
    assert_eq!(too_large(&by_word, "div"), BigUint::from(WIDE + 1));
    assert_eq!(
        too_large(&by_two_words, "div"),
        BigUint::from(WIDE + 1) << 4u32
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
    let kept = lit(Value::integer(
        Rat::int(above(WIDE)).mul(&two_to(5)).unwrap(),
    ));
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
        let got = eval(t);
        assert!(
            matches!(&got, Ok(v) if *v == Value::int(want.clone())),
            "case {i}: {}",
            outcome(&got)
        );
    }
}

/// A wide amount split by a wide divisor, `wide div (2^4096 + 1)` and `wide div (2^(2^29) +
/// 1)`, and the remainder `wide mod (2^(2^29) + 1)`, under a margin of 600 MiB: num-bigint's
/// division of them needs more than that, up to 15 times the dividend's width (the quotient)
/// and 21 times the divisor's (the remainder), so each asks for sixteen and 24 times, and is
/// refused. Asking for four and eight times, as before, let each start and abort.
#[test]
fn a_division_by_a_wide_divisor_is_refused_below_its_measured_peak() {
    if !in_child("a_division_by_a_wide_divisor_is_refused_below_its_measured_peak") {
        return;
    }
    let wide = || num(above(WIDE));
    let half = 1u64 << 29;
    let by_4097_bits = bin(Prim::IntDiv, wide(), num(above(4096)));
    let by_half = bin(Prim::IntDiv, wide(), num(above(half)));
    let mod_half = bin(Prim::Mod, wide(), num(above(half)));
    lower_limit_by(600 << 20);
    let quotient = BigUint::from(WIDE + 1) << 4u32;
    assert_eq!(too_large(&by_4097_bits, "div"), quotient);
    assert_eq!(too_large(&by_half, "div"), quotient);
    assert_eq!(too_large(&mod_half, "mod"), BigUint::from(half + 1) * 24u32);
}

/// The quotients of `a_division_by_a_wide_divisor_is_refused_below_its_measured_peak`, and one
/// of a negative amount, each in its own process with the sixteen times the dividend's width
/// that it asks for given, and 64 MiB more: each is computed. Each has its own process because
/// the allocator does not give back all the address space a division leaves, so a second
/// division in the same process can be refused. `2^n + 1` is `2` more than a multiple of
/// `2^k + 1` when `n / k` is even, so `(2^n + 1) div (2^(n/2) + 1)` is `2^(n/2) - 1`, `n/2`
/// ones; each quotient's residue modulo 2^61 - 1 is checked against its parts'.
#[test]
fn dividing_by_a_wide_divisor_answers_when_its_peak_is_given() {
    if !in_child("dividing_by_a_wide_divisor_answers_when_its_peak_is_given") {
        return;
    }
    let t = bin(Prim::IntDiv, num(above(WIDE)), num(above(4096)));
    // Sixteen times the dividend's width is twice its bits as bytes.
    lower_limit_by(2 * (WIDE + 1) + (64 << 20));
    let q = integer(&t);
    assert_eq!(q.integer_factors().0.bits(), WIDE - 4096);
    assert_eq!(residue(&q), quotient_residue(WIDE, 4096, 2));
}

/// `-(2^n + 1) = -(q + 1) (2^k + 1) + (2^k - 1)`, under the limit of
/// `dividing_by_a_wide_divisor_answers_when_its_peak_is_given`.
#[test]
fn dividing_a_negative_amount_by_a_wide_divisor_answers_when_its_peak_is_given() {
    if !in_child("dividing_a_negative_amount_by_a_wide_divisor_answers_when_its_peak_is_given") {
        return;
    }
    let t = bin(Prim::IntDiv, num(-above(WIDE)), num(above(4096)));
    lower_limit_by(2 * (WIDE + 1) + (64 << 20));
    let q = integer(&t);
    assert!(q.is_negative());
    let want = (MERSENNE - quotient_residue(WIDE, 4096, 2) + MERSENNE - 1) % MERSENNE;
    assert_eq!(residue(&q), want);
}

/// `(2^n + 1) div (2^(n/2) + 1)`, `n/2` ones, under the limit of
/// `dividing_by_a_wide_divisor_answers_when_its_peak_is_given`.
#[test]
fn dividing_by_half_the_width_answers_when_its_peak_is_given() {
    if !in_child("dividing_by_half_the_width_answers_when_its_peak_is_given") {
        return;
    }
    let half = 1u64 << 29;
    let t = bin(Prim::IntDiv, num(above(WIDE)), num(above(half)));
    lower_limit_by(2 * (WIDE + 1) + (64 << 20));
    let q = integer(&t);
    let (coef, _) = q.integer_factors();
    assert_eq!((coef.bits(), coef.magnitude().count_ones()), (half, half));
    assert_eq!(residue(&q), quotient_residue(WIDE, half, 2));
}

/// `wide mod (2^(2^29) + 1)`, of the amount and of its negative, with the 24 times the
/// divisor's width that a step of the remainder asks for given, and 64 MiB more: `2^(2^30) =
/// 1` modulo `2^(2^29) + 1`, so the remainders are `2` and `2^(2^29) - 1`.
#[test]
fn a_wide_number_modulo_a_wide_one_answers_when_its_peak_is_given() {
    if !in_child("a_wide_number_modulo_a_wide_one_answers_when_its_peak_is_given") {
        return;
    }
    let half = 1u64 << 29;
    let t = bin(Prim::Mod, num(above(WIDE)), num(above(half)));
    let negative = bin(Prim::Mod, num(-above(WIDE)), num(above(half)));
    // 24 times the divisor's width is three times its bytes.
    lower_limit_by(3 * (half + 1) + (64 << 20));
    let got = eval(&t);
    assert!(matches!(&got, Ok(Value::Int(2))), "{}", outcome(&got));
    let r = integer(&negative);
    let (coef, _) = r.integer_factors();
    assert_eq!((coef.bits(), coef.magnitude().count_ones()), (half, half));
}

/// A dense divisor `d = (2^(64 w) - 1) / 3`, every word nonzero, of `w = 2^18 + 1` words, just
/// above a power of two, where its transforms take the most points for its width, `2^20`:
/// `a mod d` and `a div d` for a dense `a = (2^(64 (3 w + 5)) - 1) / 7` ask 16 words a point,
/// 128 MiB, and the quotient twice the dividend's width more, a measured bound above their
/// peaks of 12.5 and 12.75 words a point (`num::POINT_WORDS`). Each answers with what it asks
/// for given and 64 MiB more, checked by `q d + r = a` and `r < d` modulo 2^61 - 1, and each
/// is refused, naming its ask, with half the remainder's ask given.
#[test]
fn a_dense_divisor_asks_for_its_transforms() {
    if !in_child("a_dense_divisor_asks_for_its_transforms") {
        return;
    }
    let w = (1u64 << 18) + 1;
    let d = ((BigInt::one() << (64 * w)) - 1u32) / 3u32;
    let a = ((BigInt::one() << (64 * (3 * w + 5))) - 1u32) / 7u32;
    let modulo = bin(Prim::Mod, num(a.clone()), num(d.clone()));
    let quotient = bin(Prim::IntDiv, num(a.clone()), num(d.clone()));
    let (residue_a, residue_d) = (residue(&int(a.clone())), residue(&int(d.clone())));
    let rem_ask = BigUint::from(1u64 << 20) << 10u32;
    let div_ask = &rem_ask + (BigUint::from(a.bits()) << 1u32);
    let bytes = |bits: &BigUint| u64::try_from(bits >> 3u32).expect("a few hundred MiB");
    lower_limit_by(bytes(&div_ask) + (64 << 20));
    let r = integer(&modulo);
    assert!(
        r.integer_factors().0 < &d,
        "the remainder is below the divisor"
    );
    let q = integer(&quotient);
    let m = u128::from(MERSENNE);
    let qd_r = (u128::from(residue(&q)) * u128::from(residue_d) + u128::from(residue(&r))) % m;
    assert_eq!(qd_r, u128::from(residue_a), "q d + r = a modulo 2^61 - 1");
    drop((q, r));
    lower_limit_by(bytes(&rem_ask) / 2);
    assert_eq!(too_large(&modulo, "mod"), rem_ask);
    assert_eq!(too_large(&quotient, "div"), div_ask);
}

/// A hash kept as a power, `3 ^ 2 ^ 27`, reduced modulo a wide number `2^(2^26)
/// + 1`, under a margin of 28 times the divisor's width: the remainder of the coefficient
/// asks for 24 times and is given, and the modular-power steps ask for 32 times, a measured
/// bound above their peak of 25.2 times, and are refused, although they might fit there
/// (the Complexity tradeoff in `Rat::rem_built`).
#[test]
fn a_kept_power_modulo_a_wide_number_is_refused_below_its_ask() {
    if !in_child("a_kept_power_modulo_a_wide_number_is_refused_below_its_ask") {
        return;
    }
    let k = 1u64 << 26;
    let power = int(3)
        .pow(&BigUint::from(1u64 << 27))
        .expect("a power of 3 is kept");
    let t = bin(Prim::Mod, lit(Value::integer(power)), num(above(k)));
    // 28 times the divisor's width is three and a half times its bytes.
    lower_limit_by(7 * (k + 1) / 2);
    assert_eq!(too_large(&t, "mod"), BigUint::from(k + 1) << 5u32);
}

/// A wide amount held as `3 (2^n + 1) 2^5`, split three ways exactly: the quotient keeps the
/// power of 2 and asks for sixteen times the four coefficients' width before it is built
/// (the Complexity tradeoff in `Rat::scaled`, reached through `Rat::div`), and is refused under
/// the lowered limit.
#[test]
fn an_exact_quotient_of_a_wide_number_is_refused_when_memory_is_short() {
    if !in_child("an_exact_quotient_of_a_wide_number_is_refused_when_memory_is_short") {
        return;
    }
    let amount = Rat::int(BigInt::from(3) * above(WIDE))
        .mul(&two_to(5))
        .unwrap();
    let t = bin(Prim::IntDiv, lit(Value::integer(amount)), num(3));
    lower_limit();
    // Coefficients of `n + 2`, 1, 2 and 1 bits.
    assert_eq!(too_large(&t, "div"), BigUint::from(WIDE + 6) << 4u32);
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
        (bin(Prim::Lt, wide(), half), "`<` applied to `int`, `rat`"),
        (prim(Prim::Not, vec![wide()]), "`!` applied to `int`"),
        (
            prim(Prim::BitNot, vec![num(-above(WIDE)), num(8)]),
            "`bitNot` needs `x` in int[0..], and it is negative",
        ),
        (
            prim(Prim::BitNot, vec![wide(), num(8)]),
            "`bitNot` needs `x` in int[0..<2^width], and it is at least 2^width",
        ),
    ];
    lower_limit();
    for (t, want) in &cases {
        match eval(t) {
            Err(KernelError::Type(m)) => assert_eq!(m, *want),
            other => panic!("{want}: {}", outcome(&other)),
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
            assert_eq!(m, format!("`!` applied to `{want}`"));
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
            let kept = int(a.clone()).mul(&two_to(k)).unwrap();
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
    let (x, y) = (
        int(1).div(&int(6)).unwrap().unwrap(),
        int(1).div(&int(3)).unwrap().unwrap(),
    );
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
    let inputs: Vec<(usize, Term, Term, Term, Term, Term, Term)> = [n, 8 * n]
        .into_iter()
        .map(|m| {
            let w = || num(above(m as u64));
            (
                m,
                bin(Prim::Mod, w(), num(3)),
                bin(Prim::Mod, w(), num(above(128))),
                sub(num(1), w()),
                bin(Prim::IntDiv, w(), num(3)),
                bin(Prim::Mod, w(), num(above(8192))),
                bin(Prim::IntDiv, w(), num(above(8192))),
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
    check_order("2^n + 1 mod 2^8192 + 1", n, 1, |m| {
        assert!(eval(&at(m).5).is_ok());
    });
    check_order("2^n + 1 div 2^8192 + 1", n, 1, |m| {
        assert!(matches!(eval(&at(m).6).unwrap(), Value::Big(_)));
    });
}
