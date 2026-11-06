//! Item RAT-asks: building a kept power, a sum of kept powers, a power of a wide base, the
//! text of a wide number, and the reading of a long number from a string or a literal each ask
//! the system for a measured multiple of their memory first (COMPLEXITY.md K30), so where the
//! free memory lies between the old ask and the peak the work is refused with an error naming
//! the memory asked, where it used to abort the process. Each refusal is checked in a child
//! under a limit 8 MiB above what it holds, at two widths, n and 8n, the smaller of which
//! aborted the child under the old ask; the same work is exact when its ask is given.

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use zed_kernel::num::{TooLarge, bytes_of};
use zed_kernel::term::build::{lit, prim};
use zed_kernel::{KernelError, Prim, Rat, Value, eval};
use zed_tests::scaling::check_order;

use super::memory_check::{in_child_at, lower_limit_by};

fn in_child(name: &str) -> bool {
    in_child_at(module_path!(), name)
}

/// The limit above what the child holds once its operands are built.
const SHORT: u64 = 8 << 20;

fn int(n: u64) -> Rat {
    Rat::int(BigInt::from(n))
}

/// `p^e`, kept and not built.
fn kept(p: u64, e: u64) -> Rat {
    int(p)
        .pow(&BigUint::from(e))
        .expect("a prime's power is kept")
}

/// `3^k * 7^k * 11^k`, kept: `9k + 1` bits counted at their widest.
fn three_primes(k: u64) -> Rat {
    kept(3, k)
        .mul(&kept(7, k))
        .and_then(|r| r.mul(&kept(11, k)))
        .expect("kept powers multiply without building")
}

/// `2^s - 1`, built.
fn below(s: u64) -> Rat {
    Rat::int((BigInt::one() << s) - 1u32)
}

/// `2^s + 1`, built.
fn above(s: u64) -> Rat {
    Rat::int((BigInt::one() << s) + 1u32)
}

/// The memory a refusal asked, in bytes.
fn asked(r: Result<impl Sized, TooLarge>) -> BigUint {
    match r {
        Err(TooLarge { bits }) => bytes_of(&bits),
        Ok(_) => panic!("answered"),
    }
}

/// The memory `eval` of `p` on `x` asked when it was refused, in bytes, with the operator the
/// error names; anything else is told without printing a number's digits.
fn refused(p: Prim, x: Value, op: &str) -> BigUint {
    match eval(&prim(p, vec![lit(x)])) {
        Err(KernelError::NumberTooLarge { op: o, bits }) if o == op => bytes_of(&bits),
        Ok(v) => panic!("answered a value of type {}", v.kind_type()),
        Err(e) => panic!("another error: {e:?}"),
    }
}

/// The memory asked is in bytes, rounded up.
#[test]
fn the_memory_asked_is_named_in_bytes_rounded_up() {
    for (bits, bytes) in [
        (0u32, 0u32),
        (1, 1),
        (7, 1),
        (8, 1),
        (9, 2),
        (16, 2),
        (17, 3),
    ] {
        assert_eq!(
            bytes_of(&BigUint::from(bits)),
            BigUint::from(bytes),
            "{bits}"
        );
    }
}

/// `3^k 7^k 11^k` built from its kept powers asks a byte for each of its `9k + 1` bits: at
/// `k = 2^22` that is 36 MiB, refused; the old ask of a bit for each, 4.5 MiB, was given, and
/// the build rose to about five times it and aborted.
#[test]
fn building_a_kept_power_is_refused_when_memory_is_short() {
    if !in_child("building_a_kept_power_is_refused_when_memory_is_short") {
        return;
    }
    let all = [1u64 << 22, 1 << 25].map(|k| (k, three_primes(k)));
    lower_limit_by(SHORT);
    for (k, x) in &all {
        assert_eq!(asked(x.to_integer()), BigUint::from(9 * k + 1), "k = {k}");
    }
}

/// `3^k + 7^k` asks a byte for each bit of the wider side, `7^k` counted at its widest, `3k`
/// bits, with a bit for its coefficient and one for its denominator, and one more: at
/// `k = 2^23`, 24 MiB, refused; the old ask of 3 MiB was given and the sum rose to about four
/// and a half times it.
#[test]
fn a_sum_of_kept_powers_is_refused_when_memory_is_short() {
    if !in_child("a_sum_of_kept_powers_is_refused_when_memory_is_short") {
        return;
    }
    let all = [1u64 << 23, 1 << 26].map(|k| (k, kept(3, k), kept(7, k)));
    lower_limit_by(SHORT);
    for (k, a, b) in &all {
        assert_eq!(asked(a.add(b)), BigUint::from(3 * k + 3), "k = {k}");
        assert_eq!(asked(b.sub(a)), BigUint::from(3 * k + 3), "k = {k}");
    }
}

/// `(2^s - 1)^7` asks a byte for each bit of the base times the exponent: at `s = 2^22`,
/// 28 MiB, refused; the old ask of 3.5 MiB was given and the power rose to about six times it.
#[test]
fn a_power_of_a_wide_base_is_refused_when_memory_is_short() {
    if !in_child("a_power_of_a_wide_base_is_refused_when_memory_is_short") {
        return;
    }
    let all = [1u64 << 22, 1 << 25].map(|s| (s, below(s)));
    lower_limit_by(SHORT);
    for (s, x) in &all {
        assert_eq!(
            asked(x.pow(&BigUint::from(7u32))),
            BigUint::from(7 * s),
            "s = {s}"
        );
    }
}

/// The memory, in bytes, `String` of `2^s + 1` asks: a byte for each of its `s + 2` bits
/// (`s + 1` of the numerator and one of the denominator) and eight for each byte of its text, at
/// most `0.301 (s + 2) + 2`, as `Rat::text_size` bounds them.
fn print_ask(s: u64) -> u64 {
    s + 2 + 8 * ((((s + 2) * 1234) >> 12) + 2)
}

/// `String` of `2^s + 1` asks a byte for each of its bits and eight for each byte of its text:
/// at `s = 2^23`, about 27 MiB, refused; the old ask of an eighth of that was given, and the
/// printing rose to about four times it.
#[test]
fn printing_a_wide_number_is_refused_when_memory_is_short() {
    if !in_child("printing_a_wide_number_is_refused_when_memory_is_short") {
        return;
    }
    let all = [1u64 << 23, 1 << 26].map(|s| (s, Value::integer(above(s))));
    lower_limit_by(SHORT);
    for (s, x) in all {
        assert_eq!(
            refused(Prim::Show, x, "String"),
            BigUint::from(print_ask(s)),
            "s = {s}"
        );
    }
}

/// `int` of `n` nines and `rat` of `n/2` nines over `n/2` sevens ask four bytes a digit: at
/// `n = 2^22`, 16 MiB, refused; reading them asked for nothing and rose to about 10 MiB.
#[test]
fn reading_a_long_number_from_a_string_is_refused_when_memory_is_short() {
    if !in_child("reading_a_long_number_from_a_string_is_refused_when_memory_is_short") {
        return;
    }
    let all = [1usize << 22, 1 << 25].map(|n| {
        let nines = Value::str(&"9".repeat(n));
        let half = "9".repeat(n / 2);
        let ratio = Value::str(&format!("{half}/{}", "7".repeat(n / 2)));
        (n, nines, ratio)
    });
    lower_limit_by(SHORT);
    for (n, nines, ratio) in all {
        let want = BigUint::from(4 * n);
        assert_eq!(refused(Prim::CastInt, nines, "int"), want, "n = {n}");
        assert_eq!(refused(Prim::CastRat, ratio, "rat"), want, "n = {n}");
    }
}

/// [`three_primes`], `3^k + 7^k`, `(2^s - 1)^7`, the text of `2^s + 1`, and the reading of
/// `n` nines and of `n/2` nines over `10^(n/2 - 1)`, each under a limit of its ask and 64 MiB
/// more: each is answered, and equal to the value num-bigint builds.
#[test]
fn kept_powers_sums_powers_texts_and_readings_are_exact_when_their_ask_is_given() {
    if !in_child("kept_powers_sums_powers_texts_and_readings_are_exact_when_their_ask_is_given") {
        return;
    }
    let (k, s, n) = (1u64 << 16, 1u64 << 18, 1usize << 18);
    let power = |p: u32, e: u64| BigInt::from(p).pow(u32::try_from(e).expect("e fits a u32"));
    let product = power(3, k) * power(7, k) * power(11, k);
    let sum = power(3, k) + power(7, k);
    let seventh = ((BigInt::one() << s) - 1u32).pow(7u32);
    let text = ((BigInt::one() << s) + 1u32).to_string();
    let nines = "9".repeat(n);
    let (half, tens) = ("9".repeat(n / 2), format!("1{}", "0".repeat(n / 2 - 1)));
    let ratio = format!("{half}/{tens}");
    let (a, b, wide, x) = (three_primes(k), kept(3, k), below(s), above(s));
    let (c, big) = (kept(7, k), Value::integer(x));
    let ask: u64 = [9 * k + 1, 3 * k + 3, 7 * s, print_ask(s)]
        .into_iter()
        .chain([4 * n as u64])
        .max()
        .expect("five asks");
    lower_limit_by(ask + (64 << 20));
    assert!(a.to_integer().expect("given") == product);
    assert!(b.add(&c).and_then(|r| r.to_integer()).expect("given") == sum);
    let built = wide.pow(&BigUint::from(7u32)).and_then(|r| r.to_integer());
    assert!(built.expect("given") == seventh);
    let Ok(Value::Str(shown)) = eval(&prim(Prim::Show, vec![lit(big)])) else {
        panic!("a text")
    };
    assert!(shown.flat() == text.as_str());
    let read = |p: Prim, t: &str| eval(&prim(p, vec![lit(Value::str(t))])).expect("given");
    assert!(read(Prim::CastInt, &nines) == Value::int(nines.parse::<BigInt>().expect("digits")));
    let num: BigInt = half.parse().expect("digits");
    let den: BigInt = tens.parse().expect("digits");
    assert!(
        read(Prim::CastRat, &ratio)
            == Value::rat(Rat::in_lowest_terms(num, den).expect("in lowest terms"))
    );
}

/// Each unit of `texts` parsed and resolved; then checked, under a limit `margin` bytes above
/// what the child holds when `check_short`, and elaborated under that limit otherwise. Returns
/// the messages of the errors the pass under the limit reported, unit by unit. Each unit is
/// read in full before the limit is lowered, as elaboration stops at a unit's first error.
fn literal_errors(texts: &[String], margin: u64, check_short: bool) -> Vec<String> {
    let units: Vec<_> = texts
        .iter()
        .map(|text| {
            let tokens = zedc::lex::lex_fence(text).expect("the text lexes");
            let tree =
                zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).expect("it parses");
            let stmts = zedc::ast::unit(text, &tokens, &tree).expect("it is a unit");
            let res = zedc::resolve::resolve(&stmts).expect("it resolves");
            let info = (!check_short).then(|| zedc::check::check(&stmts, &res));
            (stmts, res, info)
        })
        .collect();
    lower_limit_by(margin);
    let mut out = Vec::new();
    for (stmts, res, info) in &units {
        let errors = match info {
            None => zedc::check::check(stmts, res).errors,
            Some(info) => match zedc::elab::elaborate_checked(stmts, res, info) {
                Err(errs) => errs,
                Ok(_) => panic!("elaborated without error"),
            },
        };
        out.extend(errors.into_iter().map(|e| e.message));
    }
    out
}

/// The message for a literal whose digits the system refused `bytes` bytes to read.
fn unread(bytes: usize) -> String {
    format!(
        "this literal has so many digits that the system refused the {bytes} bytes of memory \
         asked to read them; a literal has no size limit, but this machine cannot hold this \
         one's value; write fewer digits"
    )
}

/// A decimal literal of `2^22` nines asks four bytes a digit, 16 MiB, and a hexadecimal one
/// of `2^22` `f`s three, 12 MiB: under a limit 2 MiB above what the child holds, the
/// elaborator reports each, where it copied the digits and read them with no ask and aborted.
#[test]
fn a_long_integer_literal_is_refused_when_memory_is_short() {
    if !in_child("a_long_integer_literal_is_refused_when_memory_is_short") {
        return;
    }
    let n = 1usize << 22;
    let texts = [
        format!("x = {};\n", "9".repeat(n)),
        format!("y = 0x{};\n", "f".repeat(n)),
    ];
    assert_eq!(
        literal_errors(&texts, 2 << 20, false),
        [unread(4 * n), unread(3 * n)]
    );
}

/// The checker reads each integer literal and copies a float literal's text: under a limit
/// 2 MiB above what the child holds, a literal of `2^22` nines and one of `0.` and `2^22`
/// nines are each reported, where the checker copied their text with no ask and aborted.
#[test]
fn checking_a_long_literal_is_refused_when_memory_is_short() {
    if !in_child("checking_a_long_literal_is_refused_when_memory_is_short") {
        return;
    }
    let n = 1usize << 22;
    let text = format!("x = {};\ny = 0.{};\n", "9".repeat(n), "9".repeat(n));
    assert_eq!(
        literal_errors(&[text], 2 << 20, true),
        [unread(4 * n), unread(n + 2)]
    );
}

/// Checking a float literal of `n` digits reads them where they are and copies its text once,
/// in memory asked first: O(n), at `n = 2^16` and `8n`.
#[test]
fn checking_a_long_float_literal_costs_order_n() {
    let unit = |n: usize| {
        let text = format!("x = 0.{};\n", "9".repeat(n));
        let tokens = zedc::lex::lex_fence(&text).expect("the text lexes");
        let tree = zedc::parse::parse(&text, &tokens, "Unit", zedc::parse::TOP).expect("it parses");
        let stmts = zedc::ast::unit(&text, &tokens, &tree).expect("it is a unit");
        let res = zedc::resolve::resolve(&stmts).expect("it resolves");
        (n, stmts, res)
    };
    let n = 1 << 16;
    let units = [unit(n), unit(8 * n)];
    check_order("checking a float literal of n digits", n, 1, |m| {
        let (_, stmts, res) = units
            .iter()
            .find(|(k, _, _)| *k == m)
            .expect("a size built");
        assert!(zedc::check::check(stmts, res).errors.is_empty());
    });
}
