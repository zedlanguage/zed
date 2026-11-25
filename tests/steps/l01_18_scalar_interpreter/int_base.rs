//! `int(s, base: b)` (plan row PARSE-int-base; DESIGN.md sec:corner_cases, "Casts are domain
//! proofs", QUESTIONS A110; the primitive `CastIntBase`, code 89): the text `s` read as an
//! integer in base `b`, `2 <= b <= 36`, its digits `0` to `9` then `a` to `z` in either case,
//! an optional `-` and no prefix; `#invalid` for any other text. The checker shows `b` in
//! `2..=36`, as it shows the argument of a parameter declared with that range. The kernel, the
//! counting machine and native code at both of Cranelift's levels give the same values.

use num_bigint::BigInt;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_native::{OptLevel, run_at};
use zed_tests::step_helpers::l01_16_elaboration::{elab, errors};
use zed_tests::step_helpers::l01_36_cranelift::{kernel, planned};
use zedc::zir::memory;

use super::x;

/// `n` digits of base `radix`, running through every digit of the base from `1`, so that the
/// text has no leading zero and holds each letter the base has.
pub(crate) fn digits(n: usize, radix: u32) -> String {
    (0..n)
        .map(|i| char::from_digit((i as u32 + 1) % radix, radix).expect("a digit of the base"))
        .collect()
}

/// The term `int(s, base: b)`.
pub(crate) fn int_base(s: &str, b: i64) -> Term {
    prim(
        Prim::CastIntBase,
        vec![lit(Value::str(s)), lit(Value::Int(b))],
    )
}

/// The value of `t` by the kernel, by the counting machine and natively at both levels, all
/// equal; the cast also through a function of the text and the base applied to them, so that no
/// constant decides it before the code runs.
fn agreed(s: &str, b: i64) -> Value {
    let called = let_(
        "f",
        lam(
            &["s", "b"],
            prim(Prim::CastIntBase, vec![var("s"), var("b")]),
        ),
        app(var("f"), vec![lit(Value::str(s)), lit(Value::Int(b))]),
    );
    let mut values = Vec::new();
    for t in [int_base(s, b), called] {
        let want = kernel(&t).unwrap_or_else(|e| panic!("{t}: {e}"));
        let (g, p) = planned(&t);
        let (m, _) = memory::run(g.graph(), &p, &mut Evaluator::new(World::new()))
            .unwrap_or_else(|e| panic!("{t}: {e}"));
        assert_eq!(m, want, "{t} by the counting machine");
        for level in [OptLevel::None, OptLevel::Speed] {
            let o = run_at(level, &g, &p, &mut Evaluator::new(World::new()))
                .unwrap_or_else(|e| panic!("{t}: {e}"));
            assert_eq!(o.value, want, "{t} at {level:?}");
        }
        values.push(want);
    }
    assert_eq!(
        values[0], values[1],
        "int({s:?}, base: {b}) direct and called"
    );
    values.remove(0)
}

/// The four examples of DESIGN.md sec:corner_cases, run as programs.
#[test]
fn the_examples_of_the_spec() {
    assert_eq!(x("int(\"755\", base: 8)"), "493");
    assert_eq!(x("int(\"ff\", base: 16)"), "255");
    assert_eq!(x("int(\"1011\", base: 2)"), "11");
    assert_eq!(x("int(\"1F\", base: 16)"), "31");
    // The text through a function, so the checker reads no literal.
    assert_eq!(x("int(text(\"-7f\"), base: 16)"), "-127");
    assert_eq!(x("int(text(\"0x1F\"), base: 16)"), "#invalid");
    assert_eq!(x("int(text(\"+5\"), base: 16)"), "#invalid");
    assert_eq!(x("int(text(\"9\"), base: 8)"), "#invalid");
    assert_eq!(x("int(text(\"\"), base: 2)"), "#invalid");
    assert_eq!(x("int(text(\"007\"), base: 8)"), "7");
    assert_eq!(x("int(text(\"z\"), base: 36)"), "35");
}

/// Bases 2, 8, 10, 16 and 36: the greatest digit of each, the first character past it, both
/// cases of a letter, the sign, and a number wider than a word, by every way of running.
#[test]
fn each_base_at_its_edge_digits() {
    let int = |n: i64| Value::Int(n);
    let invalid = Value::atom("invalid");
    for (b, top, past) in [
        (2, '1', '2'),
        (8, '7', '8'),
        (10, '9', 'a'),
        (16, 'f', 'g'),
        (36, 'z', '{'),
    ] {
        let top_value = top.to_digit(36).expect("a digit") as i64;
        assert_eq!(agreed(&top.to_string(), b), int(top_value), "base {b}");
        assert_eq!(agreed(&format!("-{top}"), b), int(-top_value), "base {b}");
        assert_eq!(
            agreed(&format!("{top}{top}"), b),
            int(top_value * b + top_value)
        );
        assert_eq!(agreed(&format!("1{past}"), b), invalid, "base {b}");
        assert_eq!(agreed("10", b), int(b), "base {b}");
    }
    assert_eq!(agreed("FF", 16), int(255));
    assert_eq!(agreed("fF", 16), int(255));
    assert_eq!(agreed("Zz", 36), int(35 * 36 + 35));
    assert_eq!(agreed("-0", 2), int(0));
    for bad in [
        "", "-", "+1", "--1", " 1", "1 ", "0x1", "1_0", "1.0", "４２",
    ] {
        assert_eq!(agreed(bad, 16), invalid, "{bad:?}");
    }
    let wide = digits(100, 36);
    let want = BigInt::parse_bytes(wide.as_bytes(), 36).expect("digits of base 36");
    assert_eq!(agreed(&wide, 36), Value::int(want));
    let wide = format!("-{}", digits(70, 7));
    let want = BigInt::parse_bytes(wide.as_bytes(), 7).expect("digits of base 7");
    assert_eq!(agreed(&wide, 7), Value::int(want));
}

/// A base the checker does not show in `2..=36` is rejected: a literal outside it, and a
/// parameter of type `int`. Positive controls: a literal at each end, and a parameter declared
/// in the range. The base is named: by position, or by another name, the call is rejected.
#[test]
fn a_base_outside_two_to_thirty_six_is_rejected() {
    for b in ["1", "37", "0", "-16"] {
        let got = errors(&format!("x = int(\"10\", base: {b});\n"));
        assert_eq!(got.len(), 1, "base {b}: {got:?}");
        assert!(got[0].contains("base"), "base {b}: {}", got[0]);
    }
    let got = errors("f(positional s: String, b: int) = int(s, base: b);\n");
    assert_eq!(got.len(), 1, "{got:?}");
    for ok in [
        "x = int(\"10\", base: 2);\n",
        "x = int(\"10\", base: 36);\n",
        "f(positional s: String, b: int[2..=36]) = int(s, base: b);\n",
        "f(positional s: String, b: int[8..=16]) = int(s, base: b);\n",
    ] {
        assert!(elab(ok).is_ok(), "{ok}: {:?}", elab(ok).err());
    }
    assert!(!errors("x = int(\"10\", 16);\n").is_empty());
    assert!(!errors("x = int(\"10\", radix: 16);\n").is_empty());
}

/// A text and a base written as literals that the cast cannot read are rejected as an operation
/// that always fails (DESIGN.md sec:failure), as `int("x")` is; a text it reads, and a text
/// known only when the program runs, are not.
#[test]
fn a_literal_text_that_is_no_number_in_its_base_always_fails() {
    for (s, b) in [
        ("9", 8),
        ("0x1F", 16),
        ("+5", 10),
        ("", 2),
        ("g", 16),
        ("-", 36),
    ] {
        let got = errors(&format!("x = int({s:?}, base: {b});\n"));
        assert_eq!(got.len(), 1, "{s:?} base {b}: {got:?}");
        assert!(
            got[0].starts_with(&format!(
                "`int` here always fails: its operand `{s:?}` in base {b} gives `#invalid`"
            )),
            "{}",
            got[0]
        );
    }
    for ok in [
        "x = int(\"8\", base: 9);\n",
        "x = int(\"-Zz\", base: 36);\n",
        "x = int(text(\"9\"), base: 8);\n",
    ] {
        let src = format!("text(positional v: String) = v;\n{ok}");
        assert!(elab(&src).is_ok(), "{ok}: {:?}", elab(&src).err());
    }
}

/// The input of the scaling benches (deferred to plan row RADIX-nlog2-10_5) at a small size
/// reads as num-bigint reads it, at both of their radixes.
#[test]
fn the_bench_input_reads_at_a_small_size() {
    for radix in [7u32, 36] {
        let text = digits(5000, radix);
        let want = BigInt::parse_bytes(text.as_bytes(), radix).expect("digits of the base");
        let got = kernel(&int_base(&text, i64::from(radix))).expect("no failure");
        assert_eq!(got, Value::int(want), "radix {radix}");
    }
}
