//! Item CHK-f64-bounded-int: `f64(n)` of an int the checker proves lies within ±2^53 gives no
//! `#inexact`. DESIGN.md "Casts are domain proofs": "numeric casts additionally carry
//! `#inexact` unless the argument's domain proves exact representability — `f64(n)` is exact
//! when `|n| ≤ 2^53`". The ints an operand may be come from its text (literals, names bound to
//! them, the integer operators, the bit words, `codePoint`) and from the tests the cast is under;
//! a declared range on a parameter is layer L10.

use zed_tests::scaling;

use super::scaling::resolved;
use super::{sig, type_errors};

/// `f(positional n: int) = if <test> { f64(n) } else { 0.0f64 };` and its signature.
fn under(test: &str) -> String {
    let src = format!("f(positional n: int) = if {test} {{ f64(n) }} else {{ 0.0f64 }};\n");
    assert!(type_errors(&src).is_empty(), "{src}");
    sig(&src, "f")
}

#[test]
fn an_int_a_test_bounds_within_two_to_the_53_casts_exactly() {
    // A count of at most 100, as a fraction's numerator.
    assert_eq!(under("n >= 0 && n <= 100"), "(int) -> f64");
    // Both bounds of the exact range, each included.
    assert_eq!(
        under("n >= -9007199254740992 && n <= 9007199254740992"),
        "(int) -> f64"
    );
    // The arm where the test fails is not bounded, and keeps the atom.
    let src = "f(positional n: int) = if n < 0 || n > 100 { f64(n) } else { 0.0f64 };\n";
    assert_eq!(sig(src, "f"), "(int) -> f64 | #inexact");
}

#[test]
fn one_past_either_bound_keeps_inexact() {
    for test in [
        "n >= -9007199254740993 && n <= 9007199254740992",
        "n >= -9007199254740992 && n <= 9007199254740993",
        // Bounded on one side only.
        "n >= 0",
        "n <= 0",
    ] {
        assert_eq!(under(test), "(int) -> f64 | #inexact", "{test}");
    }
}

#[test]
fn an_unbounded_int_keeps_inexact() {
    assert_eq!(
        sig("f(positional n: int) = f64(n);\n", "f"),
        "(int) -> f64 | #inexact"
    );
    // A test on another name says nothing of `n`.
    assert_eq!(
        sig(
            "f(positional n: int, positional m: int) = \
             if m >= 0 && m <= 100 { f64(n) } else { 0.0f64 };\n",
            "f"
        ),
        "(int, int) -> f64 | #inexact"
    );
}

#[test]
fn an_int_the_text_bounds_casts_exactly() {
    for (src, want) in [
        // Literals, at both bounds and inside.
        ("f(x: int) = f64(5);", "(x: int) -> f64"),
        ("f(x: int) = f64(9007199254740992);", "(x: int) -> f64"),
        ("f(x: int) = f64(-9007199254740992);", "(x: int) -> f64"),
        // A name bound to a literal, and an operation on one.
        ("f(x: int) = { k = 12; f64(k) };", "(x: int) -> f64"),
        ("f(x: int) = { k = 12; f64(k * 2 - 1) };", "(x: int) -> f64"),
        // A code point lies in 0 ..= 1114111; its own atom passes the cast.
        (
            "f(s: String) = f64(codePoint(s));",
            "(s: String) -> f64 | #notScalar",
        ),
        // The value of a parameter in a sum is not bounded.
        ("f(x: int) = f64(x + 1);", "(x: int) -> f64 | #inexact"),
    ] {
        assert!(type_errors(src).is_empty(), "{src}");
        assert_eq!(sig(src, "f"), want, "{src}");
    }
}

#[test]
fn a_literal_one_past_either_bound_keeps_inexact() {
    // 2^53 + 1 and its negation have no exact `f64`. A bare literal is generic, so its cast is
    // not rejected as one that always fails: read as an `f64`, the literal converts.
    for src in [
        "f(x: int) = f64(9007199254740993);",
        "f(x: int) = f64(-9007199254740993);",
    ] {
        assert!(type_errors(src).is_empty(), "{src}");
        assert_eq!(sig(src, "f"), "(x: int) -> f64 | #inexact", "{src}");
    }
}

#[test]
fn an_exact_cast_runs_to_the_float() {
    let src = "half(positional n: int) = if n >= 0 && n <= 1000 { f64(n) / 2.0 } else { 0.0f64 }\n\
               test { 3 -> 1.5, 1000 -> 500.0, -1 -> 0.0 }\n";
    let out = zedc::testing::test(src);
    assert!(
        !out.is_empty() && out.iter().all(|o| o.failure.is_none()),
        "{src}"
    );
    assert_eq!(sig(src, "half"), "(int) -> f64");
}

#[test]
fn many_bounded_casts_scale() {
    // n functions, each casting its parameter under a test that bounds it.
    let functions = |n: usize| -> String {
        (0..n)
            .map(|i| {
                format!(
                    "g{i}(positional n: int) = if n >= 0 && n <= {i} {{ f64(n) }} else {{ 0.0f64 }};\n"
                )
            })
            .collect()
    };
    let units = resolved(200, functions);
    scaling::check("n functions, each a cast under a test", 200, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
    // One function of n arms, each arm a cast under the tests of the arms before it.
    let chain = |n: usize| -> String {
        let arms: String = (0..n)
            .map(|i| format!("if n < {} {{ f64(n) }} else ", i as i64 - n as i64))
            .collect();
        format!("f(positional n: int) = {arms}{{ 0.0f64 }};\n")
    };
    let units = resolved(200, chain);
    scaling::check("a chain of n arms, each a cast", 200, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
