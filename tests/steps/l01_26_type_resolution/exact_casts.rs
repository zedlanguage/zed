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
    assert_eq!(sig(src, "f"), "(int) -> f64 | #inexact | #overflow");
}

#[test]
fn one_past_either_bound_keeps_inexact() {
    for (test, want) in [
        (
            "n >= -9007199254740993 && n <= 9007199254740992",
            "(int) -> f64 | #inexact",
        ),
        (
            "n >= -9007199254740992 && n <= 9007199254740993",
            "(int) -> f64 | #inexact",
        ),
        // Bounded on one side only: beyond the largest `f64` on the other (A36).
        ("n >= 0", "(int) -> f64 | #inexact | #overflow"),
        ("n <= 0", "(int) -> f64 | #inexact | #overflow"),
    ] {
        assert_eq!(under(test), want, "{test}");
    }
}

#[test]
fn an_unbounded_int_keeps_inexact() {
    assert_eq!(
        sig("f(positional n: int) = f64(n);\n", "f"),
        "(int) -> f64 | #inexact | #overflow"
    );
    // A test on another name says nothing of `n`.
    assert_eq!(
        sig(
            "f(positional n: int, positional m: int) = \
             if m >= 0 && m <= 100 { f64(n) } else { 0.0f64 };\n",
            "f"
        ),
        "(int, int) -> f64 | #inexact | #overflow"
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
        (
            "f(x: int) = f64(x + 1);",
            "(x: int) -> f64 | #inexact | #overflow",
        ),
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

/// Item CHK-f64-bounded-int-menus: a rejection beside an `int` the checker bounds within
/// ±2^53 offers `f64(n)` among its fixes, and one beside an unbounded `int` does not
/// (DESIGN.md sec:diagnostics, row "Two numeric values with no common carrier").
#[test]
fn a_bounded_int_beside_a_decimal_is_offered_both_casts() {
    let src = "f(positional n: int) = if n >= 0 && n <= 100 { n + 1.5 } else { 0.0 };\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    for fix in [
        "{ rat(n) + 1.5 } else { 0.0 };    n is cast to rat, and `+` takes two rat",
        "{ f64(n) + 1.5 } else { 0.0 };    n is cast to f64, exactly, since it lies within ±2^53",
    ] {
        assert!(errors[0].contains(fix), "{fix}\n{}", errors[0]);
    }
    let errors = type_errors("f(positional n: int) = n + 1.5;\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("rat(n) + 1.5"), "{}", errors[0]);
    assert!(!errors[0].contains("f64(n)"), "{}", errors[0]);
}

#[test]
fn a_bounded_int_compared_with_an_f64_is_offered_its_cast() {
    let src = "f(positional n: int, positional y: f64) = \
               if n >= 0 && n <= 100 { y == n } else { false };\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with(
            "No value is both `f64` and `int`: `y : f64 == n : int` always gives the same \
             answer. Try `y == f64(n)` to compare the numbers instead."
        ),
        "{}",
        errors[0]
    );
    let errors = type_errors("f(positional n: int, positional y: f64) = y == n;\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(!errors[0].contains("f64(n)"), "{}", errors[0]);
}

#[test]
fn many_bounded_comparisons_scale() {
    // n functions, each comparing an f64 with an int a test bounds: n rejections, each
    // offering `f64(n)`. The bound of each is proved from the tests above it alone.
    let functions = |n: usize| -> String {
        (0..n)
            .map(|i| {
                format!(
                    "g{i}(positional n: int, positional y: f64) = \
                     if n >= 0 && n <= {i} {{ y == n }} else {{ false }};\n"
                )
            })
            .collect()
    };
    let units = resolved(200, functions);
    scaling::check("n rejected comparisons, each of a bounded int", 200, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), n);
    });
}

/// Item CAST-overflow-atom (A36): a cast to a float format is `#overflow` for a number beyond
/// the format's largest finite value, and the atom stays in the type only where the checker
/// cannot prove the operand never gives it. The ints an operand may be come from its text and
/// the tests the cast is under, as for `#inexact` above.
fn largest(precision: u32, emax: u32) -> num_bigint::BigInt {
    ((num_bigint::BigInt::from(1) << precision) - 1) << (emax - precision + 1)
}

#[test]
fn a_cast_to_a_float_format_may_overflow() {
    for (src, want) in [
        (
            "f(positional n: int) = f64(n);",
            "(int) -> f64 | #inexact | #overflow",
        ),
        (
            "f(positional n: int) = f32(n);",
            "(int) -> f32 | #inexact | #overflow",
        ),
        (
            "f(positional r: rat) = f64(r);",
            "(rat) -> f64 | #inexact | #overflow",
        ),
        (
            "f(positional x: f64) = f32(x);",
            "(f64) -> f32 | #inexact | #overflow",
        ),
        // A text is read correctly rounded: never `#inexact`, `#overflow` past the largest.
        (
            "f(positional s: String) = f64(s);",
            "(String) -> f64 | #invalid | #overflow",
        ),
        (
            "f(positional s: String) = f32(s);",
            "(String) -> f32 | #invalid | #overflow",
        ),
        // No float format is beyond another's range upward, and `int` and `rat` have none.
        ("f(positional x: f32) = f64(x);", "(f32) -> f64"),
        ("f(positional x: f64) = rat(x);", "(f64) -> rat | #invalid"),
        ("f(positional r: rat) = int(r);", "(rat) -> int | #inexact"),
    ] {
        assert!(type_errors(src).is_empty(), "{src}");
        assert_eq!(sig(src, "f"), want, "{src}");
    }
}

#[test]
fn an_int_bounded_within_the_largest_float_gives_no_overflow() {
    let f64_max = largest(53, 1023);
    let f32_max = largest(24, 127);
    for (c, test, want) in [
        // Beyond ±2^53 but within the range: `#inexact` alone.
        (
            "f64",
            "n >= 0 && n <= 1152921504606846976".to_string(),
            "f64 | #inexact",
        ),
        (
            "f64",
            format!("n >= -{f64_max} && n <= {f64_max}"),
            "f64 | #inexact",
        ),
        (
            "f32",
            format!("n >= -{f32_max} && n <= {f32_max}"),
            "f32 | #inexact",
        ),
        // 2^127 lies within the range of `f32`; 2^128 does not, but within that of `f64`.
        (
            "f32",
            format!("n >= 0 && n <= {}", num_bigint::BigInt::from(1) << 127),
            "f32 | #inexact",
        ),
        (
            "f32",
            format!("n >= 0 && n <= {}", num_bigint::BigInt::from(1) << 128),
            "f32 | #inexact | #overflow",
        ),
        (
            "f64",
            format!("n >= 0 && n <= {}", num_bigint::BigInt::from(1) << 128),
            "f64 | #inexact",
        ),
        // One past the largest, either side, and bounded on one side only.
        (
            "f64",
            format!("n >= 0 && n <= {}", &f64_max + 1),
            "f64 | #inexact | #overflow",
        ),
        (
            "f64",
            format!("n >= -{} && n <= 0", &f64_max + 1),
            "f64 | #inexact | #overflow",
        ),
        (
            "f32",
            format!("n >= 0 && n <= {}", &f32_max + 1),
            "f32 | #inexact | #overflow",
        ),
        ("f64", "n >= 0".to_string(), "f64 | #inexact | #overflow"),
        // Within ±2^53 the cast is exact, as before.
        ("f64", "n >= 0 && n <= 100".to_string(), "f64"),
    ] {
        let src = format!("f(positional n: int) = if {test} {{ {c}(n) }} else {{ 0.0{c} }};\n");
        assert!(type_errors(&src).is_empty(), "{src}");
        assert_eq!(sig(&src, "f"), format!("(int) -> {want}"), "{src}");
    }
}

#[test]
fn a_text_beyond_the_largest_float_always_fails_with_overflow() {
    let errors = type_errors("f(x: int) = f64(\"1e400\");\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with(
            "`f64` here always fails: its operand `\"1e400\"` gives `#overflow`, so this call \
             never gives a value."
        ),
        "{}",
        errors[0]
    );
    // Within the range, the text reads correctly rounded, with no atom.
    assert_eq!(
        type_errors("f(x: int) = f64(\"1e300\");\n"),
        Vec::<String>::new()
    );
}

#[test]
fn many_casts_of_ints_in_range_scale() {
    // n functions, each casting its parameter under a test that bounds it beyond ±2^53 and
    // within the largest `f64`: the path that drops `#overflow` and keeps `#inexact`.
    let functions = |n: usize| -> String {
        (0..n)
            .map(|i| {
                format!(
                    "g{i}(positional n: int) = \
                     if n >= 0 && n <= {} {{ f64(n) }} else {{ 0.0f64 }};\n",
                    (num_bigint::BigInt::from(1) << 60) + i
                )
            })
            .collect()
    };
    let units = resolved(200, functions);
    scaling::check("n functions, each a cast of an int in range", 200, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
