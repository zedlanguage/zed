//! Casts to a float format and the ints the checker bounds. Since plan row CAST-round-whole
//! (step L1.18) a cast to a float format gives no atom: it is the float nearest the value,
//! ties to even, and the infinity of its sign past the largest finite float; whether it
//! rounded is the `inexact()` fact of step L10.3b, not part of the type. What the checker
//! still learns from the ints an operand may be (its text, and the tests the cast is under) is
//! whether `f64(n)` is exact, which decides whether a repair offers it (item
//! CHK-f64-bounded-int-menus). `int` of a value not proved whole is rejected
//! (`l01_18_scalar_interpreter::casts`).

use super::{sig, type_errors};

/// `f(positional n: int) = if <test> { <c>(n) } else { 0.0<c> };` and its signature.
fn under(c: &str, test: &str) -> String {
    let src = format!("f(positional n: int) = if {test} {{ {c}(n) }} else {{ 0.0{c} }};\n");
    assert!(type_errors(&src).is_empty(), "{src}");
    sig(&src, "f")
}

/// The largest finite float of `precision` bits and largest exponent `emax`.
fn largest(precision: u32, emax: u32) -> num_bigint::BigInt {
    ((num_bigint::BigInt::from(1) << precision) - 1) << (emax - precision + 1)
}

#[test]
fn a_cast_of_an_int_to_a_float_format_gives_no_atom_bounded_or_not() {
    let f64_max = largest(53, 1023);
    let f32_max = largest(24, 127);
    for (c, test) in [
        // Within ±2^53, where `f64(n)` is exact, both bounds included.
        ("f64", "n >= 0 && n <= 100".to_string()),
        (
            "f64",
            "n >= -9007199254740992 && n <= 9007199254740992".to_string(),
        ),
        // One past either bound, where it may round.
        (
            "f64",
            "n >= -9007199254740993 && n <= 9007199254740992".to_string(),
        ),
        (
            "f64",
            "n >= -9007199254740992 && n <= 9007199254740993".to_string(),
        ),
        // At the largest finite float, one past it, and bounded on one side only.
        ("f64", format!("n >= -{f64_max} && n <= {f64_max}")),
        ("f64", format!("n >= 0 && n <= {}", &f64_max + 1)),
        ("f64", "n >= 0".to_string()),
        ("f64", "n <= 0".to_string()),
        ("f64", "n < 0 || n > 100".to_string()),
        ("f32", "n >= -16777216 && n <= 16777216".to_string()),
        ("f32", format!("n >= -{f32_max} && n <= {f32_max}")),
        ("f32", format!("n >= 0 && n <= {}", &f32_max + 1)),
        ("f32", "true".to_string()),
    ] {
        assert_eq!(under(c, &test), format!("int -> {c}"), "{c}: {test}");
    }
}

#[test]
fn a_cast_to_a_float_format_gives_no_atom_but_invalid_from_a_text() {
    for (src, want) in [
        ("f(positional n: int) = f64(n);", "int -> f64"),
        ("f(positional n: int) = f32(n);", "int -> f32"),
        ("f(positional r: rat) = f64(r);", "rat -> f64"),
        ("f(positional r: rat) = f32(r);", "rat -> f32"),
        ("f(positional x: f64) = f32(x);", "f64 -> f32"),
        ("f(positional x: f32) = f64(x);", "f32 -> f64"),
        ("f(x: int) = f64(x + 1);", "(x: int) -> f64"),
        (
            "f(positional n: int, positional m: int) = \
             if m >= 0 && m <= 100 { f64(n) } else { 0.0f64 };",
            "(int, int) -> f64",
        ),
        // A text is read correctly rounded, past the range to an infinity; one that is not a
        // number is `#invalid`.
        (
            "f(positional s: String) = f64(s);",
            "String -> f64 | #invalid",
        ),
        (
            "f(positional s: String) = f32(s);",
            "String -> f32 | #invalid",
        ),
        // `rat` of an infinity or the NaN is `#invalid`.
        (
            "f(positional x: f64) = rat(x);",
            "f64 -> rat | #NaN | #overflow",
        ),
        // A code point lies in 0 ..= 1114111; its own atom passes the cast.
        (
            "f(s: String) = f64(codePoint(s));",
            "(s: String) -> f64 | #notScalar",
        ),
    ] {
        assert!(type_errors(src).is_empty(), "{src}");
        assert_eq!(sig(src, "f"), want, "{src}");
    }
}

#[test]
fn a_cast_of_a_literal_rounds_and_is_never_rejected() {
    let f64_max = largest(53, 1023);
    let f32_max = largest(24, 127);
    let (f64_past, f32_past) = (&f64_max + 1u32, &f32_max + 1u32);
    for (c, literal) in [
        ("f64", "5".to_string()),
        ("f64", "9007199254740992".to_string()),
        ("f64", "9007199254740993".to_string()),
        ("f64", "-9007199254740993".to_string()),
        ("f64", f64_max.to_string()),
        ("f64", f64_past.to_string()),
        ("f64", format!("-{f64_past}")),
        ("f64", format!("{f64_past}r")),
        ("f32", f32_past.to_string()),
        ("f32", format!("{f32_past}r")),
        ("f32", "16777217r".to_string()),
        ("f64", "1e22r".to_string()),
        ("f64", "1e23r".to_string()),
        ("f64", "1e309r".to_string()),
        ("f64", "-1e309r".to_string()),
        ("f64", "1e-400r".to_string()),
        ("f32", "1e11r".to_string()),
        ("f32", "1e39r".to_string()),
        // Its powers are compared and never built: 10^400000000 would hold 1.3 * 10^9 bits.
        ("f64", "1e400000000r".to_string()),
        ("f64", "1e-400000000r".to_string()),
        ("f64", "\"1e400\"".to_string()),
    ] {
        let src = format!("f(x: int) = {c}({literal});\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        assert_eq!(sig(&src, "f"), format!("(x: int) -> {c}"), "{src}");
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
    assert_eq!(sig(src, "half"), "int -> f64");
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

/// `n` functions, each casting its parameter under a test that bounds it.
pub(super) fn bounded_casts(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "g{i}(positional n: int) = if n >= 0 && n <= {i} {{ f64(n) }} else {{ 0.0f64 }};\n"
            )
        })
        .collect()
}

/// One function of `n` arms, each arm a cast under the tests of the arms before it.
pub(super) fn arms_of_casts(n: usize) -> String {
    let arms: String = (0..n)
        .map(|i| format!("if n < {} {{ f64(n) }} else ", i as i64 - n as i64))
        .collect();
    format!("f(positional n: int) = {arms}{{ 0.0f64 }};\n")
}

/// `n` functions, each comparing an `f64` with an `int` a test bounds.
pub(super) fn bounded_comparisons(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "g{i}(positional n: int, positional y: f64) = \
                 if n >= 0 && n <= {i} {{ y == n }} else {{ false }};\n"
            )
        })
        .collect()
}

/// `n` functions, each casting its parameter under a test that bounds it beyond ±2^53 and
/// within the largest `f64`.
pub(super) fn casts_in_range(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "g{i}(positional n: int) = \
                 if n >= 0 && n <= {} {{ f64(n) }} else {{ 0.0f64 }};\n",
                (num_bigint::BigInt::from(1) << 60) + i
            )
        })
        .collect()
}

/// `n` functions, each casting a `rat` literal that converts.
pub(super) fn casts_of_literals(n: usize) -> String {
    (0..n)
        .map(|i| format!("g{i}(x: int) = f64({i}r);\n"))
        .collect()
}

/// The cast of `1e<k>r` to `f64`.
pub(super) fn cast_of_a_power(k: usize) -> String {
    format!("f(x: int) = f64(1e{k}r);\n")
}

/// `n` casts to `int` that the checker does not prove whole, each rejected with the menu of
/// the six rounding calls: of a parameter `f64` where `i` is even, of the constant
/// `(2i + 1)r/2r` where `i` is odd.
pub(super) fn int_casts_not_whole(n: usize) -> String {
    (0..n)
        .map(|i| {
            if i % 2 == 0 {
                format!("h{i}(positional x: f64) = int(x);\n")
            } else {
                format!("k{i} = int({}r/2r);\n", 2 * i + 1)
            }
        })
        .collect()
}

#[test]
fn many_casts_under_tests_are_accepted() {
    // A small instance of the benchmarks `bench::exact_casts::many_bounded_casts_scale`,
    // `bench::exact_casts::many_casts_of_ints_in_range_scale` and
    // `bench::exact_casts::many_casts_of_literals_scale`.
    for text in [
        bounded_casts(3),
        arms_of_casts(3),
        casts_in_range(3),
        casts_of_literals(3),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    }
    assert_eq!(sig(&casts_in_range(1), "g0"), "int -> f64");
    assert_eq!(sig(&casts_of_literals(3), "g2"), "(x: int) -> f64");
}

#[test]
fn many_bounded_comparisons_are_one_rejection_each() {
    // A small instance of the benchmark `bench::exact_casts::many_bounded_comparisons_scale`.
    let errors = type_errors(&bounded_comparisons(3));
    assert_eq!(errors.len(), 3, "{errors:?}");
    assert!(
        errors.iter().all(|e| e.contains("y == f64(n)")),
        "{errors:?}"
    );
}

#[test]
fn int_casts_not_proved_whole_are_one_rejection_each() {
    // A small instance of the benchmark `bench::exact_casts::many_int_casts_not_whole_scale`.
    let errors = type_errors(&int_casts_not_whole(4));
    assert_eq!(errors.len(), 4, "{errors:?}");
    assert!(
        errors
            .iter()
            .all(|e| e.starts_with("No `int` equals the value: ") && e.contains("Try `round(")),
        "{errors:?}"
    );
}

#[test]
fn a_cast_of_a_large_power_rounds() {
    // A small instance of the benchmark
    // `bench::exact_casts::a_cast_of_a_power_does_not_grow_with_its_exponent`.
    let errors = type_errors(&cast_of_a_power(1000));
    assert_eq!(errors, Vec::<String>::new());
}

#[test]
fn an_int_cast_of_a_number_not_proved_whole_is_rejected() {
    for (src, operand) in [
        ("f(positional r: rat) = int(r);\n", "r"),
        ("f(positional x: f64) = int(x);\n", "x"),
        ("f(positional x: f32) = int(x);\n", "x"),
    ] {
        let errors = type_errors(src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(
            errors[0].starts_with(&format!(
                "No `int` equals the value: `int({operand})`. Try `round({operand})` instead."
            )),
            "{}",
            errors[0]
        );
    }
    // A constant the checker shows whole admits the cast, with no atom.
    assert_eq!(
        sig("f(positional r: rat) = int(6r / 2r);\n", "f"),
        "rat -> int"
    );
}
