//! Items ALWAYS-atom-div, ALWAYS-atom-cast and ALWAYS-atom-lookup: an operation that gives
//! only an exceptional atom for every value that reaches it is rejected with the row
//! "Operation that always fails" (DESIGN.md sec:failure): "Something which can never do
//! anything useful (e.g. can only ever produce `#outOfBounds` for any input value) should be a
//! compile-time error, and not just give an atom result ... However, if an input can produce
//! non-atom values for some inputs and not for other inputs, then that is not a compile-time
//! error". A division whose divisor is always 0, a cast of a literal that never converts, and a
//! read whose key shares no value with the map's keys (R11, row "Key outside the permission
//! bound") are rejected; the same operations on a parameter keep their atom.

use zed_tests::scaling;

use super::scaling::resolved;
use super::{sig, type_errors};

/// The message for `op` on the divisor `at`, always 0 for `reason`, in a function of `kind`.
fn div_zero(op: &str, reason: &str, kind: &str, at: &str) -> String {
    format!(
        "`{op}` here always fails with `#divByZero`: {reason}, so no value that reaches it gives \
         {kind}. [{at}]"
    )
}

#[test]
fn a_divisor_that_is_always_zero_is_rejected() {
    let literal = "its divisor is the literal 0";
    let folded = "its divisor is built from constants and works out to 0";
    let cases = [
        (
            "f(x: int) = x div 0;",
            div_zero("div", literal, "an int", "x div 0"),
        ),
        (
            "f(x: int) = x mod 0;",
            div_zero("mod", literal, "an int", "x mod 0"),
        ),
        (
            "f(x: int) = x div -0;",
            div_zero("div", "its divisor is the literal -0", "an int", "x div -0"),
        ),
        (
            "f(x: rat) = x / 0r;",
            div_zero("/", "its divisor is the literal 0r", "a rat", "x / 0r"),
        ),
        (
            "f(x: rat) = x / 0;",
            div_zero("/", literal, "a rat", "x / 0"),
        ),
        (
            "a = 10 div 0;",
            div_zero("div", literal, "an int", "10 div 0"),
        ),
        (
            "f(x: int) = x div (1 - 1);",
            div_zero("div", folded, "an int", "x div (1 - 1)"),
        ),
        (
            "f(x: int) = { z = 0; x div z };",
            div_zero("div", folded, "an int", "x div z"),
        ),
        (
            "z = 0;\nf(x: int) = x div z;",
            div_zero("div", folded, "an int", "x div z"),
        ),
        (
            "f(x: int) = x div (x - x);",
            div_zero(
                "div",
                "its divisor adds `x` as often as it subtracts it, which makes it 0 for every value \
                 of `x`",
                "an int",
                "x div (x - x)",
            ),
        ),
        (
            "f(x: int, y: int) = x div (y + 2 - y - 2);",
            div_zero(
                "div",
                "its divisor adds `y` as often as it subtracts it, and its constants add up to 0, \
                 which makes it 0 for every value of `y`",
                "an int",
                "x div (y + 2 - y - 2)",
            ),
        ),
        (
            "f(x: int) = if x == 0 { 1 div x } else { x };",
            div_zero(
                "div",
                "the tests around it leave its divisor only the value 0",
                "an int",
                "1 div x",
            ),
        ),
    ];
    for (src, message) in cases {
        assert_eq!(type_errors(src), [message], "{src}");
    }
}

#[test]
fn a_divisor_that_may_be_other_than_zero_keeps_its_atom() {
    let cases = [
        (
            "f(x: int, y: int) = x div y;",
            "(x: int, y: int) -> int | #divByZero",
        ),
        (
            "f(x: int, y: int) = x mod y;",
            "(x: int, y: int) -> int | #divByZero",
        ),
        (
            "f(x: rat, y: rat) = x / y;",
            "(x: rat, y: rat) -> rat | #divByZero",
        ),
        (
            "f(x: int) = x div (x - x + 1);",
            "(x: int) -> int | #divByZero",
        ),
        // A divisor that cannot be 0 gives no atom at all.
        ("f(x: int) = x div 2;", "(x: int) -> int"),
    ];
    for (src, want) in cases {
        assert!(type_errors(src).is_empty(), "{src}");
        assert_eq!(sig(src, "f"), want, "{src}");
    }
    // A float division by 0 is IEEE (`inf` or `NaN`), not a failure, so it is not judged here.
    assert!(type_errors("f(x: f64) = x / 0.0f64;").is_empty());
}

/// The message for the cast `w` of the literal `lit`, which gives `atom`.
fn cast_fails(w: &str, lit: &str, atom: &str) -> String {
    format!(
        "`{w}` here always fails: its operand `{lit}` gives `{atom}`, so this call never gives a \
         value. [{w}({lit})]"
    )
}

#[test]
fn a_cast_of_a_literal_that_never_converts_is_rejected() {
    let cases = [
        (
            "a = int(\"n/a\");",
            cast_fails("int", "\"n/a\"", "#invalid"),
        ),
        (
            "f(s: String) = int(\"n/a\");",
            cast_fails("int", "\"n/a\"", "#invalid"),
        ),
        ("a = int(2.5f64);", cast_fails("int", "2.5f64", "#inexact")),
        (
            "a = int(-2.5f64);",
            cast_fails("int", "-2.5f64", "#inexact"),
        ),
        (
            "a = f64(9007199254740993r);",
            cast_fails("f64", "9007199254740993r", "#inexact"),
        ),
    ];
    for (src, message) in cases {
        assert_eq!(type_errors(src), [message], "{src}");
    }
    // A name bound to a literal has the literal's type, so its cast is judged the same way.
    let named = "`int` here always fails: its operand `\"n/a\"` gives `#invalid`, so this call \
                 never gives a value. [int(s)]";
    for src in [
        "s = \"n/a\";\nf(x: int) = int(s);",
        "f(x: int) = { s = \"n/a\"; int(s) };",
    ] {
        assert_eq!(type_errors(src), [named], "{src}");
    }
}

#[test]
fn a_cast_that_may_convert_keeps_its_atom() {
    let cases = [
        ("f(s: String) = int(s);", "(s: String) -> int | #invalid"),
        (
            "f(x: f64) = int(x);",
            "(x: f64) -> int | #inexact | #invalid",
        ),
    ];
    for (src, want) in cases {
        assert!(type_errors(src).is_empty(), "{src}");
        assert_eq!(sig(src, "f"), want, "{src}");
    }
}

/// Item CAST-literal-exact: a literal's domain is the one value it holds (DESIGN.md
/// sec:failure), so a word applied to a literal that converts gives none of its atoms, and its
/// result lists none.
#[test]
fn a_cast_of_a_literal_that_converts_gives_no_atom() {
    let cases = [
        ("f(x: int) = int(\"12\");", "(x: int) -> int"),
        ("f(x: int) = f64(3r);", "(x: int) -> f64"),
        ("f(x: int) = f32(3r);", "(x: int) -> f32"),
        ("f(x: int) = f64(-0.5r);", "(x: int) -> f64"),
        ("f(x: int) = int(2.0f64);", "(x: int) -> int"),
        ("f(x: int) = rat(\"1/3\");", "(x: int) -> rat"),
        // A name bound to a literal has the literal's type (A63).
        ("r = 3r;\nf(x: int) = f64(r);", "(x: int) -> f64"),
        ("f(x: int) = { r = 3r; f64(r) };", "(x: int) -> f64"),
    ];
    for (src, want) in cases {
        assert!(type_errors(src).is_empty(), "{src}");
        assert_eq!(sig(src, "f"), want, "{src}");
    }
}

#[test]
fn a_key_that_shares_no_value_with_the_keys_is_rejected() {
    let cases = [
        (
            "f(m: #a -> int) = m[#b];",
            "this read can never find its key: the key is `#b` and the map's keys are `#a`, \
             which share no value, so the read can only give `#notFound`. [m[#b]]",
        ),
        (
            "f(m: int .. int | String -> bool, k: bool) = m[k];",
            "this read can never find its key: the key is `bool` and the map's keys are \
             `int | String`, which share no value, so the read can only give `#notFound`. [m[k]]",
        ),
    ];
    for (src, message) in cases {
        assert_eq!(type_errors(src), [message], "{src}");
    }
}

#[test]
fn a_key_that_may_be_present_keeps_its_atom() {
    assert_eq!(
        sig("f(m: int ->? String, k: int) = m[k];", "f"),
        "(m: int ->? String, k: int) -> String | #notFound"
    );
    assert_eq!(
        sig("f(m: #a .. #a | #b -> int, k: #a | #b) = m[k];", "f"),
        "type T1 = #a | #b;\n(m: #a .. T1 -> int, k: T1) -> int | #notFound"
    );
}

/// A function of `n` parameters whose divisor adds each parameter and the constant 1 and
/// subtracts them again, so is always 0.
fn cancelling(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("x{i}: int")).collect();
    let terms: String = (0..n).map(|i| format!(" + x{i} + 1 - x{i} - 1")).collect();
    format!("f({}) = 1 div (0{terms});\n", params.join(", "))
}

#[test]
fn a_long_divisor_that_cancels_scales() {
    // One pass over the divisor's sums, with a count for each name, and one balanced sum of
    // the constants.
    assert_eq!(type_errors(&cancelling(3)).len(), 1);
    let units = resolved(2000, cancelling);
    scaling::check("a divisor of n terms that cancel", 2000, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
    });
}

/// A function of `n` divisions, each divisor `x + 1 +` the next division.
fn nested(n: usize) -> String {
    let open: String = (0..n).map(|_| "x div (x + 1 + ").collect();
    format!("f(x: int) = {open}x{};\n", ")".repeat(n))
}

#[test]
fn nested_divisions_scale() {
    // The sums of each divisor end at the division inside it, so no divisor is read twice.
    assert!(type_errors(&nested(3)).is_empty());
    let units = resolved(2000, nested);
    scaling::check("n divisions nested in their divisors", 2000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
