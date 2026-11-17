//! A decimal literal that no use fixes is `f64` (DESIGN.md step L1.26b, author decision
//! 2026-11-12; plan row LIT-unfixed-decimal-f64), and a literal component of a tuple passed to
//! `min` or `max` follows the carrier of the component beside it (DESIGN.md sec:reduction,
//! item 5; plan row MINMAX-literal-follow). Only a `/` of integer literals alone stays
//! rejected, with the exact fixes first. Each test is one of DESIGN's examples.

use zed_tests::step_helpers::l01_16_elaboration::{checked, errors, value};

/// The value of `name` in `src`, which is accepted with no warning.
fn quiet(src: &str, name: &str) -> String {
    let warnings = checked(src).info.warnings;
    assert!(warnings.is_empty(), "{src}: {warnings:?}");
    value(src, name)
}

#[test]
fn a_decimal_that_nothing_fixes_is_an_f64_with_no_warning() {
    assert_eq!(quiet("y = 0.1;\n", "y"), "0.1");
    assert_eq!(quiet("y = 0.5 * 2;\n", "y"), "1.0");
    assert_eq!(quiet("y = (0.5, \"a\");\n", "y"), "(0.5, \"a\")");
    assert_eq!(quiet("inc(x) = x + 1;\ny = inc(x: 2.5);\n", "y"), "3.5");
    assert_eq!(quiet("y = 1 == 1.0;\n", "y"), "true");
}

#[test]
fn a_decimal_compared_with_an_int_operation_on_literals_takes_f64_in_each_place() {
    // DESIGN.md L1.26a and L1.26b make `2^(1 + 1) == 0.5` the `f64` comparison, `false`: the
    // decimal takes `f64` and the operation follows it (row LIT-f64-op-meets-int-op; this
    // zedc once rejected it with "A decimal literal is never an `int`").
    for (src, want) in [
        ("y = 2^(1 + 1) == 0.5;\n", "false"),
        ("y = 0.5 == 2^(1 + 1);\n", "false"),
        ("y = 2^(1 + 1) != 0.5;\n", "true"),
        ("g() = 2^(1 + 1) == 0.5;\ny = g();\n", "false"),
        ("g() = 4.0 == 2^(1 + 1);\ny = g();\n", "true"),
    ] {
        assert_eq!(value(src, "y"), want, "{src}");
    }
}

#[test]
fn a_decimal_base_at_an_int_exponent_and_a_decimal_argument() {
    // DESIGN.md L1.17 makes `0.5 ^ n` with `n : int` an `f64` alone. zedc has no arrow
    // `f64 ^ int` yet, so the base takes the exact `rat` (row POW-domains, item 4).
    let f = "f(positional n: int) = 0.5 ^ n;\n";
    assert_eq!(quiet(&format!("{f}y = f(-2);\n"), "y"), "4r");
    assert_eq!(quiet(&format!("{f}y = f(3);\n"), "y"), "1r/8r");
    assert_eq!(quiet("y = abs(0.5);\n", "y"), "0.5");
    assert_eq!(quiet("y = min(0.5, 2);\n", "y"), "0.5");
}

#[test]
fn a_decimal_exponent_and_a_decimal_argument_take_f64() {
    assert_eq!(value("g() = 2^-1.0;\ny = g();\n", "y"), "0.5");
    let src = "f(positional n) = 2^n;\ny = f(2.0);\nz = f(3);\n";
    assert_eq!(value(src, "y"), "4.0");
    assert_eq!(value(src, "z"), "8");
}

#[test]
fn a_division_of_integer_literals_alone_is_rejected_with_the_exact_fixes_first() {
    // DESIGN's menus also list `half: rat = 1 / 2;` and `half: f64 = 1 / 2;`. This zedc does
    // not compile a binding with a declared type, so it leaves them out: row
    // LIT-declared-fix-call-arg.
    assert_eq!(
        errors("half = 1 / 2;\n"),
        [
            "Nothing gives the integer literals a carrier, and `/` has none at `int`: \
             `half = 1 / 2`. Try `half = 1r / 2` instead.\n  fixes, each checked here:\n    \
             half = 1r / 2;        half is 1r/2r\n    \
             half = 1.0 / 2;       half is 0.5\n    \
             half = f64(1) / 2;    half is 0.5 [1 / 2]"
        ],
    );
    assert_eq!(
        errors("q = (1 + 2) / (3 + 4);\n"),
        [
            "Nothing gives the integer literals a carrier, and `/` has none at `int`: \
             `q = (1 + 2) / (3 + 4)`. Try `q = (1r + 2) / (3 + 4)` instead.\n  fixes, each \
             checked here:\n    \
             q = (1r + 2) / (3 + 4);        q is 3r/7r\n    \
             q = (1.0 + 2) / (3 + 4);       q is 0.42857142857142855\n    \
             q = (f64(1) + 2) / (3 + 4);    q is 0.42857142857142855 [(1 + 2) / (3 + 4)]"
        ],
    );
}

#[test]
fn an_integer_literal_at_a_generic_division_is_rejected_with_the_exact_fix_first() {
    // The `f64` fix is the literal written as a decimal with no suffix, which takes `f64`
    // since nothing fixes it (DESIGN.md sec:diagnostics, "The value a fix names"). DESIGN's
    // menu also lists `y: rat = half(x: 1);` and `y: f64 = half(x: 1);`, which zedc does not
    // yet offer at a call argument: row LIT-declared-fix-call-arg.
    assert_eq!(
        errors("half(x) = x / 2;\ny = half(x: 1);\n"),
        [
            "Nothing gives the literal `1` a carrier. Try `y = half(x: 1r)` instead.\n  fixes, \
             each checked here:\n    \
             y = half(x: 1r);     the literal is then exactly 1, a rat\n    \
             y = half(x: 1.0);    the literal is then the f64 1.0 [1]"
        ],
    );
    // In an operation on literals the `f64` fix keeps its suffix.
    assert_eq!(
        errors("f(positional p0) = 1;\ny = f(1 / 2);\n"),
        [
            "Nothing gives the literal `1` a carrier. Try `y = f(1r / 2)` instead.\n  fixes, \
             each checked here:\n    \
             y = f(1r / 2);        the literal is then exactly 1, a rat\n    \
             y = f(1.0f64 / 2);    the literal is then the f64 1.0 [1]"
        ],
    );
}

#[test]
fn a_decimal_branch_a_call_returns_is_an_f64() {
    let g = "g(positional c: bool) = if c { 1 } else { 2.5 };\n";
    assert_eq!(value(&format!("{g}y = g(true);\n"), "y"), "1");
    assert_eq!(value(&format!("{g}y = g(false);\n"), "y"), "2.5");
    assert_eq!(
        value(
            &format!("{g}k(positional c: bool) = g(c);\ny = k(false);\n"),
            "y"
        ),
        "2.5"
    );
}

#[test]
fn a_decimal_component_of_a_tuple_argument_is_an_f64() {
    let h = "h(positional p) = if p[0] < 5 { p[0] } else { 0 };\n";
    assert_eq!(quiet(&format!("{h}r = h((1.5, 2));\n"), "r"), "1.5");
}

#[test]
fn a_literal_component_beside_a_decimal_in_min_follows_it() {
    assert_eq!(quiet("y = min((1, 2.0), (1, 3));\n", "y"), "(1, 2.0)");
    assert_eq!(quiet("y = max((1, 2.0), (1, 3));\n", "y"), "(1, 3.0)");
    assert_eq!(quiet("t = (1, 9);\ny = min(t, (2, 0));\n", "y"), "(1, 9)");
    let g = "g(positional a) = min(a, (1, 2));\n";
    assert_eq!(quiet(&format!("{g}y = g((0, 5));\n"), "y"), "(0, 5)");
}

#[test]
fn min_of_tuples_that_cannot_be_ordered_stays_refused() {
    for src in [
        "y = min((1, 2), (1, 2, 3));\n",
        "y = min((1, \"a\"), (1, \"b\"));\n",
        "y = min((1, 2), 3);\n",
    ] {
        assert!(!errors(src).is_empty(), "{src}");
    }
}
