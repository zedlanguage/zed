//! Literals at an `f32` use (rows LIT-formats-decimal-past-f32-param and
//! LIT-formats-rat-suffix-beside-f32, parts of LIT-formats; found by TEST-complete-literals).
//!
//! DESIGN.md L1.26b: a decimal literal is read once, straight into the carrier its use fixes, and
//! one outside the range of that format is rejected for its range, as `1e39f32` and `1e400` at
//! `f64` are. DESIGN.md sec:diagnostics, row "Two numeric values with no common carrier": "a
//! forced literal is offered the same literal without its suffix where that literal takes the
//! other carrier exactly".

use zed_tests::step_helpers::l01_16_elaboration::errors;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

const LARGE: &str =
    "`1e39` is larger than the largest f32, 3.4028235e38, so as an f32 it rounds to infinity";
const SMALL: &str =
    "`1e-50` is not zero, and it lies nearer to zero than to the least positive f32";

/// `src` is rejected with one message, which holds each of `parts` and none of `not`.
fn rejected(src: &str, parts: &[&str], not: &[&str]) {
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}\n{errors:?}");
    for p in parts {
        assert!(errors[0].contains(p), "{src}\n{:?} lacks {p:?}", errors[0]);
    }
    for p in not {
        assert!(!errors[0].contains(p), "{src}\n{:?} holds {p:?}", errors[0]);
    }
}

/// A decimal can be an `f32`: one past the range of `f32` at an `f32` parameter or beside an
/// `f32` operand is rejected for its range, never as "never an `f32`".
#[test]
fn a_decimal_past_the_range_of_f32_is_rejected_for_its_range_at_an_f32_use() {
    // The controls: the suffixed forms give the range messages, at elaboration.
    let e = errors("y = 1e39f32;\n");
    assert!(e.iter().any(|m| m.contains(LARGE)), "{e:?}");
    let e = errors("y = 1e-50f32;\n");
    assert!(e.iter().any(|m| m.contains(SMALL)), "{e:?}");
    let never = ["never an `f32`"];
    rejected(
        "s(positional x: f32) = x;\ny = s(1e39);\n",
        &[LARGE],
        &never,
    );
    rejected("f(x: f32) = x + 1e39;\n", &[LARGE], &never);
    rejected(
        "s(positional x: f32) = x;\ny = s(1e-50);\n",
        &[SMALL],
        &never,
    );
    rejected("f(x: f32) = x * 1e-50;\n", &[SMALL], &never);
    // Past the range of `f64` too: still the range of `f32`, the format the use fixes.
    rejected(
        "f(x: f32) = x + 1e400;\n",
        &["`1e400` is larger than the largest f32"],
        &never,
    );
}

/// One decimal literal of `n + 1` digits, `10…0.0`, at a parameter of type `f32`: past the
/// range of `f32` for `n >= 39`, so rejected for its range, its digits read once at `f32`.
pub(super) fn long_past_f32(n: usize) -> String {
    format!(
        "id(positional v: f32) = v;\nx = id(1{}.0);\n",
        "0".repeat(n)
    )
}

/// The small instance of `bench::f32_literals`: a long literal past the range of `f32` gives
/// the range message once.
#[test]
fn a_long_decimal_past_the_range_of_f32_is_rejected_for_its_range() {
    let errors = type_errors(&long_past_f32(60));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("is larger than the largest f32"),
        "{errors:?}"
    );
}

/// A decimal within the range of `f32` at an `f32` use is still accepted: the range message is
/// given only where the format rounds the value to infinity or to zero.
#[test]
fn a_decimal_within_the_range_of_f32_is_taken_at_an_f32_use() {
    for src in [
        "s(positional x: f32) = x;\ny = s(3e38);\n",
        "f(x: f32) = x + 1e-40;\n",
        "f(x: f32) = x * 0.1;\n",
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    }
}

/// A rat literal beside an `f32` is offered the literal without its suffix where that literal
/// is exactly an `f32`, as beside an `f64`, and with no `f64` suffix.
#[test]
fn a_rat_literal_beside_an_f32_is_offered_the_literal_without_its_suffix() {
    // The control at `f64`.
    rejected(
        "f(x: f64) = x + 1r;\n",
        &["Try `f(x: f64) = x + 1.0` instead."],
        &[],
    );
    let no_f64 = ["f64`"];
    rejected(
        "f(x: f32) = x + 1r;\n",
        &["Try `f(x: f32) = x + 1.0` instead."],
        &no_f64,
    );
    rejected(
        "f(x: f32) = x + 1.0r;\n",
        &["Try `f(x: f32) = x + 1.0` instead."],
        &no_f64,
    );
    rejected(
        "f(x: f32) = x + 0.5r;\n",
        &["Try `f(x: f32) = x + 0.5` instead."],
        &no_f64,
    );
}

/// Where both `f32` and `f64` are taken, the `f64` and `f32` forms of a rat literal write the
/// same decimal, which is offered once: the decimal alone takes neither carrier there, so the
/// `f64` form is written with its suffix, and the `f32` form adds nothing (a control: the same
/// message as before the `f32` form).
#[test]
fn a_rat_literal_where_f32_and_f64_are_taken_is_offered_its_decimal_once() {
    let src = "g(positional x: f32 | f64) = x;\ny = g(1r);\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("Try `g(1.0f64)` instead."), "{errors:?}");
    assert_eq!(errors[0].matches("g(1.0").count(), 1, "{errors:?}");
}

/// Row CHECK-rat-forms-f32-other-messages: the `f32` form of `rat_forms` (row
/// LIT-formats-rat-suffix-beside-f32) reaches every message that offers a rat literal's other
/// forms, not only `+`. Run before and after that change on 25 programs, these four messages
/// changed, each from no offer to the one checked here, and nothing else did: an ordering
/// comparison, a product, and a positional and a named argument of an `f32` parameter. A rat
/// literal no `f32` holds exactly, `0.1r` or `16777217r` (2^24 + 1), is still offered nothing,
/// and `==` and `!=` beside an `f32` keep their "always `false`" and "always `true`" messages.
#[test]
fn a_rat_literal_at_every_f32_use_is_offered_the_literal_without_its_suffix() {
    let no_f64 = ["f64`"];
    for (src, repair) in [
        (
            "f(x: f32) = x < 1r;\n",
            "Try `f(x: f32) = x < 1.0` instead.",
        ),
        (
            "f(x: f32) = x * 2.5r;\n",
            "Try `f(x: f32) = x * 2.5` instead.",
        ),
        (
            "g(positional x: f32) = x;\ny = g(0.5_0r);\n",
            "Try `g(0.5_0)` instead.",
        ),
        (
            "g(x: f32) = x;\ny = g(x: 1_000r);\n",
            "Try `g(x: 1_000.0)` instead.",
        ),
    ] {
        rejected(src, &[repair], &no_f64);
    }
    // Not exactly an `f32`: no offer, as before.
    for src in [
        "g(x: f32) = x;\ny = g(x: 0.1r);\n",
        "f(x: f32) = x - 16777217r;\n",
    ] {
        rejected(src, &[], &["Try"]);
    }
    rejected(
        "f(x: f32) = x == 0.5r;\n",
        &["is always `false`. Try `false` instead."],
        &[],
    );
}
