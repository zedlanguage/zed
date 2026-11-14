//! FAIL-check-decimal-past-f64-at-rat (found by TEST-complete-lex). DESIGN.md L1.26b: a
//! decimal literal "is read once, straight into the carrier its use fixes: at `rat` it is
//! exact", and "in a class it removes `int` and each format it does not fit, and is the value
//! of each remaining format nearest its own, exact at `rat`". A decimal no float format holds
//! keeps `rat`. Observed: the checker gave such a literal the type `Never`, with no error,
//! and `zedc run` rejected `1e400 + 1r` as an `f64` that rounds to infinity. The checker
//! read the literal only where it was a finite `f64`.

use zed_tests::step_helpers::l01_16_elaboration::{errors, value};
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

#[test]
fn a_decimal_past_every_float_format_is_exact_at_rat() {
    // In range, the literal takes `rat` from `+ 1r`.
    assert_eq!(sig("t() = 1e300 + 1r;", "t"), "() -> rat");
    for t in [
        "t() = 1e400 + 1r;",
        "t() = 1e-400 + 1r;",
        "t() = 1e999999999999 + 1r;",
    ] {
        assert_eq!(type_errors(t), Vec::<String>::new(), "{t}");
        assert_eq!(sig(t, "t"), "() -> rat", "{t}");
    }
    // With no use, the class keeps `rat` alone; it is never `Never` without an error.
    for t in ["t() = 1e400;", "t() = 1e999999999999;"] {
        assert!(
            sig(t, "t") != "() -> Never" || !type_errors(t).is_empty(),
            "{t}: {}",
            sig(t, "t")
        );
    }
}

/// `k` zeros, as a power of ten prints them.
fn zeros(k: usize) -> String {
    "0".repeat(k)
}

#[test]
fn a_decimal_past_f64_holds_its_exact_value_at_rat() {
    let cases = [
        ("a = 1e400 + 1r;\n", format!("1{}1r", zeros(399))),
        ("a = -1e400 + 1r;\n", format!("-{}r", "9".repeat(400))),
        (
            "a = 1e-400 + 1r;\n",
            format!("1{}1r/1{}r", zeros(399), zeros(400)),
        ),
        // A `rat` parameter, a generic one that the literal makes `rat`, and a `/` by a
        // literal that rounds to zero at `f64`, which is no division by zero at `rat`.
        (
            "f(positional x: rat) = x + 1e400;\na = f(1r);\n",
            format!("1{}1r", zeros(399)),
        ),
        (
            "g(positional x) = x * 1e-400;\na = g(2);\n",
            format!("1r/5{}r", zeros(399)),
        ),
        (
            "f(positional x: rat) = x / 1e-400;\na = f(3r);\n",
            format!("3{}r", zeros(400)),
        ),
    ];
    for (src, want) in cases {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "a"), want, "{src}");
    }
    assert_eq!(sig("g(positional x) = x + 1e400;\n", "g"), "(rat) -> rat");
}

const INFINITE: &str = "`1e400` is larger than the largest f64, 1.7976931348623157e308, so as an \
                        f64 it rounds to infinity. Write `1e400r` for the exact rational, or a \
                        number within the range of f64.";

#[test]
fn a_decimal_past_f64_where_f64_is_expected_is_rejected_once_with_the_range() {
    // At an `f64` parameter the checker reports it, and elaboration's report of the same
    // literal is not repeated.
    let e = errors("h(positional z: f64) = z;\na = h(1e400);\n");
    assert_eq!(e.len(), 1, "{e:?}");
    assert!(e[0].starts_with(INFINITE), "{e:?}");
    let e = errors("h(positional z: f64) = z;\na = h(1e-400);\n");
    assert_eq!(e.len(), 1, "{e:?}");
    assert!(
        e[0].starts_with(
            "`1e-400` is not zero, and it lies nearer to zero than to the least positive f64"
        ),
        "{e:?}"
    );
    // A suffix fixes the format, so `rat` is not taken.
    let e = errors("a = 1e400f64 + 1r;\n");
    assert!(e.iter().any(|m| m.starts_with(INFINITE)), "{e:?}");
    // With no use to fix it, the literal stays an `f64`, past its range.
    let e = errors("t() = 1e400;\n");
    assert_eq!(e.len(), 1, "{e:?}");
    assert!(e[0].starts_with(INFINITE), "{e:?}");
}

#[test]
fn an_unfixed_decimal_past_f64_is_offered_no_f64_fix() {
    // The fix writes the literal as a `rat`; `1e400f64` would round to infinity.
    for src in ["y = 1e400;\n", "y = 1e400 + 1e400;\n"] {
        let e = errors(src);
        assert_eq!(e.len(), 1, "{src}: {e:?}");
        assert!(
            e[0].contains("1e400r") && !e[0].contains("1e400f64"),
            "{src}: {e:?}"
        );
    }
    // Under `^` no `rat` form is offered either, and the range is the reason given.
    let e = errors("y = 1e400 ^ 2;\n");
    assert_eq!(e.len(), 1, "{e:?}");
    assert!(e[0].starts_with(INFINITE), "{e:?}");
}
