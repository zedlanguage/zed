//! The references read `int` and `f64` text as DESIGN.md step L1.18 says (row
//! FAIL-ref-text-reading, found by TEST-complete-m0): "`int(s)` reads an optional `-` and decimal
//! digits ... `f64(s)` reads an optional `-` and then `inf`, `nan`, or digits with an optional
//! fraction and exponent ... In all three a digit is one of the ASCII digits `0` to `9` ... so
//! `int("٤٢")` ... is `#invalid`, as are fullwidth digits and a text that mixes ASCII and
//! Arabic-Indic digits, such as `"4٢"` ... Any other text is `#invalid`, so `+5`, `.5` and
//! `infinity` are." The readers (zed/corpus/ref/src/zedrt.rs) used to read a `+`, white space
//! around the text, `_` between digits, digits of any script, `.5` and `infinity`. The float
//! numeral is the one the compiler reads (`zed_kernel::words::float_text`), and a finite text
//! beyond the float range is `#overflow` there (`words.rs`, `Prim::CastF64`).

use zed_corpus_ref::zedrt::{parse_float, parse_int, try_parse_float, try_parse_int};

#[test]
fn the_references_read_int_and_float_text_as_design_l1_18_says() {
    // Named in DESIGN L1.18 itself.
    for s in ["+5", "٤٢", "4٢", "４２"] {
        assert_eq!(try_parse_int(s), None, "int({s:?}) is #invalid");
    }
    for s in ["+5", ".5", "infinity", "٤٢", "4٢", "４２"] {
        assert_eq!(try_parse_float(s), None, "f64({s:?}) is #invalid");
    }
    // "Any other text is #invalid": white space and digit marks are not in the rule.
    for s in [" 5", "5 ", "1_000", "\u{2003}5"] {
        assert_eq!(try_parse_int(s), None, "int({s:?}) is #invalid");
        assert_eq!(try_parse_float(s), None, "f64({s:?}) is #invalid");
    }
    // What the rule does read.
    assert_eq!(try_parse_int("-007"), Some((-7).into()));
    assert_eq!(
        try_parse_float("-0").map(f64::to_bits),
        Some((-0.0f64).to_bits())
    );
}

/// The neighbors of the int rule: one digit, a lone or doubled sign, a sign after the digits,
/// a sign after white space, a float text, and the error `parse_int` gives.
#[test]
fn int_reads_an_optional_minus_and_ascii_digits_only() {
    for (s, n) in [("0", 0), ("-0", 0), ("7", 7), ("-1", -1), ("0042", 42)] {
        assert_eq!(try_parse_int(s), Some(n.into()), "int({s:?})");
    }
    for s in [
        "", "-", "+", "--1", "-+1", "+-1", "1-", "1+", "\t1", "1\n", " -1", "- 1", "1 000", "1.0",
        "1e3", "0x10", "١", "1٠", "-٤٢", "１", "\u{a0}1",
    ] {
        assert_eq!(try_parse_int(s), None, "int({s:?}) is #invalid");
        assert_eq!(parse_int(s), Err(format!("invalid int: {s}")));
    }
}

/// The neighbors of the f64 rule: the forms `String` writes (fraction, exponent, negative
/// exponent, the special values) read; the forms it does not write (a point at either end, a
/// capital or signed exponent, other spellings of the special values) are `#invalid`; past the
/// largest finite float is `#overflow`, below the smallest subnormal rounds to a zero of the
/// text's sign.
#[test]
fn f64_reads_what_string_writes_for_a_float() {
    let bits = |s: &str| try_parse_float(s).map(f64::to_bits);
    for (s, x) in [
        ("0", 0.0),
        ("3", 3.0),
        ("-0.5", -0.5),
        ("0.25", 0.25),
        ("1.0e300", 1.0e300),
        ("1e-7", 1e-7),
        ("-2.5e-3", -2.5e-3),
        ("007.50", 7.5),
        ("inf", f64::INFINITY),
        ("-inf", f64::NEG_INFINITY),
        ("1.7976931348623157e308", f64::MAX),
        ("1e-400", 0.0),
        ("-1e-400", -0.0),
    ] {
        assert_eq!(bits(s), Some(x.to_bits()), "f64({s:?})");
    }
    for s in ["nan", "-nan"] {
        assert!(try_parse_float(s).is_some_and(f64::is_nan), "f64({s:?})");
    }
    for s in [
        "",
        "-",
        "+",
        ".",
        "5.",
        "-.5",
        "1.e5",
        "1E5",
        "1e+5",
        "1e",
        "e5",
        "1e5.0",
        "1.2.3",
        "Inf",
        "INF",
        "NaN",
        "+inf",
        "-infinity",
        "+nan",
        "inf ",
        " nan",
        "1 e5",
        "٤.٥",
        "1.0_0",
        "--1",
    ] {
        assert_eq!(try_parse_float(s), None, "f64({s:?}) is #invalid");
        assert_eq!(parse_float(s), Err(format!("invalid float: {s}")));
    }
    for s in ["1e400", "-1e400", "2e308", "1.8e308"] {
        assert_eq!(try_parse_float(s), None, "f64({s:?}) is #overflow");
    }
}
