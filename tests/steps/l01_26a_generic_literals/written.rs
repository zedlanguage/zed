//! Item LIT-written-spelling: a message quotes a literal as the program writes it, with the
//! `_` that separate its digits, its base prefix, its exponent and its suffix (DESIGN.md
//! sec:diagnostics: a message uses the program's words). The lexer drops the `_`, so each
//! literal here is written with them, and each message is compared whole.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// The rendered rejection of `src`, with its notes.
fn rejected(src: &str) -> String {
    match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e,
    }
}

const DIVIDES: &str = "Nothing gives the integer literals a carrier, and `/` has none at `int`";

#[test]
fn a_decimal_with_underscores_is_quoted_with_them() {
    assert_eq!(
        type_errors("y = 1_000.5;\n"),
        [String::from(
            "Nothing gives the literal `1_000.5` a carrier. Try `y = 1_000.5f64` instead.\n  \
             fixes, each checked here:\n    y = 1_000.5f64;    y is 1000.5\n    y = 1_000.5r;      \
             y is 2001r/2r [1_000.5]"
        )]
    );
}

#[test]
fn a_negative_literal_is_quoted_with_its_sign_and_underscores() {
    assert_eq!(
        type_errors("y = -1_000.5;\n"),
        [String::from(
            "Nothing gives the literal `-1_000.5` a carrier. Try `y = -1_000.5f64` instead.\n  \
             fixes, each checked here:\n    y = -1_000.5f64;    y is -1000.5\n    y = \
             -1_000.5r;      y is -2001r/2r [-1_000.5]"
        )]
    );
}

#[test]
fn an_exponent_is_quoted_as_written() {
    assert_eq!(
        type_errors("y = 2.5e-3;\n"),
        [String::from(
            "Nothing gives the literal `2.5e-3` a carrier. Try `y = 2.5e-3f64` instead.\n  \
             fixes, each checked here:\n    y = 2.5e-3f64;    y is 0.0025\n    y = 2.5e-3r;      y \
             is 1r/400r [2.5e-3]"
        )]
    );
    assert_eq!(
        type_errors("y = 1_0e1_0;\n"),
        [String::from(
            "Nothing gives the literal `1_0e1_0` a carrier. Try `y = 1_0e1_0f64` instead.\n  \
             fixes, each checked here:\n    y = 1_0e1_0f64;    y is 100000000000.0\n    y = \
             1_0e1_0r;      y is 100000000000r [1_0e1_0]"
        )]
    );
    assert_eq!(
        type_errors("f(x: int) = x + 1e3;\n"),
        [
            "A decimal literal is never an `int`: `x : int + 1e3`. Try `f(x: int) = rat(x) + 1e3` \
             instead.\n  fixes, each checked here:\n    f(x: int) = rat(x) + 1e3;    x is cast to \
             rat, and `+` takes two rat [1e3]"
        ]
    );
}

#[test]
fn a_suffixed_literal_is_quoted_with_its_suffix() {
    assert_eq!(
        type_errors("f(x: int) = x + 0.5f64;\n"),
        [
            "The suffix makes the literal `0.5f64` an `f64`, never `int`. No fix is offered: each one the \
          checker tried is rejected too. [0.5f64]"
        ]
    );
    // Without its suffix `2.0f64` is `2.0`, which is never an `int` either, so nothing is
    // offered, `2` least of all: the suffix says the program means an `f64` (DESIGN.md
    // sec:diagnostics, row "Two numeric values with no common carrier").
    assert_eq!(
        type_errors("f(x: int) = x + 2.0f64;\n"),
        [
            "The suffix makes the literal `2.0f64` an `f64`, never `int`. No fix is offered: each \
             one the checker tried is rejected too. [2.0f64]"
        ]
    );
    // The fix writes the digits as the program does, and names the number by them.
    assert_eq!(
        type_errors("f(x: rat) = x + 1_000.5f64;\n"),
        [
            "The suffix makes the literal `1_000.5f64` an `f64`, never `rat`. Try `f(x: rat) = x + 1_000.5` instead.\n  fixes, \
             each checked here:\n    f(x: rat) = x + 1_000.5;     the literal is then exactly \
             1_000.5, a rat\n    f(x: rat) = x + 1_000.5r;    the literal is then exactly \
             1_000.5, a rat [1_000.5f64]"
        ]
    );
}

#[test]
fn the_integer_fix_of_a_decimal_keeps_its_underscores() {
    assert_eq!(
        type_errors("f(x: int) = x * -1_000.0;\n"),
        [
            "A decimal literal is never an `int`: `x : int * -1_000.0`. Try `f(x: int) = x * \
             -1_000` instead.\n  fixes, each checked here:\n    f(x: int) = x * -1_000;           \
             -1_000 takes the int of x\n    f(x: int) = rat(x) * -1_000.0;    x is cast to rat, \
             and `*` takes two rat [-1_000.0]"
        ]
    );
}

#[test]
fn a_division_of_integer_literals_quotes_them_as_written() {
    assert_eq!(
        type_errors("half = 1_000 / 2_0;\n"),
        [format!(
            "{DIVIDES}: `half = 1_000 / 2_0`. Try `half = 1_000.0f64 / 2_0` instead.\n  fixes, each \
             checked here:\n    half = 1_000.0f64 / 2_0;    half is 50.0\n    half = 1_000r / \
             2_0;        half is 50r\n    half = f64(1_000) / 2_0;    half is 50.0 [1_000 / 2_0]"
        )]
    );
}

#[test]
fn a_literal_in_another_base_is_quoted_with_its_prefix_and_underscores() {
    // `_` stands only between two digits, so `0x_ff` is no literal: `0xF_F` is.
    assert_eq!(
        type_errors("half = -0xF_F / 2;\n"),
        [format!(
            "{DIVIDES}: `half = -0xF_F / 2`. Try `half = -f64(0xF_F) / 2` instead.\n  fixes, each \
             checked here:\n    half = -f64(0xF_F) / 2;    half is -127.5\n    half = -rat(0xF_F) \
             / 2;    half is -255r/2r [-0xF_F / 2]"
        )]
    );
    assert_eq!(
        type_errors("y = 0b1_0 / 2;\n"),
        [format!(
            "{DIVIDES}: `y = 0b1_0 / 2`. Try `y = f64(0b1_0) / 2` instead.\n  fixes, each checked \
             here:\n    y = f64(0b1_0) / 2;    y is 1.0\n    y = rat(0b1_0) / 2;    y is 1r [0b1_0 \
             / 2]"
        )]
    );
    assert_eq!(
        type_errors("f(x: String) = x == 0xF_F;\n"),
        [
            "No number equals a `String`: `x : String == 0xF_F` always gives the same answer. Try \
             `f(x: String) = x == \"0xF_F\"` instead.\n  fixes, each checked here:\n    f(x: \
             String) = x == \"0xF_F\";    compares the text [0xF_F]"
        ]
    );
}

#[test]
fn the_text_fix_of_a_number_compared_with_a_string_is_the_literal_as_written() {
    assert_eq!(
        type_errors("f(x: String) = x == 1_000;\n"),
        [
            "No number equals a `String`: `x : String == 1_000` always gives the same answer. Try \
             `f(x: String) = x == \"1_000\"` instead.\n  fixes, each checked here:\n    f(x: \
             String) = x == \"1_000\";    compares the text [1_000]"
        ]
    );
    assert_eq!(
        type_errors("f(x: (int, String)) = x == (1, 2_0);\n"),
        [
            "No number equals a `String`: `2_0` compared by `==` with a component of `x` always \
             gives the same answer. Try `f(x: (int, String)) = x == (1, \"2_0\")` instead.\n  fixes, each checked \
             here:\n    f(x: (int, String)) = x == (1, \"2_0\");    compares the text [2_0]"
        ]
    );
}

#[test]
fn a_literal_in_parentheses_is_quoted_without_them() {
    assert_eq!(
        type_errors("y = -(1_000.5);\n"),
        [String::from(
            "Nothing gives the literal `-1_000.5` a carrier. Try `y = -1_000.5f64` instead.\n  \
             fixes, each checked here:\n    y = -1_000.5f64;    y is -1000.5\n    y = \
             -1_000.5r;      y is -2001r/2r [-(1_000.5)]"
        )]
    );
    assert_eq!(
        type_errors("f(x: String) = x == -(1_000r);\n"),
        [
            "No value is both `String` and `rat`: `x : String == -1_000r : rat` is always \
             `false`. Try `false` instead. [x == -(1_000r)]"
        ]
    );
    // A type that holds the literal's value spells it as the program does.
    assert_eq!(
        type_errors("f(x: int) = x / (0_0);\n"),
        ["`/` does not take (int, 0_0): no arrow of `/` takes these types. [x / (0_0)]"]
    );
}

#[test]
fn an_operand_of_a_comparison_is_quoted_as_written() {
    assert_eq!(
        type_errors("f(x: f64) = x == 0.5_0r;\n"),
        [
            "No value is both `f64` and `rat`: `x : f64 == 0.5_0r : rat` always gives the same \
             answer. Try `x == 0.5_0` to compare the numbers instead. [x == 0.5_0r]"
        ]
    );
    // The literal repair writes the digits as the program does, on either side (row
    // RED-written-compare).
    assert_eq!(
        type_errors("f(x: f64) = 1_000.5r != x;\n"),
        [
            "No value is both `rat` and `f64`: `1_000.5r : rat != x : f64` always gives the same \
             answer. Try `1_000.5 != x` to compare the numbers instead. [1_000.5r != x]"
        ]
    );
}

#[test]
fn a_divisor_literal_is_quoted_as_written() {
    assert_eq!(
        type_errors("f(x: int) = x mod 0_0;\n"),
        [
            "`mod` here always fails with `#divByZero`: its divisor is the literal 0_0, so no \
          value that reaches it gives an int. [x mod 0_0]"
        ]
    );
    assert_eq!(
        type_errors("f(x: rat) = x / 0_0r;\n"),
        [
            "`/` here always fails with `#divByZero`: its divisor is the literal 0_0r, so no value \
          that reaches it gives a rat. [x / 0_0r]"
        ]
    );
    assert_eq!(
        type_errors("f(x: int) = 1_000 div 0;\n"),
        [
            "`div` here always fails with `#divByZero`: its divisor is the literal 0, so no value \
          that reaches it gives an int. [1_000 div 0]"
        ]
    );
}

#[test]
fn the_repair_of_a_rat_literal_writes_its_digits_as_the_program_does() {
    let out = rejected("g(x: f64) = x;\ny = g(x: -(1_000.5r));\n");
    assert!(
        out.contains("[2] 2:11: this expression is 1_000.5r\n"),
        "{out}"
    );
    assert!(
        out.contains("2:10: repair: write `-1_000.5`; the checker accepts that"),
        "{out}"
    );
    let out = rejected("g(x: int) = x;\ny = g(x: 1_000r);\n");
    assert!(
        out.contains("2:10: repair: write `1_000`; the checker accepts that"),
        "{out}"
    );
}

/// A comparison of a text with a hexadecimal literal of `n` digits, each pair separated by
/// `_`, in parentheses: each message quotes it, read from the program's text.
fn long(n: usize) -> String {
    format!("f(x: String) = x == (0x{}1);\n", "1_".repeat(n))
}

#[test]
fn quoting_a_literal_of_n_digits_with_underscores_scales() {
    let lit = format!("0x{}1", "1_".repeat(3));
    let errors = type_errors(&long(3));
    assert_eq!(errors.len(), 1);
    assert!(
        errors[0].starts_with(&format!(
            "No number equals a `String`: `x : String == {lit}`"
        )),
        "{errors:?}"
    );
    assert!(errors[0].contains(&format!("\"{lit}\"")), "{errors:?}");
    let n = 20_000;
    let srcs = scaling::inputs(n, long);
    scaling::check("quoting a literal of n digits with `_`", n, |m| {
        type_errors(&srcs[&m]);
    });
}
