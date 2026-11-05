//! `String`, `abs`, `min`, `max`, `sum` and the string words.

use super::x;
use crate::l01_16_elaboration::errors;

#[test]
fn string_writes_any_value_and_leaves_a_string_alone() {
    assert_eq!(x("String(\"ok\")"), "\"ok\"");
    assert_eq!(x("String(42)"), "\"42\"");
    assert_eq!(x("String(true)"), "\"true\"");
    assert_eq!(x("String(1r/3r)"), "\"1r/3r\"");
    assert_eq!(x("String((1, \"a\"))"), "\"(1, \\\"a\\\")\"");
    assert_eq!(x("\"${3} items at ${2.5}\""), "\"3 items at 2.5\"");
}

#[test]
fn cleaning_a_user_name() {
    let src = "raw = \"  Ada Lovelace \\n\";\nname = trim(raw);\nkey = lower(name);\n\
               shout = upper(name);\nsize = len(name);\n";
    let v = |n| crate::l01_16_elaboration::value(src, n);
    assert_eq!(v("name"), "\"Ada Lovelace\"");
    assert_eq!(v("key"), "\"ada lovelace\"");
    assert_eq!(v("shout"), "\"ADA LOVELACE\"");
    assert_eq!(v("size"), "12");
}

#[test]
fn string_words_are_unicode() {
    assert_eq!(x("len(\"héllo\")"), "5", "code points, not bytes");
    assert_eq!(x("upper(\"straße\")"), "\"STRASSE\"");
    assert_eq!(x("lower(\"ÀÉÎ\")"), "\"àéî\"");
    assert_eq!(x("trim(\"\\u{3000}hi\\t\")"), "\"hi\"");
}

#[test]
fn abs_of_each_number_kind() {
    assert_eq!(x("abs(-7)"), "7");
    assert_eq!(x("abs(-2.5)"), "2.5");
    assert_eq!(x("abs(-1r/3r)"), "1r/3r");
    assert_eq!(x("abs(-9223372036854775807 - 1)"), "9223372036854775808");
}

#[test]
fn summing_an_order() {
    assert_eq!(x("sum((3, 4, 5))"), "12");
    assert_eq!(x("sum((1.5, 2.25))"), "3.75");
    assert_eq!(x("sum((1r/2r, 1r/3r))"), "5r/6r");
    assert_eq!(x("sum((9, int(\"x\")))"), "#invalid");
    // A generic integer literal beside an f64 is read as one (DESIGN.md L1.26a), a plain one
    // is rejected; a string is no number.
    assert_eq!(x("sum((1n, 2.0))"), "3.0");
    assert_eq!(
        errors("x = sum((1, 2.0));\n"),
        [
            "`1` is an int where `f64` is expected; a literal takes no other carrier; write `1.0` \
          or `1n` [1]"
        ]
    );
    assert_eq!(
        errors("x = sum((1, \"a\"));\n"),
        ["`sum` does not take (1, \"a\") [sum((1, \"a\"))]"]
    );
}

#[test]
fn min_and_max_of_each_number_kind() {
    assert_eq!(x("min(3, 5)"), "3");
    assert_eq!(x("max(3, 5)"), "5");
    assert_eq!(x("max(-2.5, 1.0)"), "1.0");
    assert_eq!(x("min(1r/2r, 1r/3r)"), "1r/3r");
    assert_eq!(x("max(9223372036854775807 + 1, 0)"), "9223372036854775808");
    assert_eq!(x("min(min(4, 2), 3)"), "2");
    assert_eq!(x("3.max(7)"), "7");
    // A generic integer literal beside an f64 is read as one (DESIGN.md L1.26a); a plain one
    // is rejected.
    assert_eq!(x("max(0n, 2.5)"), "2.5");
    assert_eq!(
        errors("x = max(0, 2.5);\n"),
        [
            "`0` is an int where `f64` is expected; a literal takes no other carrier; write `0.0` \
          or `0n` [0]"
        ]
    );
    assert_eq!(
        crate::l01_16_elaboration::value("f = max;\nx = f(1, 2);\n", "x"),
        "2"
    );
}

#[test]
fn min_and_max_pass_a_failure_on() {
    assert_eq!(x("min(int(\"x\"), 1)"), "#invalid");
    assert_eq!(x("max(int(\"x\"), int(\"y\"))"), "#invalid");
}

#[test]
fn min_and_max_take_two_numbers_of_one_kind() {
    let sig = crate::l01_26_type_resolution::sig;
    assert_eq!(
        sig(
            "f(positional a: int, positional b: int) = max(a, b);\n",
            "f"
        ),
        "(int, int) -> int"
    );
    assert_eq!(
        sig("f(positional a: f64) = min(a, 0.0);\n", "f"),
        "(f64) -> f64"
    );
    assert_eq!(
        sig("f(positional a: int) = a.max(0);\n", "f"),
        "(int) -> int"
    );
    assert_eq!(
        sig("f(positional a: rat) = max(a, 0r);\n", "f"),
        "(rat) -> rat"
    );
    assert_eq!(
        errors("x = min(\"a\", \"b\");\n"),
        ["`min` does not take (\"a\", \"b\") [min(\"a\", \"b\")]"]
    );
    assert_eq!(
        errors("x = min(1, true);\n"),
        ["`min` does not take (1, true) [min(1, true)]"]
    );
    let both = "((int, int) -> int) & ((f64, f64) -> f64) & ((rat, rat) -> rat)";
    assert_eq!(
        errors("x = min(1);\n"),
        [format!("missing argument `x1` of `{both}` [min(1)]")]
    );
    assert_eq!(
        errors("x = 3.max;\n"),
        [format!("missing argument `x1` of `{both}` [3.max]")]
    );
    assert_eq!(
        errors("x = max(1, 2, 3);\n"),
        [format!("too many arguments: `{both}` takes 2 [3]")]
    );
}
