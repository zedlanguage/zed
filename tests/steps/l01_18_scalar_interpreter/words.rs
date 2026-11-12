//! `String`, `abs`, `min`, `max`, `sum` and the string words.

use super::x;
use zed_tests::step_helpers::l01_16_elaboration::errors;

#[test]
fn string_writes_any_value_and_leaves_a_string_alone() {
    assert_eq!(x("String(\"ok\")"), "\"ok\"");
    assert_eq!(x("String(42)"), "\"42\"");
    assert_eq!(x("String(true)"), "\"true\"");
    assert_eq!(x("String(1r/3r)"), "\"1r/3r\"");
    assert_eq!(x("String((1, \"a\"))"), "\"(1, \\\"a\\\")\"");
    assert_eq!(x("\"${3} items at ${2.5f64}\""), "\"3 items at 2.5\"");
}

#[test]
fn cleaning_a_user_name() {
    let src = "raw = \"  Ada Lovelace \\n\";\nname = trim(raw);\nkey = lower(name);\n\
               shout = upper(name);\nsize = len(name);\n";
    let v = |n| zed_tests::step_helpers::l01_16_elaboration::value(src, n);
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
    assert_eq!(x("abs(-2.5f64)"), "2.5");
    assert_eq!(x("abs(-1r/3r)"), "1r/3r");
    assert_eq!(x("abs(-9223372036854775807 - 1)"), "9223372036854775808");
}

#[test]
fn summing_an_order() {
    assert_eq!(x("sum((3, 4, 5))"), "12");
    assert_eq!(x("sum((1.5f64, 2.25))"), "3.75");
    assert_eq!(x("sum((1r/2r, 1r/3r))"), "5r/6r");
    assert_eq!(x("sum((9, int(text(\"x\"))))"), "#invalid");
    // An integer literal beside an f64 is read as one (DESIGN.md L1.26a); a decimal literal
    // that nothing gives a carrier is rejected; a string is no number.
    assert_eq!(x("sum((1, 2.0f64))"), "3.0");
    assert_eq!(
        errors("x = sum((1, 2.0));\n"),
        [
            "Nothing gives the literal `2.0` a carrier. Try `x = sum((1, 2.0f64))` instead.\n  \
             fixes, each checked here:\n    x = sum((1, 2.0f64));    the literal is then the f64 \
             2.0\n    x = sum((1, 2.0r));      the literal is then exactly 2.0, a rat [2.0]"
        ]
    );
    assert_eq!(
        errors("x = sum((1, \"a\"));\n"),
        [
            "`sum` does not take (1, \"a\"): `sum` adds the components of a tuple, and they must all be numbers [sum((1, \"a\"))]"
        ]
    );
}

#[test]
fn min_and_max_of_each_number_kind() {
    assert_eq!(x("min(3, 5)"), "3");
    assert_eq!(x("max(3, 5)"), "5");
    assert_eq!(x("max(-2.5f64, 1.0)"), "1.0");
    assert_eq!(x("min(1r/2r, 1r/3r)"), "1r/3r");
    assert_eq!(x("max(9223372036854775807 + 1, 0)"), "9223372036854775808");
    assert_eq!(x("min(min(4, 2), 3)"), "2");
    assert_eq!(x("3.max(7)"), "7");
    // An integer literal beside an f64 is read as one (DESIGN.md L1.26a); a decimal literal
    // that nothing gives a carrier is rejected.
    assert_eq!(x("max(0, 2.5f64)"), "2.5");
    assert_eq!(
        errors("x = max(0, 2.5);\n"),
        [
            "Nothing gives the literal `2.5` a carrier. Try `x = max(0, 2.5f64)` instead.\n  \
             fixes, each checked here:\n    x = max(0, 2.5f64);    the literal is then the f64 \
             2.5\n    x = max(0, 2.5r);      the literal is then exactly 2.5, a rat [2.5]"
        ]
    );
    assert_eq!(
        zed_tests::step_helpers::l01_16_elaboration::value("f = max;\nx = f(1, 2);\n", "x"),
        "2"
    );
}

#[test]
fn min_and_max_pass_a_failure_on() {
    assert_eq!(x("min(int(text(\"x\")), 1)"), "#invalid");
    assert_eq!(x("max(int(text(\"x\")), int(text(\"y\")))"), "#invalid");
}

#[test]
fn min_and_max_take_two_numbers_of_one_kind() {
    let sig = zed_tests::step_helpers::l01_26_type_resolution::sig;
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
        [
            "`min` does not take (\"a\", \"b\"): these are the types of its arguments here, and `min` has no arrow that takes them all [min(\"a\", \"b\")]"
        ]
    );
    assert_eq!(
        errors("x = min(1, true);\n"),
        [
            "`min` does not take (1, true): these are the types of its arguments here, and `min` has no arrow that takes them all [min(1, true)]"
        ]
    );
    let both = "((int, int) -> int) & ((f64, f64) -> f64) & ((rat, rat) -> rat)";
    assert_eq!(
        errors("x = min(1);\n"),
        [format!(
            "this call of `{both}` gives no value to its parameter `x1`, and `x1` has no default, so the call cannot be made [min(1)]"
        )]
    );
    assert_eq!(
        errors("x = 3.max;\n"),
        [format!(
            "this call of `{both}` gives no value to its parameter `x1`, and `x1` has no default, so the call cannot be made [3.max]"
        )]
    );
    assert_eq!(
        errors("x = max(1, 2, 3);\n"),
        [format!(
            "this argument is one more than `{both}` takes: `{both}` takes 2 arguments by position, and the arguments before this one already fill them all [3]"
        )]
    );
}
