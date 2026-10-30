//! `String`, `abs`, `sum` and the string words.

use super::x;

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
    assert!(x("sum((1, 2.0))").starts_with("error: type error"));
}
