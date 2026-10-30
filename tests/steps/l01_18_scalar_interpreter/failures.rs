//! Operator arrows per region: data selects an arrow, a loose atom selects none and flows
//! on, and the atoms of several operands merge into `#errs` of the set of them.

use super::x;
use crate::l01_16_elaboration::errors;

#[test]
fn one_failure_flows_through_the_arithmetic() {
    assert_eq!(x("int(\"x\") * 2 + 1"), "#invalid");
    assert_eq!(x("-(10 div 0)"), "#divByZero");
}

#[test]
fn two_failures_merge_into_a_set() {
    assert_eq!(
        x("int(\"seven\") + int(2.5)"),
        "#errs({#inexact, #invalid})"
    );
    assert_eq!(
        x("int(2.5) + int(\"seven\")"),
        "#errs({#inexact, #invalid})",
        "the set has no order to invent"
    );
    assert_eq!(
        x("int(\"a\") + int(\"b\")"),
        "#invalid",
        "a singleton unwraps"
    );
}

#[test]
fn a_merge_flattens_and_else_replaces_it() {
    let src = "price = int(\"n/a\");\nqty = int(1.5);\nfee = 10 div 0;\n\
               total = price * qty + fee;\nshown = total else 0;\n";
    let v = |n| crate::l01_16_elaboration::value(src, n);
    assert_eq!(v("total"), "#errs({#divByZero, #inexact, #invalid})");
    assert_eq!(v("shown"), "0");
}

#[test]
fn an_atom_compared_with_equals_is_data() {
    assert_eq!(x("int(\"x\") == int(\"y\")"), "true");
    assert_eq!(x("int(\"x\") != int(2.5)"), "true");
}

#[test]
fn euclidean_division_keeps_the_remainder_non_negative() {
    let cases = [
        ("7 div -2", "-3"),
        ("7 mod -2", "1"),
        ("-7 div -2", "4"),
        ("-7 mod -2", "1"),
        ("-7 div 2", "-4"),
        ("-7 mod 2", "1"),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}

#[test]
fn mixed_kinds_select_no_arrow() {
    assert_eq!(
        errors("x = \"a\" ++ 1;\n"),
        ["`++` does not take (\"a\", 1) [\"a\" ++ 1]"]
    );
    assert_eq!(
        errors("n = 1;\nx = n + 1.5;\n"),
        ["`+` does not take (1, 1.5) [n + 1.5]"]
    );
    // A bare literal adopts the other operand's kind (step L1.26).
    assert_eq!(x("1 + 1.0"), "2.0");
    assert_eq!(x("1r/2r * 2"), "1r");
}
