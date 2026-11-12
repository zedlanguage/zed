//! Operator arrows per region: data selects an arrow, a loose atom selects none and flows
//! on, and the atoms of several operands merge into `#errs` of the set of them.

use super::x;
use zed_tests::step_helpers::l01_16_elaboration::errors;

#[test]
fn one_failure_flows_through_the_arithmetic() {
    assert_eq!(x("int(text(\"x\")) * 2 + 1"), "#invalid");
    assert_eq!(x("-(10 div whole(0))"), "#divByZero");
    // A term with an undefined operand is undefined, the exponent 0 included, as NaN in,
    // NaN out holds for float `^` (item FLOAT-pow-nan).
    assert_eq!(x("(10 div whole(0)) ^ 0"), "#divByZero");
}

#[test]
fn two_failures_merge_into_a_set() {
    assert_eq!(
        x("int(text(\"seven\")) + int(real(2.5f64))"),
        "#errs({#inexact, #invalid})"
    );
    assert_eq!(
        x("int(real(2.5f64)) + int(text(\"seven\"))"),
        "#errs({#inexact, #invalid})",
        "the set has no order to invent"
    );
    assert_eq!(
        x("int(text(\"a\")) + int(text(\"b\"))"),
        "#invalid",
        "a singleton unwraps"
    );
}

#[test]
fn a_merge_flattens_and_else_replaces_it() {
    let src = "price = int(text(\"n/a\"));\nqty = int(real(1.5f64));\nfee = 10 div whole(0);\n\
               total = price * qty + fee;\nshown = total else 0;\n";
    let v =
        |n| zed_tests::step_helpers::l01_16_elaboration::value(&format!("{}{src}", super::PASS), n);
    assert_eq!(v("total"), "#errs({#divByZero, #inexact, #invalid})");
    assert_eq!(v("shown"), "0");
}

#[test]
fn an_atom_compared_with_equals_is_data() {
    assert_eq!(x("int(text(\"x\")) == int(text(\"y\"))"), "true");
    assert_eq!(x("int(text(\"x\")) != int(real(2.5f64))"), "true");
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
        [
            "`++` does not take (\"a\", 1): these are the types of its arguments here, and `++` has no arrow that takes them all [\"a\" ++ 1]"
        ]
    );
    // A literal keeps its kind: `1.5` is no int, and no form of it is (DESIGN.md L1.26b).
    assert_eq!(
        errors("n = 1;\nx = n + 1.5;\n"),
        [
            "A decimal literal is never an `int`: `n : int + 1.5`. Try `x = rat(n) + 1.5` \
             instead.\n  fixes, each checked here:\n    x = rat(n) + 1.5;    n is cast to rat, and \
             `+` takes two rat [1.5]"
        ]
    );
    assert_eq!(
        errors("x = 1r/2r * 2.5f64;\n"),
        [
            "the literal `2.5f64` is an `f64` by its suffix, and `rat` is expected here; a suffix \
             fixes a literal's carrier. Try `x = 1r/2r * 2.5r` instead.\n  fixes, each checked \
             here:\n    x = 1r/2r * 2.5r;    the literal is then exactly 2.5, a rat [2.5f64]"
        ]
    );
    // A generic literal takes the other operand's kind (step L1.26a).
    assert_eq!(x("1 + 1.0f64"), "2.0");
    assert_eq!(x("1r/2r * 2"), "1r");
}
