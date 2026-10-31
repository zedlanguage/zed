//! A declared function's signature comes from its body: an untyped parameter is a type
//! variable, bounded by the carriers its uses take, and the error is at the use that leaves
//! it none.

use super::{sig, type_errors};

#[test]
fn arithmetic_gives_a_variable_bounded_by_the_numeric_carriers() {
    assert_eq!(
        sig("area(w, h) = w * h;\n", "area"),
        "(w: T, h: T) -> T for T in int | f64 | rat"
    );
    assert_eq!(
        sig("neg(x) = -x;\n", "neg"),
        "(x: T) -> T for T in int | f64 | rat"
    );
}

#[test]
fn an_operator_with_one_carrier_fixes_it() {
    assert_eq!(
        sig("shout(s) = upper(s) ++ \"!\";\n", "shout"),
        "(s: String) -> String"
    );
    assert_eq!(
        sig("both(a, b) = a && b;\n", "both"),
        "(a: bool, b: bool) -> bool"
    );
    // `/` divides f64 and rat only, and the literal `2` adopts f64.
    assert_eq!(sig("half(x) = x / 2;\n", "half"), "(x: f64) -> f64");
    assert_eq!(
        sig("avg(a, b) = (a + b) / 2;\n", "avg"),
        "(a: f64, b: f64) -> f64"
    );
}

#[test]
fn comparison_checks_at_every_ordered_carrier() {
    assert_eq!(
        sig("lt(a, b) = a < b;\n", "lt"),
        "(a: T, b: T) -> bool for T in int | f64 | rat | String | bool"
    );
}

#[test]
fn a_parameter_any_value_fits_gets_a_type_variable() {
    assert_eq!(
        sig("label(n) = \"n = ${n}\";\n", "label"),
        "(n: T) -> String"
    );
    assert_eq!(
        sig("pair(a, b) = (a, b);\n", "pair"),
        "(a: T, b: U) -> (T, U)"
    );
    assert_eq!(sig("g(r) = r else 0;\n", "g"), "(r: T) -> 0 | T");
    // Only the condition is fixed; the branches stay generic, each its own variable.
    assert_eq!(
        sig(
            "pick(positional c, positional a, positional b) = if c { a } else { b };\n",
            "pick"
        ),
        "(bool, T, U) -> T | U"
    );
}

#[test]
fn a_type_variable_used_as_a_tuple_gives_the_unknown() {
    assert_eq!(sig("first(p) = p[0];\n", "first"), "(p: T) -> _");
}

#[test]
fn a_declared_type_is_kept() {
    assert_eq!(
        sig("apply(positional x, f: (int) -> int) = f(x);\n", "apply"),
        "(int, f: ((int) -> int)) -> int"
    );
    assert_eq!(
        sig(
            "n(x: int | String) = if x is String { len(x) } else { x * 2 };\n",
            "n"
        ),
        "(x: int | String) -> int"
    );
}

#[test]
fn a_default_is_checked_at_its_parameters_type() {
    assert_eq!(
        sig("tax(price, rate = 0.2) = price * rate;\n", "tax"),
        "(price: f64, rate: f64) -> f64"
    );
    assert_eq!(
        sig("tax(price, rate = price / 10.0) = price * rate;\n", "tax"),
        "(price: f64, rate: f64) -> f64"
    );
}

#[test]
fn a_default_of_the_wrong_type_is_an_error() {
    assert_eq!(
        type_errors("f(a: int, b: int = a > 0) = a + b;\n"),
        ["the default of `b` is bool, not int [a > 0]"]
    );
}

#[test]
fn a_body_that_checks_at_no_type_is_reported() {
    // Wrong at every type: the error is the body's own.
    assert_eq!(
        type_errors("bad(x) = x + \"a\" * 2;\n"),
        ["`*` does not take (\"a\", 2) [\"a\" * 2]"]
    );
    // Wrong at each carrier, for a reason that depends on it: `++` makes `x` a String, and
    // the error is at the use that then finds it none.
    assert_eq!(
        type_errors("neither(x) = x ++ \"a\" + 1;\n"),
        ["`+` does not take (String, 1) [x ++ \"a\" + 1]"]
    );
}

#[test]
fn a_parameter_compared_with_a_tuple_may_be_a_tuple() {
    // `<` orders tuples of one length as well as carriers, so `x` may be `(3, 4)`: its
    // class keeps the tuple arrow, which allows only other values, and it gives `_`.
    let src = "lt(positional x) = x < (1, 2);\nmain() = lt((3, 4));\n";
    assert_eq!(sig(src, "lt"), "(_) -> bool");
    assert!(type_errors(src).is_empty(), "{:?}", type_errors(src));
}

#[test]
fn a_literal_compared_for_equality_does_not_bound_a_parameter() {
    // `==` takes any two values, so the literal follows the class and leaves it every
    // carrier: `eq1("a")` is false, not an error.
    let src = "eq1(positional x) = x == 1;\nmain() = eq1(\"a\");\n";
    assert_eq!(sig(src, "eq1"), "(T) -> bool");
    assert!(type_errors(src).is_empty(), "{:?}", type_errors(src));
}
