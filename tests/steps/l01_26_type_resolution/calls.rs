//! A call through a value takes named arguments, closed defaults and `...` from the signature
//! the checker gives the value.

use super::type_errors;
use zed_tests::step_helpers::l01_16_elaboration::{errors, value};

#[test]
fn named_arguments_through_a_value() {
    assert_eq!(
        value("sub(a, b) = a - b;\nk = sub;\ny = k(b: 5, a: 3);\n", "y"),
        "-2"
    );
}

#[test]
fn a_closed_default_is_filled_through_a_value() {
    assert_eq!(
        value(
            "tax(price, rate = 0.2f64) = price * rate;\nt = tax;\ny = t(price: 10.0f64);\n",
            "y"
        ),
        "2.0"
    );
}

#[test]
fn a_default_that_reads_other_parameters_needs_the_declared_function() {
    assert_eq!(
        errors("tax(price, rate = price / 10.0) = price * rate;\nt = tax;\ny = t(price: 10.0);\n"),
        [
            "this call goes through a function value and leaves out `rate`, whose default reads \
          the function's other parameters; only a call of the declared function by its name \
          fills such a default, so here `rate` has no value. [t(price: 10.0)]"
        ]
    );
}

#[test]
fn a_partial_call_through_a_value() {
    assert_eq!(
        value(
            "greet(positional name, punct = \"!\") = \"${name}${punct}\";\n\
             g = greet;\nh = g(\"Al\", ...);\ny = h(punct: \"?\");\n",
            "y"
        ),
        "\"Al?\""
    );
}

#[test]
fn destructuring_gives_each_name_its_component() {
    let p = "a, b = (1, \"x\");\nc = a + 1;\nd = b ++ \"y\";\n";
    assert!(type_errors(p).is_empty());
    assert_eq!(value(p, "c"), "2");
    assert_eq!(
        type_errors("a, b = (1, 2, 3);\n"),
        [
            "Cannot take `(1, 2, 3) : (1, 2, 3)` apart into 2 names: it is not a tuple of 2. [(1, 2, 3)]"
        ]
    );
    assert_eq!(
        type_errors("t = (1, 2)[2];\n"),
        [
            "(1, 2) has no component 2: its components are at the positions 0 to 1, and this index is 2. [(1, 2)[2]]"
        ]
    );
}
