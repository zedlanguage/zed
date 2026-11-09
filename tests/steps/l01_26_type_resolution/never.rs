//! The empty type is the prelude type `Never` (DESIGN.md, the L1 row of "Defined words by
//! layer"): a program writes it from L1 on, and the checker prints a type with no value as
//! `Never`. A declared result type `-> Never` and a binding with a declared type `x: Never = 1`
//! are forms of layer L10, which zedc does not compile yet, so these tests write `Never` where
//! L1 takes a type: a parameter's type and a function type's result.

use super::{sig, type_errors};

#[test]
fn a_function_type_may_declare_the_result_never() {
    let text = "apply(positional h: (int) -> Never, positional n: int) = h(n);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "apply"), "(((int) -> Never), int) -> Never");
}

#[test]
fn never_in_a_union_adds_nothing() {
    assert_eq!(
        sig("g(positional n: int | Never) = n;\n", "g"),
        "(int) -> int"
    );
}

#[test]
fn a_parameter_of_type_never_takes_no_argument() {
    let text = "take(positional x: Never) = x;\nr = take(1);\n";
    assert_eq!(
        type_errors(text),
        [
            "`take` does not take (1): these are the types of its arguments here, and `take` has \
          no arrow that takes them all [take(1)]"
        ]
    );
    assert_eq!(sig(text, "take"), "(Never) -> Never");
}

#[test]
fn a_test_against_never_is_accepted() {
    // `x is Never` holds of no value; the test is still a test of a written type.
    let text = "h(positional x: int) = if x is Never { 1 } else { 2 };\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "h"), "(int) -> 1 | 2");
}
