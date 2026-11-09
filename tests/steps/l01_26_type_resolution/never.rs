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
    // `x is Never` holds of no value, so the first branch is unreachable: it is still
    // checked, and adds nothing to the result (DESIGN.md sec:constraints).
    let text = "h(positional x: int) = if x is Never { 1 } else { 2 };\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "h"), "(int) -> 2");
}

/// A tuple with an empty component has no value, so its type is `Never`: written as a
/// parameter's type, nested, in a union, and made by a tuple expression.
#[test]
fn a_tuple_with_an_empty_component_is_never() {
    for (text, want) in [
        ("f(positional x: (Never, int)) = x;\n", "(Never) -> Never"),
        ("f(positional x: (int, Never)) = x;\n", "(Never) -> Never"),
        (
            "f(positional x: ((Never, int), bool)) = x;\n",
            "(Never) -> Never",
        ),
        (
            "f(positional x: (int, Never) | bool) = x;\n",
            "(bool) -> bool",
        ),
        ("f(positional x: Never) = (x, 1);\n", "(Never) -> Never"),
        (
            "f(positional x: Never) = { y = ((x, 1), true); y };\n",
            "(Never) -> Never",
        ),
        // An atom whose payload has no value has none either.
        ("f(positional x: Never) = #a(x);\n", "(Never) -> Never"),
        // A function whose result has no value returns no value.
        (
            "f(positional g: (int) -> (Never, int)) = g(1);\n",
            "(((int) -> Never)) -> Never",
        ),
        // The empty tuple has one value, and is no `Never`.
        ("f(positional x: ()) = x;\n", "(()) -> ()"),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(text, "f"), want, "{text}");
    }
}

/// A branch whose test narrows a name to a type with no value is unreachable and adds nothing
/// to the result; a test that may hold keeps both branches.
#[test]
fn an_unreachable_branch_adds_nothing_to_the_result() {
    for (text, want) in [
        (
            "f(positional x: int) = if x is bool { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = if x is int { 1 } else { 2 };\n",
            "(int) -> 1",
        ),
        (
            "f(positional x: int) = if x is not int { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = if x is not Never { 1 } else { 2 };\n",
            "(int) -> 1",
        ),
        (
            "f(positional x: int) = if x is (Never, int) { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int | String) = if x is int { 1 } else if x is String { 2 } else \
             { 3 };\n",
            "(int | String) -> 1 | 2",
        ),
        // In the unreachable branch `x` is `Never`, so it adds nothing there either.
        (
            "f(positional x: int) = if x is Never { x } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = { y = (x, 1); if x is bool { y } else { (1, 2) } };\n",
            "(int) -> (1, 2)",
        ),
        // A name of type `Never` makes both branches unreachable.
        (
            "f(positional x: Never) = if x is int { 1 } else { 2 };\n",
            "(Never) -> Never",
        ),
        // A test that may hold keeps both branches.
        (
            "f(positional x: int | bool) = if x is int { 1 } else { 2 };\n",
            "(bool | int) -> 1 | 2",
        ),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(text, "f"), want, "{text}");
    }
}

/// An unreachable branch is still checked: an error in it is reported.
#[test]
fn an_unreachable_branch_is_still_checked() {
    let text = "f(positional x: int) = { y = (x, 1); if x is Never { y } else { y + 1 } };\n";
    assert_eq!(
        type_errors(text),
        [
            "`+` does not take ((int, 1), 1): these are the types of its arguments here, and `+` \
             has no arrow that takes them all [y + 1]"
        ]
    );
    // `x` is `Never` there, and `true` is still no operand of `+`.
    let text = "f(positional x: int) = if x is Never { x + true } else { 2 };\n";
    assert_eq!(
        type_errors(text),
        [
            "`+` does not take (Never, true): these are the types of its arguments here, and \
             `+` has no arrow that takes them all [x + true]"
        ]
    );
}

/// A branch whose tests contradict each other on the values of a name, so that no value of it
/// passes them all, is unreachable and adds nothing to the result, though the type of each
/// name there still lists values (DESIGN.md sec:constraints).
#[test]
fn a_branch_no_value_reaches_adds_nothing_to_the_result() {
    for (text, want) in [
        (
            "f(positional x: int) = if x > 0 && x < 0 { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = if x > 0 { if x < 0 { 1 } else { 2 } } else { 3 };\n",
            "(int) -> 2 | 3",
        ),
        // The test holds of every value, so the second branch is the unreachable one.
        (
            "f(positional x: int) = if x >= 0 || x < 0 { 1 } else { 2 };\n",
            "(int) -> 1",
        ),
        (
            "f(positional x: int) = if !(x > 0 || x <= 0) { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: int) = if x > 5 { 1 } else if x > 3 { 2 } else if x > 4 { 3 } \
             else { 4 };\n",
            "(int) -> 1 | 2 | 4",
        ),
        (
            "f(positional x: int, positional b: bool) = if b && x > 0 && x < 0 { 1 } else \
             { 2 };\n",
            "(int, bool) -> 2",
        ),
        (
            "f(positional x: int) = if x > 0 && x < 0 { 1 } else if x == 3 { 2 } else \
             { 3 };\n",
            "(int) -> 2 | 3",
        ),
        // `x` is still `int` there, but the branch adds nothing.
        (
            "f(positional x: int) = if x > 0 && x < 0 { x } else { 2 };\n",
            "(int) -> 2",
        ),
        // A test whose type meets the name's in a type with no value, though each lists
        // values: the tuple types meet in components that do not.
        (
            "f(positional x: (int, int)) = if x is (bool, int) { 1 } else { 2 };\n",
            "((int, int)) -> 2",
        ),
        (
            "f(positional x: int) = if x is (int, int) & (bool, int) { 1 } else { 2 };\n",
            "(int) -> 2",
        ),
        (
            "f(positional x: ((bool, int), int)) = if x is ((int, int), int) { 1 } else \
             { 2 };\n",
            "(((bool, int), int)) -> 2",
        ),
        // Tests that may both hold keep both branches.
        (
            "f(positional x: int) = if x > 0 && x < 9 { 1 } else { 2 };\n",
            "(int) -> 1 | 2",
        ),
        // Inside an unreachable branch nothing more is unreachable: it is all unreachable.
        (
            "f(positional x: int) = if x > 0 && x < 0 { if x > 1 { 1 } else { 2 } } else \
             { 3 };\n",
            "(int) -> 3",
        ),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(text, "f"), want, "{text}");
    }
    // Such a branch is still checked: an error in it is reported.
    let text = "f(positional x: int) = if x > 0 && x < 0 { x + true } else { 2 };\n";
    assert_eq!(
        type_errors(text),
        [
            "`+` does not take (int, true): these are the types of its arguments here, and `+` \
             has no arrow that takes them all [x + true]"
        ]
    );
}

/// An atom whose payload has no value once a generic function's types are put in has no
/// value either: it is `Never`, alone or in a union, as a tuple is.
#[test]
fn an_atom_with_a_payload_of_no_value_after_substitution_is_never() {
    let call = |body: &str| {
        format!(
            "app(positional g, positional x) = {body};\nf(positional h: (int) -> Never) = \
             app(h, 1);\n"
        )
    };
    let bool_call = |body: &str| {
        format!(
            "app(positional g, positional x, positional b: bool) = {body};\nf(positional h: \
             (int) -> Never, positional b: bool) = app(h, 1, b);\n"
        )
    };
    for (text, want) in [
        (call("#a(g(x), 1)"), "(((int) -> Never)) -> Never"),
        (call("#a((g(x), 1), 2)"), "(((int) -> Never)) -> Never"),
        (call("#a(k: g(x))"), "(((int) -> Never)) -> Never"),
        (
            bool_call("if b { #a(g(x)) } else { #a(2) }"),
            "(((int) -> Never), bool) -> #a(2)",
        ),
        (
            bool_call("if b { #a(g(x)) } else { #b }"),
            "(((int) -> Never), bool) -> #b",
        ),
        (
            bool_call("if b { #a } else { #a(g(x)) }"),
            "(((int) -> Never), bool) -> #a",
        ),
        // In a function's result.
        (
            "app(positional g) = (positional x: int) -> #a(g(x), 1);\nf(positional h: (int) -> \
             Never) = app(h);\n"
                .to_string(),
            "(((int) -> Never)) -> ((int) -> Never)",
        ),
        // A payload that keeps a value is kept.
        (
            call("#a(g, x)"),
            "(((int) -> Never)) -> #a(((int) -> Never), 1)",
        ),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(&text, "f"), want, "{text}");
    }
}
