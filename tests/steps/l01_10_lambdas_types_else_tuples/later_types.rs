//! The type `_` and the named type `(n: T)` (item INFER-FIELD-desugar). sec:grammar desugars
//! `InferType` to the type `_` of every value and `FieldType` to the type `T`, whose `where`
//! predicate reads its value by the name `n`; both are forms of layer L10, so the parser builds
//! neither and names that layer. A named parameter of a function type, `(n: int) -> int`, is
//! no `FieldType` and builds at L1.

use super::check;
use zed_tests::step_helpers::m0_03_grammar_tools::grammar;

/// The desugaring rule of `rule` in `zed/grammar/desugar.txt`.
fn rule(rule: &str) -> String {
    let text = grammar("desugar.txt");
    let line = text
        .lines()
        .find(|l| l.split(':').next().map(str::trim) == Some(rule))
        .unwrap_or_else(|| panic!("no desugaring rule for {rule}"));
    line.split_once(':')
        .expect("a rule and its text")
        .1
        .trim()
        .into()
}

#[test]
fn the_desugaring_rules_read_the_spec() {
    assert_eq!(
        rule("InferType"),
        "the type `_` of every value (sec:type_language)"
    );
    assert_eq!(
        rule("FieldType"),
        "the type T; Name names its value in T's `where` predicate (sec:domains)"
    );
}

#[test]
fn the_type_of_every_value_is_built_from_layer_10() {
    check(&[
        (
            "x is _",
            "error: this form (InferType) is built from layer L10",
        ),
        // Inside a union, a tuple and parentheses alike.
        (
            "reading is _ | #missing",
            "error: this form (InferType) is built from layer L10",
        ),
        (
            "row is (String, _)",
            "error: this form (InferType) is built from layer L10",
        ),
        (
            "x is (_)",
            "error: this form (InferType) is built from layer L10",
        ),
    ]);
}

#[test]
fn a_named_type_is_built_from_layer_10() {
    check(&[
        (
            "age is (years: int)",
            "error: this form (FieldType) is built from layer L10",
        ),
        (
            "age is (years: int | #unknown)",
            "error: this form (FieldType) is built from layer L10",
        ),
        (
            "pair is ((lo: int), int)",
            "error: this form (FieldType) is built from layer L10",
        ),
        // A function type's named parameter is not a named type.
        (
            "f is ((years: int) -> int)",
            "(is f (-> ((years: int)) int))",
        ),
        // A name alone is a type name; two named components are no type.
        ("age is (years)", "(is age years)"),
        ("span is (lo: int, hi: int)", "syntax"),
    ]);
}
