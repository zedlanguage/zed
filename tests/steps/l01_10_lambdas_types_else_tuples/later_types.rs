//! The type `_` and the named type `(n: T)` (item INFER-FIELD-desugar). sec:grammar desugars
//! `InferType` to the type `_` of every value and `FieldType` to the type `T`, whose `where`
//! predicate reads its value by the name `n`; this zedc compiles neither, so the parser builds
//! neither and reports each as not compiled yet. A named parameter of a function type, `(n: int) -> int`, is
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
fn the_type_of_every_value_is_not_compiled_yet() {
    check(&[
        (
            "x is _",
            concat!("error: ", zed_tests::not_yet!("the wildcard type `_`")),
        ),
        // Inside a union, a tuple and parentheses alike.
        (
            "reading is _ | #missing",
            concat!("error: ", zed_tests::not_yet!("the wildcard type `_`")),
        ),
        (
            "row is (String, _)",
            concat!("error: ", zed_tests::not_yet!("the wildcard type `_`")),
        ),
        (
            "x is (_)",
            concat!("error: ", zed_tests::not_yet!("the wildcard type `_`")),
        ),
    ]);
}

#[test]
fn a_named_type_is_not_compiled_yet() {
    check(&[
        (
            "age is (years: int)",
            concat!(
                "error: ",
                zed_tests::not_yet!("the named type `(years: int)`")
            ),
        ),
        (
            "age is (years: int | #unknown)",
            concat!(
                "error: ",
                zed_tests::not_yet!("the named type `(years: int | #unknown)`")
            ),
        ),
        (
            "pair is ((lo: int), int)",
            concat!("error: ", zed_tests::not_yet!("the named type `(lo: int)`")),
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

/// A refinement (`TypeSuffix`, layer L10) is refused at the first suffix of a chain of them,
/// the first in the order of the text.
#[test]
fn a_chain_of_refinements_is_refused_at_its_first() {
    check(&[
        (
            "x is int[v > 0]",
            concat!("error: ", zed_tests::not_yet!("the refinement `[v > 0]`")),
        ),
        (
            "x is int[v > 0][v < 9]",
            concat!("error: ", zed_tests::not_yet!("the refinement `[v > 0]`")),
        ),
    ]);
}
