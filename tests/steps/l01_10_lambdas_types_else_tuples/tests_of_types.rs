//! `is` and `is not` test a value against a type expression: names, atoms, tuples, unions,
//! intersections, differences and, parenthesized, function types.

use super::check;

#[test]
fn a_test_is_a_relation() {
    check(&[
        ("v is #none", "(is v #none)"),
        ("r is not Config", "(is not r Config)"),
        ("a + 1 is int", "(is (+ a 1) int)"),
        ("x is int && y is not f64", "(&& (is x int) (is not y f64))"),
        ("shape is geometry.Circle", "(is shape geometry.Circle)"),
    ]);
}

#[test]
fn type_connectives() {
    check(&[
        ("x is int | #missing", "(is x (| int #missing))"),
        ("x is int | String | #none", "(is x (| int String #none))"),
        ("x is Named & Aged", "(is x (& Named Aged))"),
        (
            "x is Named & Aged | #none",
            "(is x (| (& Named Aged) #none))",
        ),
        ("x is int \\ #zero", "(is x (\\ int #zero))"),
        ("x is (int, String)", "(is x (tuple int String))"),
        ("x is (int | #none)", "(is x (| int #none))"),
        // `\` does not mix with `|` or `&` unparenthesized.
        ("x is int \\ #zero | #none", "syntax"),
    ]);
}

#[test]
fn function_types_have_one_level_per_parameter() {
    check(&[
        // DESIGN.md L1.12: `((int, int)) -> int` has one parameter, of tuple type, and
        // `(int, int) -> int` has two.
        ("f is ((int, int) -> int)", "(is f (-> (int int) int))"),
        (
            "f is (((int, int)) -> int)",
            "(is f (-> ((tuple int int)) int))",
        ),
        (
            "f is (int -> int -> int)",
            "(is f (-> (int) (-> (int) int)))",
        ),
        ("f is (() -> int)", "(is f (-> () int))"),
        ("m is (String ->? int)", "(is m (->? (String) int))"),
        ("f is ((x: f64) -> f64)", "(is f (-> ((x: f64)) f64))"),
        (
            "f is ((positional v: int, lo: int) -> int)",
            "(is f (-> ((positional v: int) (lo: int)) int))",
        ),
        // An arrow type after `is` is parenthesized.
        ("f is int -> int", "syntax"),
    ]);
}
