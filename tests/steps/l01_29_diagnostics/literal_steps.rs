//! The steps of a rejection name the type the program gives each operation there, and none
//! for an operation on literals alone that has met no carrier. DESIGN.md sec:diagnostics,
//! "A `/` of integer literals": "An operation on integer literals alone is a literal too and
//! takes the carrier of what it meets", "`1 + 2` adds two integer literals, so it is a literal
//! too and takes the carrier of what it meets; it meets only the `/`", and "Neither side is
//! typed on its own as an `int` before it meets the `/`". The type the checker kept for such
//! a `/` after rejecting it, `f64`, is not one the program gives it.

use super::{rejected, steps};

/// The step of an operation on literals alone that has met no carrier, `what` naming it.
fn open(what: &str) -> String {
    format!(
        "this `{what}` is an operation on literals alone, so it is a literal too and takes the \
         carrier of what it meets"
    )
}

/// The step of such a `/`.
fn open_div() -> String {
    open("/") + "; `/` has no arrow at `int`"
}

#[test]
fn a_division_of_divisions_of_literals_names_no_type_for_them() {
    let out = rejected("y = (1 / 2) / (3 / 4);\n");
    let d = open_div();
    let want = format!(
        "1:5: Nothing gives the integer literals a carrier, and `/` has none at `int`: \
         `y = (1 / 2) / (3 / 4)`. Try `y = (1.0f64 / 2) / (3 / 4)` instead.
  [1] 1:5: {d}
      1 | y = (1 / 2) / (3 / 4);
        |     ^^^^^^^ [2]    ^ [7]
        |     ^^^^^^^^^^^^^^^^^ [1]
        |      ^ [3]    ^^^^^^^ [5]
        |          ^ [4] ^ [6]
  [2] 1:5: {d}
  [3] 1:6: this literal, 1, is 1
  [4] 1:10: this literal, 2, is 2
  [5] 1:15: {d}
  [6] 1:16: this literal, 3, is 3
  [7] 1:20: this literal, 4, is 4
  fixes, each checked here:
    y = (1.0f64 / 2) / (3 / 4);    y is 0.6666666666666666
    y = (1r / 2) / (3 / 4);        y is 2r/3r
    y = (f64(1) / 2) / (3 / 4);    y is 0.6666666666666666"
    );
    assert_eq!(out, want);
    assert!(!out.contains("gives f64"), "{out}");
}

#[test]
fn divisions_of_literals_nested_two_deep_name_no_type_for_any_of_them() {
    let out = rejected("y = ((1 / 2) / (3 / 4)) / (5 / 6);\n");
    let d = open_div();
    assert_eq!(
        steps(&out),
        [
            &*d,
            &d,
            &d,
            "this literal, 1, is 1",
            "this literal, 2, is 2",
            &d,
            "this literal, 3, is 3",
            "this literal, 4, is 4",
            &d,
            "this literal, 5, is 5",
            "this literal, 6, is 6",
        ],
        "{out}"
    );
}

#[test]
fn an_operand_of_a_division_of_literals_is_a_literal_too_and_not_an_int() {
    // The spec's own example: `1 + 2` and `3 + 4` meet only the `/`.
    let out = rejected("q = (1 + 2) / (3 + 4);\n");
    let (d, plus) = (open_div(), open("+"));
    assert_eq!(
        steps(&out),
        [
            &*d,
            &plus,
            "this literal, 1, is 1",
            "this literal, 2, is 2",
            &plus,
            "this literal, 3, is 3",
            "this literal, 4, is 4",
        ],
        "{out}"
    );
    // A `-` of a `/`, and a `^` under one, are literals in the same way.
    let out = rejected("y = -(1 / 2) * \"a\";\n");
    assert_eq!(steps(&out)[..2], [&*open("-"), &d], "{out}");
    let out = rejected("y = 0xFF / 2 ^ 2;\n");
    assert_eq!(steps(&out)[2], open("^"), "{out}");
}

#[test]
fn an_operation_on_literals_that_the_program_gives_a_type_keeps_it() {
    // Nothing gives `1 + 2` a carrier, and no `/` or decimal is in it, so it is the `int` the
    // program gives it: the type found and the program's agree, and the step names it.
    let out = rejected("y = (1 + 2) * \"a\";\n");
    assert_eq!(
        steps(&out)[..4],
        [
            "this `+` gives int",
            "this literal, 1, is 1",
            "this literal, 2, is 2",
            "this expression is \"a\"",
        ],
        "{out}"
    );
    // `1 + 2` meets `1.0f64` and takes `f64`, which the step names, not the `int` the walk
    // found for it before it met one.
    let out = rejected("y = ((1 + 2) * 1.0f64) * \"a\";\n");
    assert_eq!(
        steps(&out)[..2],
        ["this `*` gives f64", "this `+` gives f64"],
        "{out}"
    );
    // A `/` of literals that met a carrier is of that carrier.
    let out = rejected("y = (1.0f64 + 7 / 2) * \"a\";\n");
    assert_eq!(
        steps(&out)[..3],
        [
            "this `+` gives f64",
            "this literal, 1.0f64, is 1.0",
            "this `/` gives f64",
        ],
        "{out}"
    );
}

/// The step of a read of `name`, defined as an operation on literals alone that met no carrier.
fn read_open(name: &str) -> String {
    format!(
        "`{name}` is read here; it is defined as an operation on literals alone, so it takes the \
         carrier of what it meets"
    )
}

#[test]
fn a_name_defined_as_an_operation_on_literals_that_met_no_carrier_is_read_with_no_type() {
    // The spec's `q`, read once more: `q` was rejected, and the type the checker kept for it,
    // `Never`, is not one the program gives it, so no step names it.
    let out = rejected("q = (1 + 2) / (3 + 4);\nz = q * \"a\";\n");
    let (d, plus) = (open_div(), open("+"));
    let second = out.split_once("\n2:5: ").expect("a second rejection").1;
    assert_eq!(
        steps(second)[..4],
        [
            &*read_open("q"),
            "`q` is defined as this expression",
            &d,
            &plus,
        ],
        "{out}"
    );
    assert!(
        !second.contains("`q` is Never") && !second.contains("expression, Never"),
        "{out}"
    );
    // `q = 1 / 2` the same: the `f64` the checker kept for the `/` is not the program's.
    let out = rejected("q = 1 / 2;\nz = q * \"a\";\n");
    let second = out.split_once("\n2:5: ").expect("a second rejection").1;
    assert_eq!(
        steps(second)[..3],
        [&*read_open("q"), "`q` is defined as this expression", &d],
        "{out}"
    );
    assert!(
        !second.contains("`q` is f64") && !second.contains("expression, f64"),
        "{out}"
    );
}

#[test]
fn a_name_defined_as_an_operation_on_literals_of_a_type_is_read_with_its_type() {
    let out = rejected("q = 1 + 2;\nz = q * \"a\";\n");
    assert_eq!(
        steps(&out)[..3],
        [
            "`q` is int here",
            "`q` is defined as this expression, int",
            "this `+` gives int",
        ],
        "{out}"
    );
}
