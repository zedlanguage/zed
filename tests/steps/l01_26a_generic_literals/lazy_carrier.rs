//! A `/` or a `^` of literals alone, and a component of a tuple that is an operation on
//! literals alone, takes the carrier of what it meets, as `+`, `-` and `*` of literals do.
//! DESIGN.md sec:diagnostics, "A `/` of integer literals": "Neither side is typed on its own
//! as an `int` before it meets the `/`: an operation on literals alone is an `int` only where
//! nothing at all gives it a carrier." Step L1.26a: "An operation on literals alone, as
//! `2 + 1` or `-1`, is a literal too and takes the carrier of what it meets".

use super::fixes::{checked, pairs};
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// The value of `y` in `src`, which the checker accepts.
fn y(src: &str) -> String {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    value(src, "y")
}

/// The first line of the one rejection of `src`, without the ` [text]` the helper adds.
fn first(src: &str) -> String {
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}: {errors:?}");
    let message = errors[0].rsplit_once(" [").unwrap().0;
    message.lines().next().unwrap().to_string()
}

#[test]
fn a_division_of_literals_takes_the_carrier_it_meets() {
    // "an operation on literals alone is an `int` only where nothing at all gives it a
    // carrier": `7 / 2` meets `1.0f64` under `+`, so it is an `f64`, the carrier on the left
    // or on the right.
    assert_eq!(y("y = 1.0f64 + 7 / 2;\n"), "4.5");
    assert_eq!(y("y = 7 / 2 + 1.0f64;\n"), "4.5");
    assert_eq!(y("y = (1 + 2) / (3 + 4) + 1.0f64;\n"), "1.4285714285714286");
    assert_eq!(y("y = 1.0f64 + (1 + 2) / (3 + 4);\n"), "1.4285714285714286");
    // A `rat` reaches it the same way, and a name of one carrier as a literal does.
    assert_eq!(y("y = 1r + 7 / 2;\n"), "9r/2r");
    assert_eq!(y("y = (1 + 2) / (3 + 4) - 1r;\n"), "-4r/7r");
    assert_eq!(y("x = 0.5f64;\ny = x * (7 / 2);\n"), "1.75");
    // A `/` nested in a `/`, and a `-` of one.
    assert_eq!(y("y = 1.0f64 + (7 / 2) / (1 / 4);\n"), "15.0");
    assert_eq!(y("y = (1 / 2) / (1 / 4) * 1r;\n"), "2r");
    assert_eq!(y("y = -(7 / 2) + 1.0f64;\n"), "-2.5");
    // A comparison gives its other side's carrier too.
    assert_eq!(y("y = 7 / 2 == 3.5f64;\n"), "true");
    assert_eq!(y("y = 4.0f64 > 7 / 2;\n"), "true");
    // A `+` of a decimal and an integer literal meets the carrier the same way.
    assert_eq!(y("y = 1.0f64 + (2 + 0.5);\n"), "3.5");
}

#[test]
fn a_power_of_literals_takes_the_carrier_it_meets() {
    // DESIGN.md sec:operators, `^`: "`^` takes the integer or the floating-point power by the
    // types of its operands". `2 ^ 3` meets `1.0f64`, so both its literals are `f64`.
    assert_eq!(y("y = 1.0f64 + 2 ^ 3;\n"), "9.0");
    assert_eq!(y("y = 2 ^ 3 * 0.5f64;\n"), "4.0");
    // At `f64` a negative exponent is a power like any other.
    assert_eq!(y("y = 1.0f64 + 2 ^ -1;\n"), "1.5");
    assert_eq!(y("y = (2 ^ 3) / (1 + 1) + 0.5f64;\n"), "4.5");
    // With nothing to give a carrier, `^` of integer literals is the `int` power.
    assert_eq!(y("y = 1 + 2 ^ 3;\n"), "9");
    assert_eq!(y("y = 2 ^ 3;\n"), "8");
}

#[test]
fn where_nothing_gives_a_carrier_the_menu_writes_the_first_literal() {
    // "A `/` of integer literals": "the menu writes the carrier at the first literal of the
    // value". The carrier written at `1` reaches the `/` through the `+`.
    let src = "y = 1 + 7 / 2;\n";
    assert_eq!(
        first(src),
        "the `/` in the value of `y` divides integer literals, and nothing here gives them a \
         carrier; `/` has no arrow at `int`, and Zed does not choose `f64` or `rat` for it"
    );
    assert_eq!(
        checked(src),
        pairs(&[
            ("y = 1.0f64 + 7 / 2;", "y is 4.5"),
            ("y = 1r + 7 / 2;", "y is 9r/2r"),
            ("y = f64(1) + 7 / 2;", "y is 4.5"),
        ])
    );
    // A decimal fixed by its suffix gives its carrier to the `/` it meets.
    assert_eq!(
        checked("y = 0.5 * (7 / 2);\n"),
        pairs(&[
            ("y = 0.5f64 * (7 / 2);", "y is 1.75"),
            ("y = 0.5r * (7 / 2);", "y is 7r/4r"),
        ])
    );
    // A `^` takes `f64` alone, since it has no arrow at `rat`.
    assert_eq!(
        checked("y = 2 ^ 3 / 2;\n"),
        pairs(&[
            ("y = 2.0f64 ^ 3 / 2;", "y is 4.0"),
            ("y = f64(2) ^ 3 / 2;", "y is 4.0"),
        ])
    );
    assert_eq!(
        checked("y = 1 + 2 ^ 3 / 2;\n"),
        pairs(&[
            ("y = 1.0f64 + 2 ^ 3 / 2;", "y is 5.0"),
            ("y = f64(1) + 2 ^ 3 / 2;", "y is 5.0"),
        ])
    );
}

#[test]
fn a_tuple_comparison_gives_a_component_its_carrier() {
    // Step L1.26a: "two tuples compare component by component, each pair under this rule",
    // and "An operation on literals alone [...] takes the carrier of what it meets": in
    // `(1 + 2, 0) == (3.0f64, 0)`, `1 + 2` meets `3.0f64`.
    assert_eq!(y("y = (1 + 2, 0) == (3.0f64, 0);\n"), "true");
    assert_eq!(y("y = (3.0f64, 0) == (1 + 2, 0);\n"), "true");
    assert_eq!(y("y = (1 + 2, 0) != (3.0f64, 0);\n"), "false");
    assert_eq!(y("y = (7 / 2, 0) == (3.5f64, 0);\n"), "true");
    assert_eq!(y("y = (2 ^ 2, 0) == (4.0f64, 0);\n"), "true");
    assert_eq!(y("y = (0, (1 + 2, 1)) == (0, (3r, 1));\n"), "true");
    assert_eq!(y("x = 3.0f64;\ny = (1 + 2, 0) == (x, 0);\n"), "true");
    // With nothing to give a carrier the component is an `int`.
    assert_eq!(y("y = (1 + 2, 0) == (3, 0);\n"), "true");
}
