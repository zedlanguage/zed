//! An operation on literals alone passed as a call's argument at a parameter of a declared
//! carrier takes that carrier. DESIGN.md sec:domains: "A use fixes a literal's carrier as step
//! L1.26a describes: as an operand of an operator, the other operand's; at a declared type,
//! that type's; [...] An operation on literals alone, as `2 + 1`, is a literal too, and takes
//! the carrier of what it meets." Step L1.26a: "`x: f64 = 1 / 2` is `0.5`".

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// The value of `y` in `src`, which the checker accepts.
fn y(src: &str) -> String {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    value(src, "y")
}

const F64: &str = "f(x: f64) = x;\n";
const RAT: &str = "f(x: rat) = x;\n";

#[test]
fn a_division_of_literals_takes_the_carrier_of_the_parameter() {
    assert_eq!(y(&format!("{F64}y = f(x: 1 / 2);\n")), "0.5");
    assert_eq!(y(&format!("{RAT}y = f(x: 1 / 2);\n")), "1r/2r");
    assert_eq!(y(&format!("{F64}y = f(x: (1 / 2));\n")), "0.5");
    assert_eq!(y(&format!("{F64}y = f(x: -(1 / 2));\n")), "-0.5");
    assert_eq!(
        y(&format!("{F64}y = f(x: (1 + 2) / (3 + 4));\n")),
        "0.42857142857142855"
    );
    assert_eq!(y(&format!("{RAT}y = f(x: (1 + 2) / (3 + 4));\n")), "3r/7r");
}

#[test]
fn other_operations_on_literals_take_the_carrier_of_the_parameter() {
    assert_eq!(y(&format!("{F64}y = f(x: 1 + 2);\n")), "3.0");
    assert_eq!(y(&format!("{RAT}y = f(x: 1 + 2);\n")), "3r");
    assert_eq!(y(&format!("{F64}y = f(x: 0.5 * 3);\n")), "1.5");
    assert_eq!(y(&format!("{F64}y = f(x: 2 ^ 3);\n")), "8.0");
}

#[test]
fn each_argument_takes_the_carrier_of_its_own_parameter() {
    let g = "g(x: f64, y: rat) = (x, y);\n";
    assert_eq!(
        y(&format!("{g}y = g(x: 1 / 2, y: 1 / 3);\n")),
        "(0.5, 1r/3r)"
    );
    assert_eq!(
        y(&format!("{g}y = g(y: 1 / 3, x: 1 / 2);\n")),
        "(0.5, 1r/3r)"
    );
    let p = "g(positional x: f64, positional y: rat) = (x, y);\n";
    assert_eq!(y(&format!("{p}y = g(1 / 2, 1 / 3);\n")), "(0.5, 1r/3r)");
}

#[test]
fn a_division_of_literals_at_an_int_or_untyped_parameter_is_still_rejected() {
    // `/` has no arrow at `int`, and a parameter with no declared type fixes no carrier.
    for f in ["f(x: int) = x;\n", "f(x) = x + x;\n"] {
        let src = format!("{f}y = f(x: 1 / 2);\n");
        let errors = type_errors(&src);
        assert!(
            errors
                .iter()
                .any(|e| e.starts_with("Nothing gives the literal `1` a carrier")),
            "{src}: {errors:?}"
        );
    }
}
