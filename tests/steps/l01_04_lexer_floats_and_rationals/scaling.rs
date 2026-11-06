//! Lexing floats and rationals is of order n log n in the length of the text: many literals,
//! one long float with a long exponent, and a long float that runs into a name at its end
//! (DESIGN.md Part G).

use zed_tests::scaling::{check, inputs};
use zedc::lex::lex;

#[test]
fn many_literals_scale() {
    // Five literals and a range `1..10` of three tokens.
    let texts = inputs(2_000, |n| {
        "0.5 1.5e-3 6.022_140_76e23 0.1r 2.5e-3r 1..10 ".repeat(n)
    });
    check("lexing 6n literals", 2_000, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), 8 * n);
    });
}

#[test]
fn one_long_float_with_a_long_exponent_scales() {
    let texts = inputs(20_000, |n| {
        format!(
            "{}.{}e-{}r",
            "1_0".repeat(n),
            "0_5".repeat(n),
            "1".repeat(n)
        )
    });
    check("lexing a rational of 5n digits", 20_000, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), 1);
    });
}

#[test]
fn one_long_float_that_runs_into_a_name_scales() {
    let texts = inputs(20_000, |n| {
        format!("{}.5{}", "1_0".repeat(n), "m".repeat(n))
    });
    check("lexing a float of 2n digits run into a name", 20_000, |n| {
        assert!(lex(&texts[&n]).is_err());
    });
}
