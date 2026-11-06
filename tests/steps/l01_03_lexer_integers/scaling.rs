//! Lexing integers is of order n log n in the length of the text: many literals in every base,
//! one long literal, and a long literal that runs into a name at its end (DESIGN.md Part G).

use zed_tests::scaling::{check, inputs};
use zedc::lex::lex;

#[test]
fn many_literals_in_every_base_scale() {
    let texts = inputs(2_000, |n| {
        "1_048_576 0o755 0xFF_88_00 0b1011 8080 ".repeat(n)
    });
    check("lexing 5n integers", 2_000, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), 5 * n);
    });
}

#[test]
fn one_long_literal_scales() {
    let texts = inputs(20_000, |n| "1_0".repeat(n) + "9");
    check("lexing an integer of 2n digits", 20_000, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), 1);
    });
}

#[test]
fn one_long_literal_that_runs_into_a_name_scales() {
    let texts = inputs(20_000, |n| format!("0x{}g", "F_0".repeat(n)));
    check(
        "lexing a hex integer of 2n digits run into a name",
        20_000,
        |n| {
            assert!(lex(&texts[&n]).is_err());
        },
    );
}
