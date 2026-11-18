//! A bit word given as a function value, not called where it is named (SPEC-bit-identities):
//! `bitAnd`, `bitOr` and `bitXor` are functions of two ints in int[0..], and each call of the
//! value checks its operands as a call of the word does; every other bit word is refused as a
//! value, with the lambda that calls it as the repair. Before this, a bit word given as a value
//! took the type of `String`, one text to one text, so `f = bitOr; f(3, 5)` was refused as a
//! call with one argument too many.

use super::{accepted, rejected};

/// The value of `x` in the definitions `src`.
fn value(src: &str) -> String {
    zed_tests::step_helpers::l01_16_elaboration::value(src, "x")
}

#[test]
fn the_three_associative_words_are_values_of_two_operands() {
    assert_eq!(value("f = bitOr;\nx = f(3, 5);\n"), "7");
    assert_eq!(value("f = bitAnd;\nx = f(12, 10);\n"), "8");
    assert_eq!(value("f = bitXor;\nx = f(6, 3);\n"), "5");
    assert!(accepted("f = bitOr;\nx = f(3, 5);\n"));
}

#[test]
fn a_call_of_the_value_checks_each_operand() {
    let out = rejected("f = bitAnd;\nx = f(-1, 5);\n");
    assert!(out.contains("`f` takes `a` in int[0..]"), "{out}");
    assert!(out.contains("`bitAnd` takes `a` in int[0..] here"), "{out}");
    let out = rejected("f = bitXor;\nx = f(5, -1);\n");
    assert!(out.contains("`f` takes `b` in int[0..]"), "{out}");
}

#[test]
fn a_fold_by_the_value_checks_the_entries() {
    // The entry -5 reaches `bitOr`'s second operand, which takes only int[0..].
    let out = rejected("x = [3, -5].foldl(0, bitOr);\n");
    assert!(
        out.contains("the function given to `foldl` takes `b` in int[0..]"),
        "{out}"
    );
}

#[test]
fn another_bit_word_is_refused_as_a_value_with_the_lambda_as_repair() {
    for (src, repair) in [
        ("g = popCount;\n", "repair: write `(x) -> popCount(x)`"),
        ("g = shl;\n", "repair: write `(x, k) -> shl(x, k)`"),
        (
            "g = bitNot;\n",
            "repair: write `(x, width) -> bitNot(x, width: width)`",
        ),
    ] {
        let out = rejected(src);
        let w = &src[4..src.len() - 2];
        assert!(
            out.contains(&format!("`{w}` is given here as a function value")),
            "{out}"
        );
        assert!(out.contains(repair), "{out}");
    }
    // Called, the same words are accepted.
    assert!(accepted("g = popCount(7);\nh = shl(1, 3);\n"));
}
