//! Lexing floats and rationals is of order n log n in the length of the text: many literals,
//! one long float with a long exponent, and a long float that runs into a name at its end
//! (DESIGN.md Part G). The benchmarks of this step, run by `tools/run_tests.sh --bench`;
//! `scaling.rs` makes each of their checks at small sizes.

use zed_tests::scaling::{check, inputs};

use super::scaling::{
    is_rejected, lexes_eight_tokens_each, lexes_one_token, literals,
    long_float_into_a_name, long_float_with_a_long_exponent,
};

/// Checks `expect` on the text `make` builds, lexed at sizes `n` and `8n`.
fn scales(what: &str, n: usize, make: fn(usize) -> String, expect: fn(&str, usize)) {
    let texts = inputs(n, make);
    check(what, n, |m| expect(&texts[&m], m));
}

#[test]
fn many_literals_scale() {
    scales("lexing 6n literals", 2_000, literals, lexes_eight_tokens_each);
}

#[test]
fn one_long_float_with_a_long_exponent_scales() {
    scales(
        "lexing a rational of 5n digits",
        20_000,
        long_float_with_a_long_exponent,
        lexes_one_token,
    );
}

#[test]
fn one_long_float_that_runs_into_a_name_scales() {
    scales(
        "lexing a float of 2n digits run into a name",
        20_000,
        long_float_into_a_name,
        is_rejected,
    );
}
