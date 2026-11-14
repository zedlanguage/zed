//! Lexing integers is of order n log n in the length of the text: many literals in every base,
//! one long literal, and a long literal that runs into a name at its end (DESIGN.md Part G).
//! The benchmarks of this step, run by `tools/run_tests.sh --bench`; `scaling.rs` makes each of
//! their checks at small sizes.

use zed_tests::scaling::{check, inputs};

use super::scaling::{
    is_rejected, lexes_five_integers_each, lexes_one_token, literals_in_every_base, long_literal,
    long_literal_into_a_name,
};

/// Checks `expect` on the text `make` builds, lexed at sizes `n` and `8n`.
fn scales(what: &str, n: usize, make: fn(usize) -> String, expect: fn(&str, usize)) {
    let texts = inputs(n, make);
    check(what, n, |m| expect(&texts[&m], m));
}

#[test]
fn many_literals_in_every_base_scale() {
    scales(
        "lexing 5n integers",
        2_000,
        literals_in_every_base,
        lexes_five_integers_each,
    );
}

#[test]
fn one_long_literal_scales() {
    scales(
        "lexing an integer of 2n digits",
        20_000,
        long_literal,
        lexes_one_token,
    );
}

#[test]
fn one_long_literal_that_runs_into_a_name_scales() {
    scales(
        "lexing a hex integer of 2n digits run into a name",
        20_000,
        long_literal_into_a_name,
        is_rejected,
    );
}
