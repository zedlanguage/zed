//! Rounding a float literal at the rule of low complexity. The inputs are built in
//! `literals.rs`, whose test `a_long_literal_rounds_by_every_digit` checks them at a small
//! size.

use std::collections::HashMap;

use zed_kernel::num::literal_f64;
use zed_tests::scaling::{check_instructions_only, check_order, inputs};
use zed_tests::step_helpers::l01_16_elaboration::elab;

use super::super::literals::{digits_above_a_tie, digits_near_one};

#[test]
fn elaborating_a_literal_of_n_digits_scales() {
    // About 8 ns and 5 bytes a digit: 1x about 0.27 s, 1.3 GB at 8n, 6 s in all.
    let n = 1 << 25;
    let built: HashMap<usize, String> = inputs(n, |n| format!("v = {}f64;\n", digits_near_one(n)));
    check_order("a float literal of n digits", n, 1, |n| {
        elab(&built[&n]).unwrap();
    });
}

#[test]
fn rounding_a_literal_of_n_digits_scales() {
    // The rounding alone: at 2000 digits the rest of the pipeline did about 2.6 times its
    // work, enough to hide a quadratic added to it (COMPLEXITY.md F85). It allocates nothing,
    // and takes about 0.7 ns a digit: 1x about 0.1 s. 0.6 s would take 2^30 digits, whose
    // text at 8n alone is 8 GB; the texts of 2^27 and 2^30 digits hold 1.2 GB.
    let n = 1 << 27;
    let built = inputs(n, digits_near_one);
    check_instructions_only("rounding a float literal of n digits", n, 1, |n| {
        assert!(literal_f64(&built[&n]).is_ok());
    });
}

#[test]
fn rounding_a_literal_of_n_digits_near_a_tie_scales() {
    // About 1.2 ns a digit, allocating nothing: 1x about 0.16 s; the texts of 2^27 and 2^30
    // digits hold 1.2 GB.
    let n = 1 << 27;
    let built = inputs(n, digits_above_a_tie);
    check_order(
        "rounding a float literal of n digits near a tie",
        n,
        1,
        |n| {
            assert_eq!(literal_f64(&built[&n]), Ok(1.0 + f64::EPSILON));
        },
    );
}
