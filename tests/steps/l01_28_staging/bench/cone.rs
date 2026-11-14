//! The checks of `cone.rs` at `n` and `8n` (COMPLEXITY.md rows F43 and F83). Each unit is
//! built before the timing; `cone.rs` checks what each mix gives at small sizes.

use zed_tests::scaling;

use crate::cone::{
    F0, a_root_remixed, a_split_of_calls_reading_k, at_a_lambda, chain_passing_functions,
    chain_reading_k, float_chain_at_minus_zero, left_to_run, nothing_left, sites, with_main,
};

/// Checks that mixing `with_main(n, F0::Loops, two)` scales.
fn mixing_scales(what: &'static str, two: bool) {
    let n = 400;
    let units = scaling::inputs(n, |n| with_main(n, F0::Loops, two));
    scaling::check(what, n, |n| left_to_run(&units[&n], n));
}

#[test]
fn mixing_calls_of_a_long_chain_whose_form_does_not_show_it_ends_scales() {
    mixing_scales(
        "stage::mix on n calls of a chain of n functions whose form does not show it ends",
        false,
    );
}

#[test]
fn mixing_calls_of_functions_that_each_call_the_two_before_scales() {
    mixing_scales(
        "stage::mix on n calls of n functions, each calling the two before, whose form does \
         not show it ends",
        true,
    );
}

/// Each function's failing call is run once (COMPLEXITY.md row F43).
#[test]
fn failing_calls_of_a_long_chain_are_left_to_run_in_linear_time() {
    let n = 100;
    let units = scaling::inputs(n, |n| with_main(n, F0::Fails, false));
    scaling::check(
        "stage::mix on n calls of a chain of n functions whose every call fails",
        n,
        |n| left_to_run(&units[&n], n),
    );
}

/// Each call at a lambda fails at its own guard in constant time (COMPLEXITY.md row F43).
#[test]
fn failing_calls_no_answer_table_takes_are_run_as_written_in_linear_time() {
    let n = 100;
    let units = scaling::inputs(n, |n| at_a_lambda(n, F0::Fails));
    scaling::check(
        "stage::mix on n calls at a lambda of a chain of n functions whose every call fails",
        n,
        |n| left_to_run(&units[&n], n),
    );
}

/// `k = 2 + 2` is bound mixed, so each call of the split fails at its guard in constant time
/// (COMPLEXITY.md row F43).
#[test]
fn calls_reading_a_definition_the_trick_builds_are_split_in_linear_time() {
    let n = 100;
    let units = scaling::inputs(n, chain_reading_k);
    scaling::check(
        "stage::split of a function of n calls at a lambda of a chain of n functions reading \
         k = 2 + 2",
        n,
        |n| a_split_of_calls_reading_k(&units[&n], n),
    );
}

#[test]
fn remixing_a_root_held_inline_over_a_long_chain_scales() {
    let n = 400;
    let inputs = scaling::inputs(n, |n| (with_main(n, F0::Ends, false), sites(n)));
    scaling::check(
        "Remix::new and Remix::mix of n calls of a chain of n functions, the root held \
         inline",
        n,
        |n| a_root_remixed(&inputs[&n], n),
    );
}

/// Each call at `-0.0` reads the answer below it from a table (COMPLEXITY.md row F83).
#[test]
fn calls_at_minus_zero_of_a_long_chain_are_answered_in_linear_time() {
    let n = 200;
    let units = scaling::inputs(n, float_chain_at_minus_zero);
    scaling::check(
        "stage::mix on n calls at -0.0 of a chain of n functions over floats",
        n,
        |n| nothing_left(&units[&n]),
    );
}

/// Each call passing a function reads the answer below it from a table (COMPLEXITY.md row
/// F83).
#[test]
fn calls_passing_functions_of_a_long_chain_are_answered_in_linear_time() {
    let n = 200;
    let units = scaling::inputs(n, chain_passing_functions);
    scaling::check(
        "stage::mix on n calls g(fj, fj(1)) over a chain of n functions",
        n,
        |n| nothing_left(&units[&n]),
    );
}
