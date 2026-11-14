//! How long left-recursive parsing takes (COMPLEXITY.md F35): a growth matches again only the
//! rules at its token that read a seed still growing, so a chain is linear in its length. The
//! benchmarks of the left recursion, run by `tools/run_tests.sh --bench`; `scaling.rs` parses
//! each of their inputs at small sizes.

use zed_tests::scaling::check_order;
use zedc::parse::Grammar;

use crate::scaling::{
    CYCLE_UNDER_A_LIST, Case, FAILED_ALTERNATIVE, FINISHED_RUNG, LONG_CHAIN, LOOKAHEAD_BEFORE,
    LOOKAHEAD_EVERY_TOKEN, LOOP_INSIDE, SHORT_CHAINS, STALE_RULE, lexed, parses,
};

/// Parsing the input of `case` is of order n^`power` (n log n for 1), timed at `n` and `8n`.
fn scales(what: &str, case: &Case, n: usize, power: u32) {
    let g = Grammar::read(&[case.grammar]).unwrap();
    let inputs = lexed(case, &[n, 8 * n]);
    check_order(what, n, power, |m| parses(&g, case, &inputs[&m]));
}

#[test]
fn a_long_chain_of_operators_is_linear() {
    scales("a chain of n operators", &LONG_CHAIN, 4_000, 1);
}

#[test]
fn many_short_chains_are_linear() {
    scales("n lines of short chains", &SHORT_CHAINS, 2_000, 1);
}

#[test]
fn a_long_alternative_that_failed_is_not_walked_again_at_each_growth() {
    scales(
        "a list of n names and n operators",
        &FAILED_ALTERNATIVE,
        1_000,
        1,
    );
}

#[test]
fn a_lookahead_before_the_left_recursion_is_matched_once() {
    scales("a check over n tokens", &LOOKAHEAD_BEFORE, 1_000, 1);
}

#[test]
fn a_finished_rung_is_not_matched_again_by_the_rung_above() {
    scales(
        "a list of n numbers and n operators",
        &FINISHED_RUNG,
        1_000,
        1,
    );
}

#[test]
fn a_growth_leaves_a_stale_rule_at_a_later_token_good() {
    scales("a list of n numbers and n operators", &STALE_RULE, 1_000, 1);
}

#[test]
fn a_loop_written_inside_the_left_recursive_rule_is_quadratic() {
    scales("a loop over n tokens", &LOOP_INSIDE, 250, 2);
}

#[test]
fn lookahead_over_a_left_recursive_rule_at_every_token_is_quadratic() {
    scales("lookahead at n tokens", &LOOKAHEAD_EVERY_TOKEN, 250, 2);
}

#[test]
fn a_cycle_of_two_rules_under_a_list_at_the_growing_token_is_quadratic() {
    scales(
        "a list of n numbers and n operators",
        &CYCLE_UNDER_A_LIST,
        250,
        2,
    );
}
