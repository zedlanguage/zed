//! Benchmarks of `path_check`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn the_checker_on_a_chain_of_difference_tests_is_linear() {
    checked_in_linear_work("chain of n difference tests, zedc check", chain);
}

#[test]
fn the_checker_on_a_raised_head_is_linear() {
    checked_in_linear_work("n raises of a chain's head, zedc check", raise);
}

#[test]
fn the_checker_reading_names_bound_under_a_chain_is_linear() {
    checked_in_linear_work("n names bound under a chain, one input, zedc check", |n| {
        reads(n, false)
    });
}
