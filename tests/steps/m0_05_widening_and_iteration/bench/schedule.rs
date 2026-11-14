//! The scheduler's time on a program of n groups, linear in the facts and reads; what
//! [`run_scaling`] asserts is checked at small sizes by
//! `schedule::the_scaling_program_is_solved_at_small_sizes`.

use zed_tests::scaling;

use crate::schedule::run_scaling;

/// The search is linear in the facts and reads (DESIGN.md, "The algorithm"): 7.96 times the
/// instructions and 8.00 times the bytes at 8n (2026-11-13). Negative control, run once and not
/// committed: resetting the refusal marks over every node instead of over the component's
/// members, O(n) for each of n / 7 refusals, took 29.2 times the instructions and failed.
#[test]
fn scaling() {
    scaling::check("the scheduler of checks and evaluations", 4000, run_scaling);
}
