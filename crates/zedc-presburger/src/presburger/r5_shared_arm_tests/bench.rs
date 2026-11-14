//! The benchmarks of `r5_shared_arm_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

#[test]
fn shared_flat_arms_with_many_guard_rows_are_read_once() {
    scaling::check_order(
        "shared flat arms with redundant guard rows",
        125_000,
        1,
        |n| {
            assert!(GuardedChain::of(&parts(n, false)).is_some());
        },
    );
}

// n guard rows repeated in each of n shared arms were read once per disjunction by `pick_by`'s
// first reading and taken again by its search: 63 times the bytes at 8n on main before
// [`Parts::held`] (cross-review R5-CX4).
#[test]
fn shared_two_input_arms_do_not_slow_the_old_point_path() {
    scaling::check_order(
        "shared two-input arms with redundant guard rows",
        125,
        1,
        |n| {
            assert_eq!(has_point(parts(n, true)), Ok(true));
        },
    );
}

// The same with the arm that fails at the point first: its rows are read once, by
// [`Parts::failed`], not once per disjunction.
#[test]
fn a_shared_failing_arm_read_first_is_read_once() {
    scaling::check_order(
        "shared two-input arms, the failing arm first",
        125,
        1,
        |n| {
            assert_eq!(has_point(parts_in(n, true, true)), Ok(true));
        },
    );
}
