//! The benchmarks of `cells_scaling`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 0.5 s and a
//! piece stays under 20 s.

use super::*;

fn no_point_scales(what: &str, n: usize, make: impl Fn(usize) -> Formula) {
    let fs = scaling::inputs(n, make);
    scaling::check_order(what, n, 1, |m| {
        assert_eq!(decide(&fs[&m]), Ok(false), "{m}");
    });
}

/// Control (63662d8d, not kept): fails by the 60 s limit; at n = 250 the base takes over
/// 60 s alone.
#[test]
fn a_part_held_by_many_disjunctions_is_decided_in_near_linear_work() {
    no_point_scales("a part held by many disjunctions", 4000, |n| {
        shared_holders(n, false)
    });
}

/// Control (63662d8d, not kept): fails by the 60 s limit, as above.
#[test]
fn two_parts_held_by_many_disjunctions_are_decided_in_near_linear_work() {
    no_point_scales("two parts held by many disjunctions", 4000, |n| {
        shared_holders(n, true)
    });
}

/// Control (63662d8d, not kept): fails; the base solves the `n` equalities once per cell,
/// and at sizes 62 and 496 its first runs allocate 47.6 times the bytes.
#[test]
fn cells_in_few_classes_are_solved_once_per_class() {
    no_point_scales("cells in three classes", 992, interface);
}

/// Control (main f0abc6b6e, not kept): killed at the 60 s limit.
#[test]
fn a_chain_over_one_shared_set_is_decided_in_linear_work() {
    no_point_scales("a chain over one shared set", 3000, |n| holders_chain(n, 1));
}

/// [`has_point`] on the parts `make` gives, at n and 8n, with the answer `answer`.
fn has_point_scales(what: &str, n: usize, answer: bool, make: impl Fn(usize) -> Parts + Sync) {
    scaling::check_order(what, n, 1, |m| {
        assert_eq!(has_point(make(m)), Ok(answer), "{m}")
    });
}

/// The chain with a point at `i = 0`. Control (main f0abc6b6e, not kept): 58.3 times the
/// bytes at 8n.
#[test]
fn a_chain_over_one_shared_set_with_a_point_is_decided_in_linear_work() {
    has_point_scales(
        "parts of a chain over one shared set, with a point",
        12_500,
        true,
        |n| holders_parts(n, Some(0), false),
    );
}

/// The chain with `i` odd and `q_n` free, so no cell of the shared set has a point.
/// Control (main f0abc6b6e, not kept): 58.3 times the bytes at 8n.
#[test]
fn a_chain_over_one_shared_set_with_no_point_on_it_is_decided_in_linear_work() {
    has_point_scales(
        "parts of a chain over one shared set, odd",
        8000,
        false,
        |n| holders_parts(n, None, true),
    );
}
