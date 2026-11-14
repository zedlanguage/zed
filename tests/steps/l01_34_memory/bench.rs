//! The memory planner and the machine at the rule of low complexity (DESIGN.md Part G): the
//! benchmarks of this step, run by `tools/run_tests.sh --bench` and left out of its default
//! run, one check each. Each shape they plan or run is planned and run at a small size, its
//! value checked against the kernel's, by the correctness test named in its doc.

use zed_kernel::{Evaluator, World};
use zed_tests::deep::on_small_stack;
use zed_tests::scaling::{FACTOR, check_order, inputs};
use zedc::zir::Region;
use zedc::zir::lower::lower;
use zedc::zir::memory::{self, Mode, Plan};

use super::{binders, chains, places, scaling};

/// `g` planned with fusion, at the two sizes of a check, `n` and `8n`.
fn planned_pair(n: usize, build: impl Fn(usize) -> Region) -> [(Region, Plan); 2] {
    [n, FACTOR * n].map(|d| {
        let g = build(d);
        let p = memory::plan(&g, true);
        (g, p)
    })
}

/// Checks that running the plans of `pair`, built at `n` and `8n`, is of order 1 in `n`, on a
/// small stack.
fn runs_in_linear_time(what: &str, n: usize, pair: &[(Region, Plan); 2]) {
    on_small_stack(|| {
        check_order(what, n, 1, |d| {
            let (g, p) = if d == n { &pair[0] } else { &pair[1] };
            memory::run(g, p, &mut Evaluator::new(World::new())).unwrap();
        });
    });
}

/// Matching an invoice `n` deep and keeping every line, held once: each spine cell freed,
/// each line moved out. Small instances: `binders::every_set_of_kept_lines_of_a_deep_match_
/// is_released_exactly` and `binders::a_held_once_invoice_moves_its_kept_lines_out_with_no_
/// count_write`.
#[test]
fn a_binder_at_every_level_of_a_deep_match_held_once_scales() {
    let n = 20_000;
    let pair = planned_pair(n, |d| {
        let all: Vec<usize> = (0..=d).collect();
        lower(&binders::read_lines(d, &all, false)).unwrap()
    });
    runs_in_linear_time("a match keeping each of n levels, held once", n, &pair);
}

/// [`a_binder_at_every_level_of_a_deep_match_held_once_scales`] with the invoice shared: each
/// line given a reference. Small instance: `binders::every_set_of_kept_lines_of_a_deep_match_
/// is_released_exactly`.
#[test]
fn a_binder_at_every_level_of_a_deep_match_shared_scales() {
    let n = 20_000;
    let pair = planned_pair(n, |d| {
        let all: Vec<usize> = (0..=d).collect();
        lower(&binders::read_lines(d, &all, true)).unwrap()
    });
    runs_in_linear_time("a match keeping each of n levels, shared", n, &pair);
}

/// Small instance: `chains::nested_ifs_hand_each_name_owned_down_to_the_tuple`.
#[test]
fn nested_ifs_reading_four_names_plan_in_linear_time() {
    let n = 6_000;
    let gs = inputs(n, |d| lower(&chains::nest(4, d)).unwrap());
    check_order("planning 4 names read under n nested `if`s", n, 1, |d| {
        memory::plan(&gs[&d], true);
    });
}

/// Small instance: `chains::nested_ifs_hand_each_name_owned_down_to_the_tuple`.
#[test]
fn many_names_read_under_nested_ifs_plan_in_linear_time() {
    let n = 8_000;
    let gs = inputs(n, |k| lower(&chains::nest(k, 4)).unwrap());
    check_order("planning n names read under 4 nested `if`s", n, 1, |k| {
        memory::plan(&gs[&k], true);
    });
}

/// Small instance: `chains::capture_chains_borrow_the_captured_string_for_every_call`.
#[test]
fn capture_chains_in_nested_arms_plan_in_linear_time() {
    let n = 3_000;
    let gs = inputs(n, |d| lower(&chains::capture_chain(d, false)).unwrap());
    check_order(
        "planning 2 calls of a captured function in each of n nested arms",
        n,
        1,
        |d| {
            memory::plan(&gs[&d], true);
        },
    );
}

/// Small instance: `chains::capture_chains_borrow_the_captured_string_for_every_call`.
#[test]
fn capture_chains_in_nested_lambdas_plan_in_linear_time() {
    let n = 6_000;
    let gs = inputs(n, |d| lower(&chains::capture_chain(d, true)).unwrap());
    check_order(
        "planning 2 calls of a captured function in each of n nested lambdas",
        n,
        1,
        |d| {
            memory::plan(&gs[&d], true);
        },
    );
}

/// Small instance: `chains::a_call_chain_borrows_down_to_a_borrowing_leaf_and_owns_down_to_a_
/// consuming_one`.
#[test]
fn call_chains_plan_in_linear_time() {
    let n = 2_000;
    let gs = inputs(n, |d| lower(&chains::call_chain(d, false)).unwrap());
    check_order(
        "planning n functions each calling the one before twice",
        n,
        1,
        |d| {
            let g = &gs[&d];
            let p = memory::plan(g, true);
            assert_eq!(p[chains::body_path(g, 0).as_str()].args, [Mode::Borrowed]);
        },
    );
}

/// Running `n` lambdas, each called twice and once handed to the kernel inside a closure, is
/// linear in `n`: each node occurrence finds its one-node region by its id. Small instance:
/// `places::the_machine_keeps_nodes_by_place_not_address`.
#[test]
fn running_many_node_occurrences_is_linear() {
    let n = 2_000;
    let pair = planned_pair(n, |m| lower(&places::callers(m, &mut || {})).unwrap());
    runs_in_linear_time(
        "running n lambdas, each node by its occurrence id",
        n,
        &pair,
    );
}

/// Small instance: `scaling::a_nest_of_ifs_1250_deep_is_planned_and_run_on_a_2_mib_stack`.
#[test]
fn planning_a_deep_nest_is_linear_in_its_depth() {
    use zed_tests::step_helpers::l01_33_lowering::nest;
    let n = 10_000;
    let gs = inputs(n, |d| lower(&nest(d)).unwrap());
    on_small_stack(|| {
        check_order("planning n nested `if`s", n, 1, |d| {
            memory::plan(&gs[&d], true);
        });
    });
}

/// Small instance: `scaling::a_nest_of_ifs_1250_deep_is_planned_and_run_on_a_2_mib_stack`.
#[test]
fn running_a_deep_nest_is_linear_in_its_depth() {
    use zed_tests::step_helpers::l01_33_lowering::nest;
    let n = 8_000;
    let pair = planned_pair(n, |d| lower(&nest(d)).unwrap());
    runs_in_linear_time("running n nested `if`s", n, &pair);
}

/// Small instance: `scaling::a_value_14000_deep_is_allocated_and_freed_on_a_2_mib_stack`.
#[test]
fn allocating_and_freeing_a_deep_value_is_linear_in_its_depth() {
    let n = 300_000;
    let pair = planned_pair(n, |d| lower(&scaling::wrap_deep(d)).unwrap());
    runs_in_linear_time("allocating and freeing a value n deep", n, &pair);
}

/// Small instance: `scaling::closures_capturing_closures_1250_deep_are_called_and_dropped_on_
/// a_2_mib_stack`.
#[test]
fn planning_a_closure_chain_is_linear_in_its_depth() {
    let n = 12_000;
    let gs = inputs(n, |d| lower(&scaling::closure_chain(d)).unwrap());
    on_small_stack(|| {
        check_order("planning a closure chain n deep", n, 1, |d| {
            memory::plan(&gs[&d], true);
        });
    });
}

/// Small instance: `scaling::closures_capturing_closures_1250_deep_are_called_and_dropped_on_
/// a_2_mib_stack`.
#[test]
fn calling_and_dropping_a_closure_chain_is_linear_in_its_depth() {
    let n = 10_000;
    let pair = planned_pair(n, |d| lower(&scaling::closure_chain(d)).unwrap());
    runs_in_linear_time("calling and dropping a closure chain n deep", n, &pair);
}
