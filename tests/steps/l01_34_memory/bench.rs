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

/// Small instance: `scaling::a_nest_of_ifs_is_planned_and_run_to_the_kernels_value`.
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

/// Small instance: `scaling::a_nest_of_ifs_is_planned_and_run_to_the_kernels_value`.
#[test]
fn running_a_deep_nest_is_linear_in_its_depth() {
    use zed_tests::step_helpers::l01_33_lowering::nest;
    let n = 8_000;
    let pair = planned_pair(n, |d| lower(&nest(d)).unwrap());
    runs_in_linear_time("running n nested `if`s", n, &pair);
}

/// Small instance: `scaling::a_nested_value_is_allocated_and_freed_a_cell_a_level`.
#[test]
fn allocating_and_freeing_a_deep_value_is_linear_in_its_depth() {
    let n = 300_000;
    let pair = planned_pair(n, |d| lower(&scaling::wrap_deep(d)).unwrap());
    runs_in_linear_time("allocating and freeing a value n deep", n, &pair);
}

/// Small instance: `scaling::closures_capturing_closures_are_called_and_dropped`.
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

/// Small instance: `scaling::closures_capturing_closures_are_called_and_dropped`.
#[test]
fn calling_and_dropping_a_closure_chain_is_linear_in_its_depth() {
    let n = 10_000;
    let pair = planned_pair(n, |d| lower(&scaling::closure_chain(d)).unwrap());
    runs_in_linear_time("calling and dropping a closure chain n deep", n, &pair);
}

// The deep shapes of `scaling.rs` at depths about 20% past the ones at which the recursive
// planner and machine before T2-mid (578fbe70e) overflowed a 2 MiB stack in the dev profile,
// measured 2026-11-14: a nest of ifs, a push under ifs and a closure chain at 1,046 (1,031
// ran), a value at 11,875 (11,750 ran). Each is lowered on the test's stack and planned and run
// on a 2 MiB thread.

/// Small instance: `scaling::a_nest_of_ifs_is_planned_and_run_to_the_kernels_value`.
#[test]
fn a_nest_of_ifs_1250_deep_is_planned_and_run_on_a_2_mib_stack() {
    use zed_tests::step_helpers::l01_33_lowering::nest;
    let t = nest(1_250);
    let want = Evaluator::new(World::new()).run(&t).unwrap();
    let g = lower(&t).unwrap();
    let v = on_small_stack(|| {
        let p = memory::plan(&g, true);
        memory::run(&g, &p, &mut Evaluator::new(World::new()))
            .unwrap()
            .0
    });
    assert_eq!(v, want);
}

/// Small instance: `scaling::a_push_under_nested_ifs_is_planned_and_run_once`.
#[test]
fn a_push_1250_regions_deep_is_planned_and_run_on_a_2_mib_stack() {
    use zed_tests::step_helpers::l01_33_lowering::push_under_ifs;
    let g = lower(&push_under_ifs(1_250)).unwrap();
    on_small_stack(|| {
        let p = memory::plan(&g, true);
        let mut ev = Evaluator::new(World::new().output("stdout"));
        memory::run(&g, &p, &mut ev).unwrap();
        assert_eq!(ev.world.log("stdout").len(), 1);
    });
}

/// Small instance: `scaling::a_nested_value_is_allocated_and_freed_a_cell_a_level`.
#[test]
fn a_value_14000_deep_is_allocated_and_freed_on_a_2_mib_stack() {
    let g = lower(&scaling::wrap_deep(14_000)).unwrap();
    let s = on_small_stack(|| {
        let p = memory::plan(&g, true);
        memory::run(&g, &p, &mut Evaluator::new(World::new()))
            .unwrap()
            .1
    });
    assert_eq!((s.allocations, s.frees), (14_000, 14_000), "{s:?}");
}

/// Small instance: `scaling::closures_capturing_closures_are_called_and_dropped`.
#[test]
fn closures_capturing_closures_1250_deep_are_called_and_dropped_on_a_2_mib_stack() {
    let g = lower(&scaling::closure_chain(1_250)).unwrap();
    let v = on_small_stack(|| {
        let p = memory::plan(&g, true);
        memory::run(&g, &p, &mut Evaluator::new(World::new()))
            .unwrap()
            .0
    });
    assert_eq!(v, zed_kernel::value::Value::from(7i64));
}
