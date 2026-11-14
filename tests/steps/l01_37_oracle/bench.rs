//! The oracle at the rule of low complexity (DESIGN.md Part G): the benchmarks of this step,
//! run by `tools/run_tests.sh --bench` and left out of its default run. Each input is built,
//! and each unit elaborated, before it is measured. Each check they make besides the ratio is
//! made at a small size by the correctness test named in its doc.

use zed_tests::scaling::{check, inputs};

use super::{alone, counts, scaling};

/// Small instance: `scaling::the_inputs_are_compared_as_they_should_be`.
#[test]
fn a_unit_of_many_bindings_scales() {
    let units = inputs(1_000, scaling::numbers);
    check("a unit of n bindings, run natively", 1_000, |k| {
        scaling::agree_natively(&units[&k], k);
    });
}

/// Small instance: `scaling::the_inputs_are_compared_as_they_should_be`.
#[test]
fn a_unit_of_many_bindings_scales_in_the_interpreter() {
    let units = inputs(20_000, scaling::numbers);
    check("a unit of n bindings, each mismatched", 20_000, |k| {
        scaling::each_off_by_one(&units[&k], k);
    });
}

/// Small instance: `scaling::the_inputs_are_compared_as_they_should_be`.
#[test]
fn a_wave_of_many_lines_scales() {
    let input = inputs(150_000, scaling::lines);
    check("a wave of n lines", 150_000, |k| {
        scaling::echoes_the_first_line(&input[&k]);
    });
}

/// `Report::add` takes the report it adds, so each run builds its own, at linear cost. Small
/// instance: `scaling::the_inputs_are_compared_as_they_should_be`.
#[test]
fn a_report_of_many_mismatches_scales() {
    check("a report of n mismatches, built and added", 800_000, |k| {
        scaling::adds_a_report(k);
    });
}

/// The replay of each row finds its failure by a lookup, not a pass over the failures. Small
/// instance: `scaling::wrong_rows_are_replayed`.
#[test]
fn many_wrong_rows_are_replayed() {
    let texts = inputs(1_500, scaling::wrong_rows);
    check("a table of n wrong rows, each replayed", 1_500, |k| {
        scaling::replays_each_row(&texts[&k], k);
    });
}

/// Small instance: `scaling::a_chain_of_bindings_is_compared`.
#[test]
fn a_chain_of_bindings_scales_in_the_interpreter() {
    let units = inputs(7_000, scaling::chain);
    check("a chain of n bindings, each mismatched", 7_000, |k| {
        scaling::each_off_by_one(&units[&k], k);
    });
}

/// Small instance: `scaling::a_chain_of_bindings_is_compared`.
#[test]
fn a_chain_of_bindings_scales_natively() {
    let units = inputs(1_000, scaling::chain);
    check("a chain of n bindings, run natively", 1_000, |k| {
        scaling::agree_natively(&units[&k], k);
    });
}

/// Small instance: `alone::a_chain_whose_last_binding_stops_is_compared`.
#[test]
fn a_chain_that_stops_scales() {
    let units = inputs(20_000, alone::stopped_chain);
    check("a chain of n bindings, the last stopping", 20_000, |k| {
        alone::the_last_stops(&units[&k], k);
    });
}

/// Small instances: `alone::stops_that_reach_functions_end_the_walk_at_the_second` and
/// `alone::a_second_stop_through_functions_is_not_compared`.
///
/// The kernel's environment (COMPLEXITY.md K8) costs `O(log n)` per binding, so the work is
/// `n log n`: the least of three runs at 8n against n was 10.05 to 10.55 times at n = 250 to
/// 4,000 (2026-11-14), near the limit at every size (plan row ORACLE-env-nlogn).
#[test]
fn stops_that_reach_functions_scale() {
    let units = inputs(2_500, alone::stops_reaching_functions);
    check("n stops each reaching n functions", 2_500, |k| {
        alone::the_walk_ends_at_the_second_stop(&units[&k], k);
    });
}

/// Small instances: `counts::live_cells_are_listed_by_type_and_allocating_node` and
/// `counts::the_live_cells_of_many_nodes_are_each_listed`.
#[test]
fn listing_the_live_cells_scales() {
    let n = 1_000_000;
    let heaps = inputs(n, counts::heap);
    check("listing n live cells by type and node", n, |m| {
        counts::lists_every_cell(&heaps[&m], m);
    });
}
