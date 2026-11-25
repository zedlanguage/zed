//! The oracle at the rule of low complexity (DESIGN.md Part G): the benchmarks of this step,
//! run by `tools/run_tests.sh --bench` and left out of its default run. Each input is built,
//! and each unit elaborated, before it is measured. Each check they make besides the ratio is
//! made at a small size by the correctness test named in its doc.

use zed_tests::scaling::{check, check_n_log_n, inputs};

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

/// Small instances: `alone::a_chain_whose_last_binding_stops_is_compared` and, for the cost,
/// `alone::the_search_for_the_stop_binds_each_definition_a_bounded_number_of_times`.
///
/// The work is O(n log n): O(n) lets in all (proof at `oracle::Runs::first_stop`), each
/// O(log n) (COMPLEXITY.md K8), so the n log n prediction 8·ln(8n)/ln(n) at n = 20,000 is
/// 9.68. Measured 2026-11-20 (BENCH-over-nlogn-prediction): 10.24 times the instructions on
/// 929ccd72d, when the search for the stop ran each prefix whole (O(n log² n), prediction
/// 8·(ln 8n/ln n)² = 11.71), and 8.58 times the instructions, 7.93 times the bytes, with the
/// fix (load5 43).
#[test]
fn a_chain_that_stops_scales() {
    let units = inputs(20_000, alone::stopped_chain);
    check("a chain of n bindings, the last stopping", 20_000, |k| {
        alone::the_last_stops(&units[&k], k);
    });
}

/// Small instance: `alone::bindings_that_share_a_cone_are_compared`.
#[test]
fn bindings_that_share_a_cone_scale() {
    let units = inputs(100, alone::shared_cone);
    check("n bindings reaching n functions, and a stop", 100, |k| {
        alone::the_cone_is_compared(&units[&k], k);
    });
}

/// Small instances: `alone::stops_that_reach_functions_end_the_walk_at_the_second` and
/// `alone::a_second_stop_through_functions_is_not_compared`.
///
/// Proof that the work is O(n log n), for the unit of `n` functions and `2n` bindings:
/// 1. The engine's runs bind at most 13 lets a function and 44 a run for the prelude over
///    `O(log n)` runs, as counted exactly by
///    `alone::the_search_for_a_stop_through_functions_binds_them_once_a_probe`: the tuple of
///    all the bindings, the doubling prefixes up to the stop `b0` (at most twice the prefix
///    that stops), three runs that confirm `b0` (`first_stop`), and three runs after it that
///    end the walk. The interpreter's runs, of the tuple and of the same walk, bind as many,
///    and one more run of the window locates `b0`. So the lets are O(n).
/// 2. A let, a lookup of a name and a closure's capture each cost O(log n) in the kernel's
///    environment, an AVL tree of the names in scope (COMPLEXITY.md K8, `eval/env.rs`): one
///    path from the root, of height at most 1.44 log2(n + 2). A name is compared in O(1), as
///    it is at most 8 bytes for n up to 10^6 (`f`, `b`, `c` and a decimal index).
/// 3. A call `f(n−1)(j)` runs one body, whose `if false` arm is not taken: O(log n).
/// 4. The rest is linear: the walk's visited set and marks (`reads_a_stop`, `leave`), one
///    entry a definition, and the report's `2n − 3` lines.
///
/// So O(n log n), and the ratio at n and 8n is held to that of n log n, 10.13 at 2,500
/// (`check_n_log_n`). Before SCALE-near-oracle-stops the search halved its window, binding
/// the `n` functions once per probe, O(n log² n), though this comment said n log n.
/// It measured 9.79 times the instructions at 2,500 and 20,000, under 10.5 only because the
/// extra log factor has a small constant; after it, 8.54 and 8.55 times on two runs.
#[test]
fn stops_that_reach_functions_scale() {
    let units = inputs(2_500, alone::stops_reaching_functions);
    check_n_log_n("n stops each reaching n functions", 2_500, |k| {
        alone::the_walk_ends_at_the_second_stop(&units[&k], k);
    });
}

/// Small instances: `counts::live_cells_are_listed_by_type_and_allocating_node` and
/// `counts::the_live_cells_of_many_nodes_are_each_listed`.
///
/// O(n log g) for `g` = n / 8 + 1 allocating nodes: `Heap::survivors` counts each cell into an
/// ordered map by type and node, since the listing is in that order, O(log g) per cell. With
/// `g` growing as `n`, `8 log2(8g) / log2 g` predicts 9.42 at
/// `n` = 10^6; measured on 2026-11-21 (PERF-ratios-over-9-l0136) 9.4, 9.4 and 9.2 times the
/// instructions at 10^6, 2 * 10^6 and 4 * 10^6 cells, no growth with `n`.
#[test]
fn listing_the_live_cells_scales() {
    let n = 1_000_000;
    let heaps = inputs(n, counts::heap);
    check("listing n live cells by type and node", n, |m| {
        counts::lists_every_cell(&heaps[&m], m);
    });
}
