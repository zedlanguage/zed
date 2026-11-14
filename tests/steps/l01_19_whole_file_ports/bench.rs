//! Whole-file ports at the rule of low complexity (DESIGN.md Part G): the benchmarks of this
//! step, run by `tools/run_tests.sh --bench` and left out of its default run. Each check they
//! make besides the ratio is made at a small size by a correctness test of the file that
//! builds its input, named in the doc of each benchmark below; those of `main … with
//! handles(…)` (plan row SPEC-sigint-override) by the correctness tests in `signals.rs`.

use std::collections::BTreeMap;

use zed_tests::deep::resolved;
use zed_tests::scaling::{check, check_order, inputs};
use zedc::check::walk::check_text;
use zedc::rejection::Row;

use super::signals::{REPEATS_REPAIR, built, reads, repeats};
use super::{blocking, main_args, nonblocking, outside, ports, scaling, sharing};

/// Small instance: `scaling::a_lines_input_is_split_and_joined`.
#[test]
fn a_long_lines_input_is_split_and_joined_in_linear_time() {
    let n = 250_000;
    let texts = inputs(n, scaling::lines);
    check("splitting and joining n lines", n, |m| {
        scaling::split_and_join(&texts[&m], m);
    });
}

/// Small instance: `scaling::a_wave_reads_the_last_of_its_lines`.
#[test]
fn a_wave_reading_the_last_of_many_lines_scales() {
    let n = 200_000;
    let waves = inputs(n, scaling::last_line_wave);
    check("a wave over n lines", n, |m| {
        let (program, input) = &waves[&m];
        scaling::reads_the_last_line(program, input, m);
    });
}

/// Small instance: `scaling::a_record_of_reads_is_written_and_read_back`.
#[test]
fn a_record_of_many_reads_is_written_and_read_back_in_linear_time() {
    let n = 120_000;
    let records = inputs(n, scaling::record_of_reads);
    check("writing and reading back a record of n reads", n, |m| {
        scaling::reads_back(&records[&m], m);
    });
}

/// Small instance: `scaling::a_wave_reading_distinct_paths_records_each`.
#[test]
fn a_wave_reading_many_distinct_paths_scales() {
    let n = 6_000;
    let programs = inputs(n, scaling::distinct_paths);
    check("a wave reading n paths", n, |m| {
        scaling::records_each_path(&programs[&m], m);
    });
}

/// Small instance: `scaling::lines_read_in_small_reads_are_found_whole`.
#[test]
fn reading_lines_in_small_reads_scales() {
    let n = 1_000_000;
    let texts = inputs(n, scaling::mixed_lines);
    check("reading n lines in reads of 7 bytes", n, |m| {
        scaling::reads_in_small_pieces(&texts[&m], m);
    });
}

/// A chain of n functions, each calling the next, the last calling a function value, decides
/// in linear time: one search backward over the calls, each function visited once. Small
/// instance: `blocking::every_function_of_a_chain_of_calls_blocks`.
#[test]
fn a_long_chain_of_calls_is_decided_in_linear_time() {
    let n = 16_000;
    let units = inputs(n, |m| {
        let text = blocking::call_chain(m);
        let (stmts, res) = resolved(&text);
        (text, stmts, res)
    });
    check_order("deciding a chain of n calls", n, 1, |m| {
        let (text, stmts, res) = &units[&m];
        blocking::decides_the_chain(text, stmts, res, m);
    });
}

/// Small instance: `main_args::the_status_of_an_if_chain_is_checked_and_given`.
#[test]
fn the_status_of_a_long_if_chain_is_checked_in_linear_time() {
    let n = 1_200;
    let srcs = inputs(n, main_args::chain);
    check("checking the status of an if chain of n branches", n, |m| {
        main_args::loads_the_chain(&srcs[&m]);
    });
}

/// Small instance: `main_args::the_reads_after_several_mains_are_built`.
#[test]
fn building_the_reads_after_n_mains_is_linear() {
    let n = 4_500;
    let srcs = inputs(n, main_args::mains_then_reads);
    check("building n field reads after n mains", n, |m| {
        main_args::builds_the_reads(&srcs[&m], m);
    });
}

/// Small instance: `nonblocking::every_function_of_a_marked_chain_has_its_error`.
#[test]
fn a_long_marked_chain_is_checked_in_linear_time() {
    let n = 14_000;
    let units = inputs(n, |m| {
        let text = nonblocking::marked_chain(m);
        let (stmts, res) = resolved(&text);
        (text, stmts, res)
    });
    check_order("checking n marked functions", n, 1, |m| {
        let (text, stmts, res) = &units[&m];
        nonblocking::checks_the_marks(text, stmts, res, m);
    });
}

/// Small instance: `outside::reads_of_main_files_before_and_after_main_load`.
#[test]
fn reads_of_main_files_outside_main_load_in_linear_time() {
    let n = 500;
    let srcs = inputs(n, outside::helpers);
    check("loading n helpers that read main::files", n, |m| {
        outside::loads_the_helpers(&srcs[&m]);
    });
}

/// The pass that finds the output ports is timed alone: in the whole check it is too small a
/// part for a slower pass to show. Small instance:
/// `ports::a_chain_of_helpers_passing_a_port_writes_once`.
#[test]
fn a_chain_of_helpers_passing_a_port_scales() {
    let n = 8_000;
    let units = inputs(n, |m| {
        let text = ports::helper_chain(m);
        let (stmts, res) = resolved(&text);
        (text, stmts, res)
    });
    // The program is accepted, as a whole.
    let (text, stmts, res) = &units[&n];
    let info = check_text(stmts, res, Some(text));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    check("finding the output ports of n helpers", n, |m| {
        let (text, stmts, res) = &units[&m];
        ports::finds_the_ports(text, stmts, res, m);
    });
}

/// Small instance: `sharing::a_wave_and_its_replay_share_the_input`.
#[test]
fn a_wave_over_n_lines_and_its_replay_share_the_input_and_scale() {
    let n = 200_000;
    let waves = inputs(n, |m| {
        let input = BTreeMap::from([("m.stdin".to_string(), sharing::lines(m))]);
        (sharing::last_line(m), input)
    });
    check("a wave over n lines and its replay", n, |m| {
        let (program, input) = &waves[&m];
        sharing::replays_sharing_the_input(program, input);
    });
}

/// Small instance: `sharing::zedc_run_reads_a_file_of_lines_on_stdin`.
#[test]
fn zedc_run_reading_a_file_of_n_lines_on_stdin_scales() {
    let n = 200_000;
    let dir = std::env::temp_dir().join("zed-l01-19-sharing-scaling");
    std::fs::create_dir_all(&dir).unwrap();
    let program = dir.join("first.zed");
    std::fs::write(&program, sharing::FIRST_LINE).unwrap();
    let files = inputs(n, |m| {
        let path = dir.join(format!("input-{m}.txt"));
        std::fs::write(&path, &*sharing::lines(m)).unwrap();
        path
    });
    check("zedc run reading a file of n lines on stdin", n, |m| {
        sharing::runs_on_the_file(&program, &files[&m]);
    });
    std::fs::remove_file(&program).unwrap();
    for path in files.values() {
        std::fs::remove_file(path).unwrap();
    }
}

#[test]
fn a_handles_with_n_repeated_arguments_is_rejected_in_linear_time() {
    const N: usize = 60_000;
    let srcs = inputs(N, repeats);
    check("rejecting handles with n repeated arguments", N, |n| {
        let error = built(&srcs[&n]);
        assert!(error.message.ends_with(REPEATS_REPAIR), "{}", error.message);
    });
}

#[test]
fn n_reads_of_signals_without_handles_are_rejected_in_linear_time() {
    const N: usize = 18_000;
    let srcs = inputs(N, reads);
    check("rejecting n reads of m.signals without handles", N, |n| {
        assert_eq!(built(&srcs[&n]).row, Some(Row::SignalsReadWithoutHandles));
    });
}
