//! How the reference programs scale with their input, run by `tools/run_tests.sh --bench` and
//! left out of its default run (TEST-bench-move-rest). Each input is built before timing, at n
//! and 8n. Most are linear up to a sort or a tree lookup; the ones that are not name why at their
//! input in `scaling.rs`: the power is what the problem forces, such as a full table in the
//! output, not the algorithm of the corpus program. `scaling.rs` runs each input at small sizes.

mod chains;
mod digits;

use std::fs;

use zed_tests::scaling::{check_order, check_proved_cost};

use crate::scaling::*;

/// Checks reference `input.number` at n and 8n on the input it builds for each size.
fn scales(input: &Input) {
    scales_by(input, |run| {
        check_order(input.what, input.n, input.power, run)
    });
}

/// Writes the inputs of reference `input.number` at n and 8n, hands `check` the run at a size,
/// and removes the inputs.
fn scales_by(input: &Input, check: impl FnOnce(&(dyn Fn(usize) + Sync))) {
    let Input {
        what,
        number,
        n,
        input,
        ..
    } = *input;
    for m in [n, zed_tests::scaling::FACTOR * n] {
        fs::write(input_path(what, m), input(m)).expect("writing an input");
    }
    check(&|m| {
        let (_, result) = zed_corpus_ref::run(number, &input_path(what, m));
        assert_eq!(result, Ok(()), "{what}");
    });
    for m in [n, zed_tests::scaling::FACTOR * n] {
        fs::remove_file(input_path(what, m)).expect("removing an input");
    }
}

/// The bytes reference 15 prints on `SPREADSHEET_ALL_DEPEND` at `n`: after each of the first n
/// lines, `c{j}=1` for each cell defined so far, and after each edit `s = {i}`, `c{j}={i+1}` for
/// all n cells and `s={i}`; the entries of a line apart by spaces, and a newline.
fn spreadsheet_all_depend_output(n: usize) -> usize {
    let digits = |x: usize| x.to_string().len();
    let (mut total, mut line) = (0, 0);
    for i in 0..n {
        line += 3 + digits(i);
        total += line + i + 1;
    }
    let names: usize = (0..n).map(|j| 2 + digits(j)).sum();
    for i in 0..n {
        total += names + n * digits(i + 1) + 2 + digits(i) + n + 1;
    }
    total
}

/// The capacity of the `String` reference 15 prints to at `n`: grown from 8 bytes by doubling,
/// the least power of two that holds the output.
fn spreadsheet_all_depend_buffer(n: usize) -> f64 {
    spreadsheet_all_depend_output(n).next_power_of_two() as f64
}

/// Proof of the cost, for n cells and n edits, `out(n)` bytes printed
/// (`spreadsheet_all_depend_output`, n² values of up to `log10 n + 1` digits, so of order
/// n² log n, which the n² values printed force):
/// 1. The first n lines each set one formula and walk the one cell that reads nothing: O(1)
///    each, besides the line printed.
/// 2. An edit of `s` walks its n readers once each (`Sheet::dependents`), hands each its change,
///    a product and a sum of numbers of one word, and formats its `name=value` once
///    (`Sheet::spread`): O(1) instructions and bytes a cell besides its digits.
/// 3. Each line printed gathers its entries in name order from the ordered map of defined
///    cells, O(n), and joins them, O(the line's bytes).
/// So the instructions and the bytes are O(out(n)), but for the one output `String`: the meter
/// counts each regrowth as a new block of the full new size, so its bytes are about twice its
/// last capacity, `2^⌈log2 out(n)⌉`, a step function of the output. The cost is the sum of these
/// two nonnegative terms, so its ratio at 8n is at most the greater of their ratios: at 200 and
/// 1600, 76.2 for the output (441,185 and 33,597,785 bytes) and 128 for the capacity (2^19 and
/// 2^26; the output at 1600 lies just past 2^25), so the bench holds both measures to the
/// capacity's ratio, the step included. Before it the bench was held to power 2 (84): 65.3 times
/// the instructions, 84.9 times the bytes on cdf07ac4f, deferred by TESTS-scaling-limit-10_5 and
/// back with row M0-scaling-10_5. The output's count is checked against the program's output at
/// 200 here. Measured 65.3 times the instructions and 84.9 times the bytes (b24-scale1); with
/// the whole output copied at each line printed (negative control, not committed), 138.2 times
/// the instructions, which this test fails.
#[test]
fn spreadsheet_edits_of_a_cell_that_every_cell_depends_on() {
    let input = &SPREADSHEET_ALL_DEPEND;
    let n = input.n;
    let ratio = |f: fn(usize) -> f64| f(8 * n) / f(n);
    let out = |m: usize| spreadsheet_all_depend_output(m) as f64;
    assert!(ratio(spreadsheet_all_depend_buffer) >= ratio(out));
    let path = input_path(input.what, n);
    fs::write(&path, (input.input)(n)).expect("writing an input");
    let (printed, result) = zed_corpus_ref::run(input.number, &path);
    fs::remove_file(&path).expect("removing an input");
    assert_eq!(result, Ok(()));
    assert_eq!(printed.len(), spreadsheet_all_depend_output(n));
    scales_by(input, |run| {
        check_proved_cost(
            input.what,
            n,
            (
                "the output's buffer, 2^⌈log2 out(n)⌉",
                spreadsheet_all_depend_buffer,
            ),
            run,
        )
    });
}

/// Checks reference 14 at n and 8n, after its output at n, or at 1000 points where n is larger,
/// is checked to be that of the O(n²) form: at 4000 random points of 72 digits that form took
/// most of the 18.6 s the benchmark ran, the two timed runs 4.3 s.
fn clustering_scales(input: &Input) {
    let m = input.n.min(1000);
    let differs = crate::clustering_differs_from_oracle(&(input.input)(m));
    assert!(
        differs.is_none(),
        "{}: the O(n²) form differs at {m}",
        input.what,
    );
    scales(input);
}

macro_rules! benchmarks {
    ($check:ident; $($name:ident $input:ident;)*) => {
        $(
            #[test]
            fn $name() {
                $check(&$input);
            }
        )*
    };
}

benchmarks! {
    scales;
    word_count_over_many_words WORD_COUNT;
    histogram_with_one_long_word_among_short_ones HISTOGRAM;
    edit_distance_is_quadratic_in_the_word_length EDIT_DISTANCE;
    running_variance_of_a_long_series RUNNING_VARIANCE;
    max_prefix_sum_of_a_long_series MAX_PREFIX_SUM;
    matrix_multiply_is_cubic_in_the_side MATRIX_MULTIPLY;
    json_parser_on_deep_nesting JSON_DEPTH;
    json_parser_on_deep_objects JSON_OBJECT_DEPTH;
    json_parser_on_a_wide_list JSON_WIDTH;
    json_parser_on_a_failure_at_the_end_of_a_deep_list JSON_FAILURE;
    percent_decoding_of_a_long_line PERCENT_DECODING;
    canonical_equality_over_many_lines CANONICAL_EQUALITY;
    regex_matcher_over_many_lines REGEX_LINES;
    regex_matcher_on_a_long_line REGEX_LENGTH;
    csv_split_of_a_long_line CSV;
    balanced_brackets_of_a_long_line BALANCED_BRACKETS;
    balanced_brackets_of_a_deep_line DEEP_BRACKETS;
    union_find_over_a_long_chain UNION_FIND;
    union_find_over_few_edges_among_huge_node_numbers UNION_FIND_HUGE_NUMBERS;
    spreadsheet_prints_every_cell_after_every_edit SPREADSHEET;
    spreadsheet_edits_of_a_cell_beside_one_long_formula SPREADSHEET_LONG_FORMULA;
    spreadsheet_edits_of_the_cell_a_long_formula_repeats SPREADSHEET_REPEATED_TERM;
    game_tick_with_many_players GAME_PLAYERS;
    game_tick_over_many_ticks GAME_TICKS;
    sensor_pipeline_over_many_readings SENSOR_PIPELINE;
    windowed_word_frequency_over_many_lines WORD_FREQUENCY;
    bank_ledger_over_many_transactions BANK_LEDGER;
    taint_escaping_of_many_lines TAINT;
    stats_over_many_rows STATS;
    top_k_over_many_scores TOP_K;
    join_zoo_over_many_keys JOIN_ZOO;
    weighted_pick_over_many_queries WEIGHTED_PICK;
    autocorrelation_of_a_long_series AUTOCORRELATION;
    heat_stencil_over_a_long_row HEAT_STENCIL;
    parent_chain_of_one_long_chain PARENT_CHAIN;
    precedence_climbing_of_a_long_expression PRECEDENCE_CLIMBING;
    late_dedup_over_many_readings LATE_DEDUP;
    client_server_over_many_requests CLIENT_SERVER;
    typechecker_over_a_long_chain_of_declarations TYPECHECKER_CHAIN;
    typechecker_over_a_chain_declared_backward TYPECHECKER_BACKWARD;
    typechecker_on_one_long_expression TYPECHECKER_LENGTH;
    typechecker_on_a_long_cycle TYPECHECKER_CYCLE;
}

benchmarks! {
    clustering_scales;
    clustering_of_points_near_a_line CLUSTERING_NEAR_A_LINE;
    clustering_of_a_grid CLUSTERING_GRID;
    clustering_of_a_rotated_grid CLUSTERING_ROTATED_GRID;
    clustering_of_random_points CLUSTERING_RANDOM;
    clustering_of_many_equal_points CLUSTERING_EQUAL_POINTS;
    clustering_of_points_on_one_line CLUSTERING_ON_A_LINE;
    clustering_of_points_on_one_circle CLUSTERING_CIRCLE;
    clustering_of_two_parabolas_facing_apart CLUSTERING_TWO_PARABOLAS;
    clustering_of_random_points_with_wide_coordinates CLUSTERING_RANDOM_WIDE;
}

/// The same 1000 random points with coordinates of 36 and of 288 digits (120 and 957 bits, an
/// in-circle determinant of up to 488 and 3836 bits), held to the limit of power 1. At these
/// sizes the cost per number is mostly fixed, so this does not show the cost of num-bigint's
/// products, which larger coordinates reach (COMPLEXITY F39, item BIGINT-fast-mul).
#[test]
fn clustering_of_random_points_at_eight_times_the_coordinate_size() {
    let differs = crate::clustering_differs_from_oracle(&wide_random_points(1000, 4));
    assert!(differs.is_none(), "the O(n²) form differs at 36 digits");
    scales(&Input {
        what: "clustering coordinate blocks",
        number: "14",
        n: 4,
        power: 1,
        input: |chunks| wide_random_points(1000, chunks),
    });
}
