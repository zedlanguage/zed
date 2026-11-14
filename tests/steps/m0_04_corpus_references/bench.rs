//! How the reference programs scale with their input, run by `tools/run_tests.sh --bench` and
//! left out of its default run (TEST-bench-move-rest). Each input is built before timing, at n
//! and 8n. Most are linear up to a sort or a tree lookup; the ones that are not name why at their
//! input in `scaling.rs`: the power is what the problem forces, such as a full table in the
//! output, not the algorithm of the corpus program. `scaling.rs` runs each input at small sizes.

use std::fs;

use zed_tests::scaling::check_order;

use crate::scaling::*;

/// Checks reference `input.number` at n and 8n on the input it builds for each size.
fn scales(input: &Input) {
    let Input {
        what,
        number,
        n,
        power,
        input,
    } = *input;
    for m in [n, 8 * n] {
        fs::write(input_path(what, m), input(m)).expect("writing an input");
    }
    check_order(what, n, power, |m| {
        let (_, result) = zed_corpus_ref::run(number, &input_path(what, m));
        assert_eq!(result, Ok(()), "{what}");
    });
    for m in [n, 8 * n] {
        fs::remove_file(input_path(what, m)).expect("removing an input");
    }
}

/// Checks reference 14 at n and 8n, after its output at n is checked to be that of the O(n²)
/// form.
fn clustering_scales(input: &Input) {
    let differs = crate::clustering_differs_from_oracle(&(input.input)(input.n));
    assert!(
        differs.is_none(),
        "{}: the O(n²) form differs at {}",
        input.what,
        input.n
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
