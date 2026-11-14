# M0.4 completeness: the corpus and its reference programs

Code under test: the reference programs of the corpus, crate `zed-corpus-ref`
(zed/corpus/ref/src: `run`, the 31 programs `pNN.rs` and the shared helpers `zedrt.rs` and
`zedrt/product.rs`), each `.out` file against its reference, against DESIGN.md step M0.4 and the
rules the references cite (sec:reduction for the float sum and printing, step L1.18 for reading
and `lower`). Lines reached by this group's tests (llvm-cov, without the `bench` module): 97.5%
before (56 of 2,222 missed), 99.8% after (4 missed, listed at the end of the table with their
reasons).

| Case | Covering test, or the reason none is needed |
|---|---|
| Every `.out` is what its reference prints on the `.in`, all 31 | `every_output_is_what_its_reference_program_prints` |
| A program number with no program; a missing input; an input that is not UTF-8 | `a_number_with_no_program_is_an_error`, `a_missing_input_is_an_error`, `an_input_that_is_not_utf8_is_an_error_and_prints_nothing` |
| The references do not use the compiler | `the_references_do_not_depend_on_the_compiler` |
| Every program's enabled layer equals its `// layer` label (M0.4's own test) | None in this suite: the `layer` tool reads the word table of DESIGN.md, which lives in the spec repository, not here, so it is run by hand, `zcargo run -p zed-tools --bin layer -- <spec dir> zed/corpus/*.zed`; on 2026-11-14 all 31 agreed. The tool itself is tested in m0_03 (`layer_agrees_with_a_right_label_and_rejects_a_label_below_a_word_of_the_program` and the tests after it) |
| Float printing: fixed and exponent forms at their bounds, `-0.0`, `inf`, `nan`, ties to the larger magnitude | `floats_print_as_the_compiler_prints_them` |
| Float sum (`fsum`): no value, an exact zero, rounding once, no intermediate overflow, subnormal terms and results, a tie carried into the next binade and a tie kept, NaN, each infinity, both infinities, overflow at each sign | `cases::a_float_sum_is_the_exact_sum_rounded_once_at_every_kind_of_value`; the overflow and both-infinities errors inside a program in `mod.rs` |
| Float text read as DESIGN L1.18 says: digits, fraction, exponent (`e` and a sign only as `-`; `1E3`, `1e+3` refused), `-0`, a value below half the least subnormal at each sign, `inf`, `nan`; texts that are no numeral, marks `_` misplaced | `cases::a_float_text_reads_as_design_says_where_the_reference_agrees` |
| Integer text of any length, zeros, nines, powers of ten, a long text that is not an integer; at each length the texts L1.18 makes `#invalid` (a `+`, white space, `_`, Arabic-Indic digits alone and mixed with ASCII) | `int_reading::*` |
| Int and float text that DESIGN L1.18 calls `#invalid` (`+5`, `.5`, `infinity`, digits of other scripts, fullwidth digits, white space, `_` marks), and its neighbors: a lone or doubled sign, a sign after the digits, a point at either end, a capital or signed exponent, `Inf` and `NaN`, `-infinity`; a finite text past the largest `f64` (`#overflow`) | `fail_reading::*` (row FAIL-ref-text-reading, fixed): the references read all of them as numbers before. No corpus input uses these forms, so no `.out` changed |
| `lower`: U+0130, capital sigma final and not, case-ignorable characters skipped on both sides | `cases::lower_takes_the_full_mapping_with_the_final_sigma` |
| A line with the wrong number of fields: 06 header, 16, 23, 27, 29 | `cases::a_line_with_the_wrong_number_of_fields_is_an_error` |
| 06 a row range before the first row; a header of huge sizes | `cases::a_matrix_row_range_before_the_first_row_is_empty`, `a_matrix_header_of_huge_sizes_reserves_nothing` |
| 07 JSON failures report the farthest position | `a_json_failure_deep_in_a_list_reports_the_farthest_position` |
| 08 a surrogate or a value past U+10FFFF fails its line, output before it kept | `cases::percent_decoding_of_a_surrogate_or_a_value_past_u10ffff_fails_the_line` |
| 09 balanced brackets | `balanced_brackets_agree_with_the_definition_on_every_short_line`, `balanced_brackets_of_a_line_with_other_characters` |
| 13 union-find: huge and negative node numbers, nodes on no edge, no edges, against a table of labels | the `a_two_node_edge…` to `union_find_agrees_with_a_table_of_labels_on_small_graphs` tests in `mod.rs` |
| 14 clustering: ties, start order, errors by count, as many clusters as points, a hugely negative count, against its quadratic form, lattice circles | the `clustering_*` tests in `mod.rs`, `lattice_circles::*`, `scaling::reference_14_agrees_with_its_quadratic_form_on_each_clustering_input_at_small_sizes` |
| 15 spreadsheet: a cycle, a repeated term, an edit dropping old dependencies, a diamond, a late cycle; the cycle walk past closed cells, integer terms and a cell visited before its turn | the `a_spreadsheet_*` tests in `mod.rs`, `cases::a_spreadsheet_cycle_is_named_after_a_walk_past_closed_and_shared_cells` |
| 18 a line whose first piece is not an int, and an empty line, are skipped | `cases::a_word_frequency_line_whose_first_piece_is_not_an_int_is_skipped` |
| 19 a failed balance stays failed, an unknown kind ignored, a transaction on an account never opened | `cases::a_failed_balance_stays_failed_and_an_unknown_kind_is_ignored`, `cases::a_missing_account_operand_or_heat_step_is_an_error` |
| 21 no line | `cases::stats_of_no_line_divide_by_zero` |
| 26 the first three rows and the last; one step only | `a_heat_stencil_prints_the_first_three_rows_and_the_last`, `cases::a_missing_account_operand_or_heat_step_is_an_error` |
| 27 parent chains: a returning chain, a parent outside the children, short chains | `a_parent_chain_stops_at_the_first_node_it_has_seen`, `a_parent_outside_the_children_is_a_root`, `a_short_nest_and_short_chains_are_followed` |
| 28 too few operands | `cases::a_missing_account_operand_or_heat_step_is_an_error` |
| 30 a buy request with no quantity, or a non-digit one | `cases::a_buy_request_with_no_quantity_fails_at_the_farthest_position` |
| 31 a type error through a cycle | `a_type_error_spreads_through_a_cycle_and_past_it` |
| Exact running sum; histogram lengths | `a_running_sum_stays_exact_where_doubles_alone_would_lose_it`, `a_histogram_counts_each_length_up_to_the_longest` |
| Each reference on its benchmark inputs at small sizes | `scaling::each_reference_runs_on_its_benchmark_inputs_at_small_sizes`; large sizes in the `bench` module |
| p10.rs line 77: the direct test and the derivatives disagree | None: a check of the reference against itself, reached only if the two transcriptions of the matcher differ; every corpus and test line reaches both and they agree |
| p15.rs line 150: the cycle walk finds no cycle | None: the walk runs only after an edit found a cycle (`expect` at its call), so it always returns one |
