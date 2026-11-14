# Completeness: the test runner (L1.21)

Row TEST-complete-diagnostics (author P189). The code under test is `crates/zedc/src/testing.rs`
(`test`, `command`, the outcomes of a unit's rows and ✗ marks, the counts and the exit status of
`zedc test`) and the row names of `crates/zedc-base/src/rejection.rs` (`Row::named_by`). Expected
results are from DESIGN.md step L1.21, sec:diagnostics (the ✗ mark names a row by its first
column "up to any parenthesis") and "The document is the first test suite" (sec:roadmap).

Coverage by this group (llvm-cov, benchmarks skipped): `crates/zedc/src/testing.rs` regions 82.95%
before the pass, 84.49% after (lines 82.11% to 83.20%);
`crates/zedc-base/src/rejection.rs` 69.70% in this group (its `bug` message is tested by
`l01_29_diagnostics/bug.rs`, where the file is covered in full). What stays uncovered in
`testing.rs` is listed in the last rows of the table: the staged runner `test_through` and its
rows not run, `--mutate`, a refused staging, and a `--suppress` address left unmatched.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| A row that gives its result passes; a wrong row reports the result at its place | `tables.rs` `a_wrong_row_reports_the_result`; `command.rs` `a_failing_check_is_printed_at_its_file_and_line` | |
| A row of several arguments; a failure value as the expected result | `tables.rs` `a_row_of_several_arguments_and_a_failure_value` | |
| A row that stops the evaluator; a wave that aborts | `tables.rs` `a_row_that_stops_the_evaluator_fails`, `a_wave_that_aborts_fails_its_row` | |
| A row is a call: atoms pass by as in a call, tuple keys, merged atoms, inferred parameters | `rows_are_calls.rs` (seven tests) | |
| `main` rows: port writes, an unpushed port, a files port, the exit status, a wrong shape, a key of more than four items, a wrong header reported once | `tables.rs` (seven tests) | |
| Port clauses: files, arguments and environment, per row, a name that is no port, a port given twice, ports zedc has not | `ports.rs` (thirteen tests) | |
| A ✗ mark on the line of its diagnostic passes; off the line fails, and so does the mark | `marks.rs` `a_diagnostic_on_a_marked_line_passes`, `a_diagnostic_off_the_marked_line_fails_and_so_does_the_mark` | |
| A mark in an accepted unit fails, and the unit's rows still run | `marks.rs` `a_mark_in_an_accepted_unit_fails`; `completeness.rs` `a_mark_in_an_accepted_unit_fails_and_its_rows_still_run` | |
| A commented variant is no mark | `marks.rs` `a_commented_variant_is_no_mark_and_a_rejected_unit_fails_each_row_it_cannot_run`; `completeness.rs` `a_file_of_comments_alone_has_no_test_and_fails` | |
| A marked line placed at its first diagnostic; two marked lines each pass on their own diagnostic | `marks.rs` `a_marked_line_is_placed_at_its_first_diagnostic_and_others_stay_failures`; `completeness.rs` `two_marked_lines_each_pass_on_their_own_diagnostic` | |
| A rejected unit with no mark fails on its diagnostic and on each row it cannot run | `completeness.rs` `a_rejected_unit_with_no_mark_fails_on_its_diagnostic_and_each_row`; through `zedc test`, the lines and the counts: `a_rejected_file_fails_its_rows_and_prints_its_diagnostic` | |
| A unit the parser rejects fails on its syntax error alone | `completeness.rs` `a_unit_the_parser_rejects_fails_on_its_syntax_error_alone` | |
| A mark names a row by its name and a colon; another row, no row, a diagnostic in no row | `rows.rs` (five tests); `completeness.rs` `a_mark_naming_no_row_fails_even_on_a_line_with_its_diagnostic` | |
| A row name holding a parenthesis inside its code is named whole; cut at it, it names none | `completeness.rs` `a_row_named_with_a_parenthesis_in_its_code_is_named_whole` | |
| No space after the mark, a tab, an empty comment, a lone colon | `completeness.rs` `a_comment_with_no_space_after_the_mark_names_its_row` | |
| Every row is named by its own name and a colon | `completeness.rs` `every_row_is_named_by_its_own_name_and_a_colon`; `rows.rs` `the_rows_are_those_of_the_spec_table`, `every_live_mark_of_the_spec_names_a_row` | |
| `zedc test`: passing units exit 0 with the counts; a passing and a failing file add their counts and exit 1 | `command.rs` `passing_units_exit_zero_with_the_counts`; `completeness.rs` `a_passing_and_a_failing_file_add_their_counts_and_fail_the_run` | |
| A unit with no test fails: an empty file, a file of comments alone | `command.rs` `a_unit_with_no_tests_fails_so_a_run_that_finds_none_fails`; `completeness.rs` `an_empty_file_has_no_test_and_fails`, `a_file_of_comments_alone_has_no_test_and_fails` | |
| Rejection units are counted, once however many lines they mark; one that compiles fails | `command.rs` `the_rejection_units_run_are_counted`, `a_rejection_unit_that_compiles_fails`; `completeness.rs` `a_rejection_unit_counts_once_however_many_lines_it_marks` | |
| Usage errors exit 2: a file not UTF-8 or missing, one after a file that passes, a flag with no value, an unknown target, no file | `command.rs` `a_file_that_is_not_utf8_fails_and_a_missing_file_is_a_usage_error`; `completeness.rs` `a_file_that_cannot_be_read_after_one_that_passes_is_a_usage_error`, `a_flag_with_no_value_is_a_usage_error_and_runs_nothing`, `an_unknown_target_is_a_usage_error`, `no_file_is_a_usage_error` | |
| A known target runs the rows for it | `completeness.rs` `a_known_target_runs_the_rows_for_it` | |
| The cone of a row: the definitions it reaches, closed in the unit's order | `cones.rs` (two tests) | |
| Each row the implementation raises has a near miss with its place and first repair | `near_miss.rs` (two tests) | |
| The L1 fences, the predictions suite and every step's Zed tests pass | `fences.rs`, `predictions.rs`, `zed.rs` | |
| A row not run because staging dropped its branch | none in this group | Covered by `l02_08d_build_constant/test_staged.rs` (step L2.8d). |
| `zedc test --mutate` | none in this group | Covered by `l25_08_mutate/command.rs` (step L25.8). |
| A run of a unit whose `main` staging is refused (`Accepted::Refused` in `command`) | none | Uncovered: no small program that reaches it was found; the staging refusals are tested in their own steps through `test`, not the command. |
| `zedc test --suppress` with an address that names nothing | none in this group | Covered by `l01_29_diagnostics/suppress.rs` `an_address_that_names_nothing_is_reported`. |
| An outside test tool | none | DESIGN names none: the tests of a Zed program are its tables and marks. |
| Many rows, many units | `scaling.rs`, `bench/` | Sizes beyond the small cases are benchmarks (P178). |
