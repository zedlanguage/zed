# Completeness: compiler as queries (L1.30)

Row TEST-complete-diagnostics (author P189). The code under test is `crates/zedc/src/query.rs`
(`key`, `Db` and its queries: front end, parse, check, resolution, address, exports, row) and its
callers in `crates/zedc/src/testing.rs` and `crates/zedc/src/unit.rs`, with the work report
(`Counter`, `Report`) and `zedc --report`. Expected results are from DESIGN.md step L1.30 (queries
keyed by content hashes, syntactic hashes enough here) and L1.30a (the work report).

Coverage of `crates/zedc/src/query.rs` by this group (llvm-cov, benchmarks skipped): regions
88.64% before the pass, 100% after; lines 82.74% to 100%.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Equal parts give equal keys; one byte changes the key | `keys.rs` `equal_parts_give_equal_keys_and_one_byte_changes_the_key` | |
| The boundaries between parts are hashed; the name is kept apart from the parts | `keys.rs` `the_parts_boundaries_are_hashed`; `completeness.rs` `a_key_keeps_the_name_apart_from_the_parts` | |
| A new database has computed nothing | `a_new_database_has_computed_nothing` | |
| A row computed once per key; a failing row is kept too | `a_row_is_computed_once_per_key_and_a_failure_is_kept_too` | |
| A function row and a wave row under one key are kept apart | `a_function_row_and_a_wave_row_under_one_key_are_kept_apart` | |
| The front end kept by text; another build computes it again and keeps the first | `the_front_end_is_kept_by_text`, `another_build_computes_the_front_end_again_and_keeps_the_first` | |
| A check kept by text and build; a parse by text alone | `a_check_is_kept_by_text_and_build`, `a_parse_is_kept_by_text_alone` | |
| A resolution computed once per key | `a_resolution_is_computed_once_per_key` | |
| An address kept; the options of a build leave it | `an_address_is_kept_and_the_options_of_a_build_leave_it` | |
| Equal exports share a number; unequal ones do not | `equal_exports_share_a_number_and_unequal_ones_do_not` | |
| A copy of the database keeps what was computed and goes on apart | `a_copy_keeps_what_was_computed_and_goes_on_apart` | |
| Two databases give one answer; every answer equals a fresh database's | `two_databases_give_one_answer`; `reuse.rs` `every_answer_equals_a_fresh_databases` | |
| A unit with no table computes no row | `a_unit_with_no_table_computes_no_row` | |
| Asking again recomputes nothing | `reuse.rs` `asking_again_recomputes_nothing` | |
| A comment reruns the front end and no row | `reuse.rs` `a_comment_reruns_the_front_end_and_no_row` | |
| An edit reruns only the rows that reach the changed definition | `reuse.rs` `an_edit_reruns_the_rows_that_reach_the_changed_definition`; `scaling.rs` `asking_again_after_an_edit_to_one_of_a_few_definitions_checks_one_row` | |
| A new row is the only row computed | `reuse.rs` `a_new_row_is_the_only_row_computed` | |
| An edit made and then undone reuses the first results | `an_edit_back_reuses_the_first_results` | |
| A rejected unit kept with its diagnostics; a type error added then removed | `reuse.rs` `a_rejected_unit_is_kept_with_its_diagnostics`, `a_type_error_added_then_removed` | |
| A renamed definition; a changed import edge | `reuse.rs` `a_renamed_definition`, `a_changed_import_edge` | |
| A wave row reused until `main` or what it reads changes | `reuse.rs` `a_wave_row_is_reused_until_main_or_what_it_reads_changes` | |
| Whole definitions moved with their tables, no text changed: every row reused | none in the tree | Fails: row FAIL-queries-reorder (the row key holds the unit-wide temporary numbers, so moving a definition changes the keys of rows after it). Test kept at `/home/luke/Work/wt/failing-tests/FAIL-queries-reorder.rs`. |
| The edit-script reader: a replace of absent text, a replace without its `with` stop the script | `reuse.rs` `a_replace_of_text_the_file_lacks_stops_the_script`, `a_replace_without_its_with_stops_the_script`, `a_script_of_a_few_rate_changes_runs` | |
| The work report: rows sum to the total and name each stage and definition; a cached definition reports zero; a definition's work in its own row; a test row per definition | `report.rs` (four tests) | |
| `zedc --report` on a second copy of a unit, on a build, on a failing command | `binary.rs` (three tests) | |
| A few kept results each found again | `scaling.rs` `a_few_kept_results_are_each_found_again` | |
| Many definitions, many kept results | `bench/` | Sizes beyond the small cases are benchmarks (P178). |
| Semantic hashes (an edit that keeps the meaning reuses the row) | none | DESIGN L1.30: syntactic hashes suffice at this step. |
