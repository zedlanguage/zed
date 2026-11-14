# Completeness: s_01_port_catalog

Plan row PORT-catalog: the `catalog` tool scans the SCIP index of the Rust sources for the
routines they call, counts uses, files and the first site, and keeps a table of them with a
Zed column checked against Zed0's grammar. Plan row TEST-complete-ports (author P189).
Coverage before and after is in l01_19_whole_file_ports/COMPLETENESS.md.

| Case | Covering test | Or reason none is needed |
|---|---|---|
| Routine names of methods, trait impls, macros and functions | `mod.rs::routine_names_methods_trait_impls_macros_and_functions` | |
| The scan counts uses, files and the first site, and skips definitions and imports | `mod.rs::scan_counts_uses_files_and_the_first_site_and_skips_definitions_and_imports` | |
| A damaged index is refused with its own message | `mod.rs::scan_rejects_a_damaged_index_with_its_own_message` | |
| An empty index, and no index bytes at all, find no routine | `combinations.rs::an_empty_index_finds_no_routine` | |
| Each routine found once across many documents | `mod.rs::scan_finds_each_routine`, `mod.rs::the_scan_of_many_documents_finds_each_routine_once` | |
| The Zed check: missing plan rows and Zed texts in Zed0 only | `mod.rs::check_zed_takes_missing_plan_rows_and_zed_texts_in_zed0_only` | |
| The Zed check: a sort with no key taken, other wrong sorts refused | `mod.rs::check_zed_takes_a_sort_with_no_key_and_refuses_the_other_wrong_sorts` | |
| The Zed check: lambda parameters scoped to their lambda; nested lambdas and chains of calls | `mod.rs::check_zed_scopes_lambda_parameters_to_their_lambda`, `mod.rs::nested_lambdas_and_chains_of_calls_pass_the_zed_check` | |
| Writing keeps the Zed column; the check reports each difference | `mod.rs::write_keeps_the_zed_column_and_check_reports_each_difference` | |
| A bar in a routine name or a Zed text survives a write and a read | `combinations.rs::a_bar_in_a_routine_or_a_zed_text_survives_a_rewrite` | |
| A routine listed twice is a problem | `mod.rs::a_routine_listed_twice_is_a_problem` | |
| A file with no table, a row of fewer than five cells | `combinations.rs::a_catalog_with_no_table_or_a_short_row_is_refused` | |
| A table at the end of the file with no counts line; a table with no rows | `combinations.rs::the_table_reads_back_at_the_end_of_the_file_with_no_counts_and_with_no_rows` | |
| No arguments, one argument, `--index` with no path | `combinations.rs::every_wrong_command_line_is_refused_with_the_usage` | |
| The committed catalog is well formed | `mod.rs::the_committed_catalog_is_well_formed` | |
| The floor division and modulo texts hold for a negative divisor | `mod.rs::the_catalog_floor_texts_hold_for_a_negative_divisor` | |
| Large indexes, long texts, deep lambda nesting | `bench.rs` (all three tests) | Benchmarks (P178). |
