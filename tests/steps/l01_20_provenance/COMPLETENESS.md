# Completeness: provenance (L1.20)

Row TEST-complete-diagnostics (author P189). The code under test is
`crates/zed-kernel/src/provenance.rs` (`Position`, `NodeAddress`, `FactAddress`, `Fact`,
`Provenance` and its origin sets) and the recording in `crates/zed-kernel/src/eval.rs`. Expected
results are from DESIGN.md step L1.20 (facts, static node addresses, keypaths, inputs, origin
sets, a run that records only when asked).

Coverage of `crates/zed-kernel/src/provenance.rs` by this group (llvm-cov, benchmarks skipped):
regions 57.87% before the pass, 75.44% after; lines 58.55% to 76.67%. What stays uncovered: the
counted-set path for a set that is not the one counted whole (`enter` past its first branch,
`more`, `less`, `drop_if_uncounted`, `whole_holds`, `uncount`), which only a search holding two
counted sets at once reaches and no small program here produces; `child_mut`, read only by
`zedc --mutate` and covered by `l25_08_mutate`; `PartialOrd for Position`, a one-line forward to `Ord`, which
no code of this group calls.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| A position prints as its child indices; the root prints empty | `completeness.rs` `positions_print_as_their_child_indices` | |
| Two positions built apart are equal and hash alike when their paths are | `two_positions_built_apart_are_equal_when_their_paths_are` | |
| Positions are ordered as the preorder of the term | `positions_are_ordered_as_the_term_preorder` | |
| A fact address prints its call sites, then its keypath, the root as `.` | `a_fact_address_prints_its_call_sites_then_its_keypath` | |
| A variable is an edge, not a fact; a `let` reads the facts both its subterms produced | `a_variable_is_no_fact` | |
| An application reads the function, the arguments and the body's result | `an_application_reads_its_function_its_arguments_and_its_body` | |
| A lambda is a fact with no value and no failure | `a_function_fact_has_no_value_and_holds_no_failure` | |
| Every fact comes after the facts it read | `every_fact_comes_after_the_facts_it_read` | |
| The result fact is the last and holds the run's value | `the_result_fact_is_the_last_and_holds_the_value` | |
| Each fact's term is the term at its node | `each_fact_term_is_the_term_at_its_node`; `scaling.rs` `the_term_of_every_fact_of_a_sum_is_found` | |
| A fact holding no failure has no origins | `a_fact_holding_no_failure_has_no_origins` | |
| A failure held in a tuple, a family entry, a payload | `a_failure_taken_from_a_tuple_has_its_origin_where_it_was_made`, `a_failure_taken_from_a_family_has_its_origin_in_the_entry`, `a_failure_in_a_payload_has_its_origin_where_it_was_made` | |
| A failure read from a union of nested families: its origin is the operand that held it; a merge of two read through one union names each operand | `completeness.rs` `a_failure_read_from_a_union_of_nested_families_has_its_origin_in_its_operand`, `a_merge_of_failures_read_from_a_union_names_each_operand` | |
| One atom made at two facts: both are origins | `one_atom_made_at_two_facts_has_both_as_origins` | |
| A merged failure: each member's origin | `kernel.rs` `a_merged_failure_names_the_origin_of_each_member` | |
| A comparison of a failure gives a boolean, no origin; an `if` on a failure gives it | `a_failed_condition_is_the_origin_of_the_if` | |
| A failure through function calls, through a `match` arm | `kernel.rs` `an_atom_passed_through_functions_keeps_its_literal_as_origin`, `a_failure_bound_by_a_match_arm_keeps_its_origin` | |
| Two calls of one function; a call through another (call sites in the address) | `kernel.rs` `two_calls_of_one_function_are_two_facts`, `a_function_called_through_another_is_named_by_both_call_sites` | |
| A recursion: one call site per level | `scaling.rs` `the_facts_of_a_recursion_are_at_their_call_sites` | |
| A family body once per key; nested families, a key per level | `kernel.rs` `a_family_body_runs_once_per_key`; `nested_families_give_a_key_per_level` | |
| A fold: groups and the index of each combine; its primitive is no fact | `kernel.rs` `word_count_has_a_fact_per_word_and_per_group`, `a_combine_step_is_named_by_its_group_and_index`; `a_primitive_a_fold_calls_is_no_fact` | |
| A `discard` selector once per key at every level | `kernel.rs` `a_selector_runs_once_per_key_at_every_level` | |
| A lattice `fix`: each iterate | `kernel.rs` `a_lattice_fixpoint_names_each_iterate` | |
| A definedness entry: one fact however many attempts | `kernel.rs` `a_definedness_entry_is_one_fact_however_many_attempts_it_took` | |
| A `gen` step and its guard, by `t` | `kernel.rs` `a_generation_names_its_step_and_guard_by_t` | |
| Every keypath starts with the wave stamp, in the kernel and in a program's wave | `kernel.rs` `every_keypath_starts_with_the_wave_stamp`; `programs.rs` `every_keypath_of_a_wave_starts_with_its_stamp` | |
| No two facts share an address, for every region form | asserted in each `kernel.rs` test through its helper | |
| A run not asked to record keeps nothing and gives the same value | `kernel.rs` `without_the_request_nothing_is_recorded_and_the_value_is_the_same` | |
| A run that stops with an error records nothing | `a_run_that_stops_with_an_error_records_nothing` | |
| A second run records only its own facts | `a_second_run_records_only_its_own_facts` | |
| A keypath that is empty at the root | `an_empty_keypath_root_is_allowed` | |
| A whole program: the origin of a failed total in its input and its file | `programs.rs` `a_failed_total_names_the_bad_quantity_and_the_missing_price_file` | |
| A `reindex`: the leaf path it reads is the coordinate of its key map and value map | `kernel.rs` `word_count_has_a_fact_per_word_and_per_group` | |
| The `::origin` reads | none | They arrive with `::` at step L3.1 (DESIGN L1.20). |
| Deep recursion, large sums | `bench.rs` | Sizes beyond the small cases are benchmarks (P178). |
