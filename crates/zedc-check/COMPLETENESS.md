# Completeness: zedc-check unit tests

Row TEST-complete-crates (author P189). The checker as a whole (`check/walk.rs`, `arms.rs`,
`blocking.rs`, `ports.rs`, `read.rs`, `widen.rs` and most of `mod.rs`) is tested through whole
programs by the step groups, each with its own cases: `tests/steps/l01_22_type_representation`
through `l01_30_queries` (types, subtyping, refinements, resolution, absences, staging,
diagnostics, queries), `l02_*`, `l07_03_unit_log_off`, `l22_08_vacuity`, `m0_05_widening_and_iteration`,
`m0_11_prelude_axioms_and_limits` and `m0_12_refusal_census`. This file covers the pieces that
the crate's own unit tests call directly. Expected results come from DESIGN.md (sec:diagnostics,
sec:ffi on `@limits`, sec:type_language) and from arithmetic. New tests are in
`src/check/completeness.rs`; `tests::` names the older tests in `src/check/mod.rs`,
`limits::tests::` those in `src/check/limits.rs`, `walk::tests::` those in `src/check/walk.rs`.

llvm-cov lines (unit tests of the crate, benchmarks none):

| File | Before | After |
|---|---|---|
| `check/limits.rs` | 34/88 (38.64%) | 78/88 (88.64%) |
| `check/mod.rs` | 1125/6851 (16.42%) | 1163/6851 (16.98%) |
| `check/walk.rs` | 251/12549 (2.00%) | 251/12549 (2.00%) |
| `arms.rs`, `blocking.rs`, `ports.rs`, `read.rs`, `widen.rs` | 21/2441 | 21/2441 (step groups above) |

Within the pieces below, the lines left unreached and why:

- `mod.rs`, the `TypeKind::For` arm of `explain_empty`'s `Find`: unreachable, since `Find` first
  strips every `for` clause with `bare`. The arm exists only so that the `match` is exhaustive.
  The case is still tested: a part under a `for` clause is found and named at the type it bounds.
- `limits.rs`, `through_names` (a limit read through a chain of names, `d = 1r/2r;
  @limits(cpu: d)`): it needs a whole program, and is tested by
  `tests/steps/l01_29_diagnostics/main_limits.rs`.

| Case | Test, or reason none is needed |
|---|---|
| `memory:` limit: a positive `int` of bytes; 0, negative, a `rat`, a string refused; above the target's address space refused; at its top accepted; no fixed value refused | `a_memory_limit_is_a_positive_int_of_bytes_within_the_address_space` |
| `memory: 2^63`, the largest limit the rejection above names | Fails: `2^63` is refused with the same message. Row FAIL-check-memory-limit-2-63, test in `wt/failing-tests/FAIL-check-memory-limit-2-63.rs` (not merged) |
| `cpu:` duration: positive `int` or `rat` of seconds; 0, negative and non-numbers refused; exactly 2^64 - 1 ns accepted, one nanosecond more too long | `a_duration_is_a_positive_int_or_rat_of_seconds_below_2_to_the_64_nanoseconds` |
| Seconds rounded up to a whole nanosecond | `limits::tests::a_number_of_seconds_is_rounded_up_to_a_nanosecond` |
| Target named system first (`x86_64-unknown-linux-gnu`) | `limits::tests::a_target_is_named_system_first` |
| Target of another form: trailing dash, two-part, empty | `a_target_of_another_form_is_kept_or_split_at_its_first_dash` |
| Empty-type explanation: cause named by kind (name, tuple, atom, union, intersection, difference, other) | `each_kind_of_cause_is_named_by_its_kind_in_the_step_after_it` |
| Intersection and difference found empty | `an_intersection_or_a_difference_with_an_empty_operand_names_it` |
| Parts found inside every kind of type: arrow parameters (positional, named, later), arrow result, bounded arrow, applied type, record, array, atom payload, union, intersection, difference (both sides), `for` clause; types with no parts | `parts_with_no_value_are_found_inside_every_kind_of_type` |
| Tuple or atom found empty with no empty part; union members; a part of a kind with values; atom with an empty payload; `for` clause | `tests::a_tuple_found_empty_with_no_empty_component_gets_a_step` and the five tests after it |
| Atom with a positional payload part found empty: named by position | `an_atom_found_empty_names_a_positional_part_by_its_position` |
| Family atoms passed on: one atom and nothing else (one repair, no rest arm) | `a_family_of_one_atom_and_nothing_else_gets_one_d_and_no_rest_arm` |
| Family of every atom but some: the match written in words | `a_family_of_every_atom_but_some_gets_a_match_in_words` |
| Family atom reaching a call: repairs | `tests::a_family_atom_reaching_a_call_is_rejected_with_its_repairs` |
| Repair code on several lines or blank is not quoted | `code_on_more_than_one_line_or_blank_is_not_quoted_in_the_repair` |
| A type with no family: loose atoms passed on, nothing rejected | `a_type_with_no_family_passes_on_its_loose_atoms_and_rejects_nothing` |
| `ungrouped`: parentheses around the whole code only | `tests::ungrouped_takes_off_only_the_parentheses_around_the_whole_code` |
| `ungrouped` of code that does not lex, unbalanced, empty | `code_that_does_not_lex_keeps_its_parentheses` |
| `Label`: operator printed quoted; only an operator label is an operator | `tests::an_operator_label_prints_as_the_quoted_operator`, `only_an_operator_label_is_an_operator` |
| `or_list`, `and_list`: none, one, two, three items | `a_list_in_a_sentence_joins_its_last_item_with_or_or_and` |
| Trial state: `mark`, `undo`, passed atoms rolled back, memo rows | `tests::a_rolled_back_branch_restores_the_passed_atoms`, `walk::tests::a_trial_undone_after_the_memo_entered_a_row_leaves_no_memo`, `walk::tests::a_row_found_clean_is_walked_again_after_its_level_ends` |
| `one_shape_per_length`: each length once through shared parts; deep nesting | `tests::one_shape_per_length_joins_each_length_once_through_shared_parts`; the deep case is a benchmark (`tests::bench`) |
| `plain_rat`: a `rat` literal written with its point where that is shorter | `walk::tests::a_rat_literal_is_written_with_its_point_where_that_is_no_longer` |
| A parenthesized part, `((int, Never))`: its span holds its parentheses | None needed: the checker matches found parts by the denotation, not by their text; only the test helper matches by text |
| Everything else in the checker | The step groups named at the top |
