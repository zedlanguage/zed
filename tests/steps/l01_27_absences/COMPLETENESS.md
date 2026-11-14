# Completeness: absences and narrowing (L1.27)

Row TEST-complete-staging (author P189). The code under test is the checker's handling of
`else` and of loose atoms passing through operators and calls (`zedc::check`, with the merge
into `#errs` and `Ty::loose`, `Ty::without_loose` in `zedc::check::ty`), and its check of `_`
(`discard`, `entries`, `named_default`, `flows` in `crates/zedc-check/src/check/mod.rs`).
Expected results are from DESIGN.md sec:failure ("All or the failures", the merge rule),
rule 6 of sec:type_resolution, and sec:tour_methods (`_` drops a loose failure only where an
`else` default names it). llvm-cov as a floor, regions before and after: `flows` 76.92% to
98.08%, `named_default` 87.50% to 100%, `discard` 100% both, `entries` 98.20% both.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Plain `else` strips every loose atom | `loose.rs` `else_defaults_every_loose_atom` | |
| `else` as a call argument | `edges.rs` `else_strips_the_loose_atoms_in_each_place_an_expression_stands` | |
| `else` as an operand | same, case "operand" | |
| `else` as a tuple component | same, case "tuple component" | |
| `else` in an `if` branch | same, case "if branch"; `discard.rs` `an_else_default_inside_an_if_branch_or_a_block_names_what_is_dropped` | |
| `else` in an `if` condition | same, case "if condition" | |
| `else` in a block statement and a block export | same, case "block statement and export" | |
| `else` nested in its own default | same, case "nested in its own default" | |
| `else` in a lambda body | `edges.rs` `an_else_in_a_lambda_body_handles_what_the_lambda_is_passed` | |
| `else` in a match arm | | `match` is not compiled at L1 (`zed_tests::is_not_yet`) |
| `else` in a loop body or with `initial` | | zedc answers "a `loop` ... does not compile it yet" at L1 |
| A default that may itself fail keeps its own atoms | `edges.rs` `a_default_that_may_fail_or_is_an_atom_puts_its_own_atoms_in_the_type` | |
| An atom literal as the default | same | |
| The pattern form with an atom default | same | |
| The pattern form names one atom, keeps the rest | `loose.rs` `the_pattern_form_handles_the_atom_it_names_and_keeps_the_rest` | |
| Pattern with a payload keeps the atom | `loose.rs` `a_pattern_with_a_payload_keeps_the_atom_in_the_type`, `a_payload_pattern_that_binds_its_field_keeps_the_atom_for_underscore` | |
| `else` on a value with no loose atom: accepted, value unchanged | `edges.rs` `else_on_a_value_with_no_loose_atom_leaves_the_value` | the warning DESIGN gives there is step L2.12e |
| The three absences stay three facts | `loose.rs` `the_three_absences_stay_three_facts` | |
| `?.` carries the atom; `else` after it | `loose.rs` `a_loose_atom_flows_through_safe_navigation`; `edges.rs` `else_after_safe_navigation_strips_what_it_carried` | |
| Rule 6 through declared, generic and overloaded functions | `loose.rs` five `a_loose_atom_...` and `a_call_takes_...` tests | |
| The `is` repairs | `loose.rs` four `..._is_repair_...` tests | |
| Two operands, different failures merge into `#errs` | `merge.rs` `different_failures_on_two_operands_merge_into_errs` | |
| Same failure on both operands | `merge.rs` `the_same_failure_on_both_operands_is_that_failure` | |
| One operand, two ways; one failing operand | `merge.rs` `one_operand_that_can_fail_two_ways_meets_one_of_them`, `one_failing_operand_passes_its_failures_alone` | |
| Same name, different payloads | `merge.rs` `the_same_failure_name_with_a_payload_can_differ` | |
| Nested chain gives one flat set | `merge.rs` `a_nested_chain_merges_into_one_flat_set` | |
| Plain `else` on a merge | `merge.rs` `else_handles_a_merged_failure_as_it_handles_one` | |
| Pattern `else #errs -> d` handles the merge, keeps single failures | `edges.rs` `the_pattern_form_on_a_merged_failure` | |
| Pattern naming one member keeps the `#errs` that holds it | same | |
| Two arguments of a call merge | `edges.rs` `failures_of_two_arguments_of_a_call_merge_as_those_of_two_operands_do` | |
| Three arguments give a flat set of three | same | |
| Unary operator passes one operand's failures unmerged | `edges.rs` `a_unary_operator_passes_its_one_operands_failures_unmerged` | |
| Comparison merges its operands' failures | `edges.rs` `a_comparison_merges_the_failures_of_its_operands` | |
| `==` with an atom operand | | `==` takes atoms as values (`x == #gold` tests the atom), so it merges nothing; covered in `l01_26_type_resolution/handled.rs` |
| Loose atoms inside a tuple or struct argument | | step L2.6b (plan row, not yet built); rule 6 reads value positions from there |
| README examples | `merge.rs` `the_readme_examples_give_these_values` | |
| Family atoms: `else` keeps them, pattern strips, join, written type, narrowing, errors and repairs | `families.rs`, all ten tests | |
| `_` after a call that may fail: rejected with derivation and repairs | `discard.rs` `a_dropped_lookup_miss_is_rejected_with_its_derivation_and_repairs` | |
| `_` after an `else` whose default names the atom | `discard.rs` `an_else_default_names_what_is_dropped` | |
| `_` after safe navigation, unary, comparison, call argument, a default that may fail, a pattern default that may fail | `edges.rs` `underscore_drops_no_failure_passed_on_by_each_form` | each also accepted once `else #ok` names it |
| `_` after a lookup `m[k]` and a member read `.abs` | `edges.rs` `underscore_drops_no_failure_of_a_lookup_or_a_member_read` | |
| `_` in a local function body | `edges.rs` `underscore_in_a_local_function_is_checked_as_in_any_body` | |
| `_` on a value with no failure: literal, arithmetic, tuple, comparison | `edges.rs` `underscore_drops_a_value_with_no_failure` | |
| `_` with the pattern form | `discard.rs` `the_pattern_form_drops_only_the_atom_it_handles` | |
| `_` with every dropped atom named and where it enters | `discard.rs` `every_dropped_atom_is_named_with_where_it_enters` | |
| `_` on a family atom | `discard.rs` `a_family_atom_is_data_and_dropped_freely` | |
| `_` as a tuple component; failure of the whole tuple | `discard.rs` `a_discarded_component_is_checked_alone`, `a_failure_of_the_whole_tuple_reaches_each_named_component` | |
| `(a, _)` parenthesized target list | `discard.rs` `a_parenthesized_target_list_is_not_a_binding_at_layer_l1` | |
| `_` as a match arm pattern | `discard.rs` `a_match_arm_is_a_pattern_not_a_dropped_binding` | |
| Defaults per `if` branch, in each branch, on an inner `if` | `discard_paths.rs` first three tests | |
| Block export and a name | `discard_paths.rs` `a_block_export_and_a_name_keep_what_their_default_names` | |
| Argument with a default; generic calls | `discard_paths.rs` last three tests | |
| Checking units alone and together agree | `discard.rs` `checking_units_together_and_alone_agree` | |
| `flows` arm for an expression of no other kind | | reached only by a leaf, which passes no part on; the arm returns nothing |
| `entries` when a span is unnamed but not seen | | every span the checker records as unnamed is also recorded as seen; the `continue` is defensive |
