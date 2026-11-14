# L1.16 elaboration: cases and the tests that cover them

Code under test: `crates/zedc-elab/src/elab/walk.rs`, `elab/state.rs` and `elab.rs` (the
elaborator), with `crates/zedc-resolve/src/tables.rs` and `topo.rs` (dependency order and cycles).
Measured with `-C instrument-coverage` and `llvm-cov` over this group alone, regions% / lines%,
before the last three tests of `complete.rs` were added:

| File | Before | After |
|---|---|---|
| elab/walk.rs | 72.71 / 73.34 | 76.21 / 76.69 |
| elab/state.rs | 80.99 / 80.74 | 83.57 / 82.09 |
| elab.rs | 89.36 / 92.23 | unchanged |
| tables.rs | | 91.26 / 90.28 |
| topo.rs | | 100 / 100 |

| Case | Test that covers it | Or reason none is needed |
|---|---|---|
| Each binary operator, its primitive and its value | complete.rs `each_binary_operator_elaborates_to_its_primitive_and_computes`; programs.rs `arithmetic_comparison_and_power` | |
| Precedence and associativity | complete.rs `precedence_and_associativity_shape_the_term` | |
| Integers past a machine word in each operation | complete.rs `integers_widen_past_a_machine_word_in_every_operation` | |
| `int ^` a negative exponent, division by the literal zero | complete.rs `an_int_power_with_a_negative_exponent_and_a_division_by_the_literal_zero_are_rejected` | |
| Comparisons take one kind on both sides | complete.rs `comparisons_take_one_kind_on_both_sides` | |
| `++` and `+` operand types | complete.rs `concatenation_and_addition_take_their_own_operand_types`; programs.rs `concatenation_and_interpolation`, `string_concatenation_is_the_offset_concatenation` | |
| Interpolation, each hole, an atom passing through | complete.rs `interpolation_shows_each_hole_and_passes_an_atom_through` | |
| Blocks nest; one kernel name per binder | complete.rs `blocks_nest_and_each_binder_gets_its_own_kernel_name`; programs.rs `a_name_bound_twice_gets_one_kernel_name_per_binder` | |
| Block without export is `()`; destructuring | programs.rs `a_block_without_an_export_is_the_empty_tuple`, `return_of_several_values_is_a_tuple_and_destructuring_reads_it` | |
| `if` branches; an atom condition passes through; `and`/`or` short-circuit | complete.rs `if_elaborates_each_branch_and_an_atom_condition_passes_through`; programs.rs `if_chains`, `and_or_are_if_forms_so_they_short_circuit` | |
| `else`: any atom or the one its pattern names | complete.rs `else_matches_any_atom_or_the_atom_its_pattern_names`; programs.rs `else_replaces_an_atom_and_passes_any_other_value` | |
| Atom handling through `is`, `else`, function arrows | handled.rs (17 tests) | |
| `?.` passes an atom | complete.rs `a_safe_member_passes_an_atom_and_calls_on_anything_else`; programs.rs `safe_member_passes_an_atom_through` | |
| Member call with or without parentheses, chained | complete.rs `a_member_is_a_call_with_or_without_parentheses_and_chains`; calls.rs `a_receiver_fills_the_first_parameter_of_either_kind`, `a_member_naming_a_prelude_word_is_its_call` | |
| Named arguments, order, missing one | complete.rs `named_arguments_reach_their_parameters_and_a_missing_one_is_reported`; calls.rs `named_arguments_go_in_parameter_order_whatever_the_written_order` | |
| Defaults: filled, reading earlier parameters, chains | calls.rs `a_default_is_filled_where_the_call_omits_it`, `defaults_read_earlier_parameters_in_dependency_order`; scaling.rs `a_chain_of_defaults_calls_each_default_once`, `a_compound_default_reads_the_parameters_it_names` | |
| Curry `...` | calls.rs `curry_is_a_lambda_over_the_named_parameters_left_out` | |
| Brackets index one level | calls.rs `brackets_index_one_level_and_fill_no_default`; errors.rs `an_index_of_a_function_with_no_parameters_is_rejected` | |
| Lambdas by position, exact arity, capture | complete.rs `a_lambda_is_called_by_position_with_exactly_its_arguments`; programs.rs `lambdas_are_called_by_position_and_capture_their_scope` | |
| Call errors: rules, too many, defaults reading each other, names through a value | errors.rs `call_rules`, `too_many_arguments`, `defaults_that_read_each_other`, `named_arguments_through_a_value_need_its_parameter_names`; scaling.rs `an_argument_named_for_no_parameter_of_the_value_called_is_rejected` | |
| Atoms with and without payloads | complete.rs `atoms_with_and_without_payloads_are_values` | |
| Atom payload by position and name at once, or with `...` | complete.rs `an_atom_payload_mixing_position_and_name_or_left_open_is_rejected` | |
| Float literal rounding to infinity or to zero at its suffix's format | complete.rs `a_float_literal_that_rounds_to_infinity_or_to_zero_is_rejected` | |
| Prelude words of L1 on corner cases | complete.rs `each_prelude_word_of_l1_computes_on_its_corner_cases` | |
| Casts from a string | complete.rs `a_cast_from_a_string_reads_what_the_design_lists` | |
| Dependency order, not written order | programs.rs `statements_run_in_dependency_order_not_written_order`; order.rs (8 tests) | |
| Cycles: value, function, overload set, destructuring, member calls, several cycles, repairs | complete.rs `a_cycle_among_statements_is_an_error_whether_a_value_or_a_function`, `a_cycle_is_reported_for_each_form_its_statements_and_uses_take`; order.rs `a_cycle_through_an_overload_set`, `every_cycle_is_reported_each_by_name`; errors.rs `recursion_is_layer_l6` | |
| Cycle notes and the rename repair | l01_29_diagnostics recursion.rs | |
| Test tables | programs.rs `test_tables_check_each_case`; errors.rs `test_tables` | |
| Forms of later steps | errors.rs `forms_of_later_steps_and_layers` | |
| Deep and wide programs at small sizes | scaling.rs `each_benchmark_input_elaborates_at_small_sizes`, `each_deep_benchmark_program_is_ordered_and_elaborated_at_small_depths`; benchmarks in bench.rs | |
| Elaboration from the checker's findings | scaling.rs `elaborating_from_the_checkers_findings_gives_what_elaborate_gives` | |
| Decimal literals with no suffix, generic literals taking a carrier (`witnessed`, `Fit::Read`) | none | Pending POW-domains: the carriers of decimal literals and powers change with that row |
| Test cases of `main` keyed by `main::files` and the other ports (`main_field`, keyed `test_case`) | none | Rows MAIN-files (A68); not yet in the surface the checker accepts |
| `UnitAnnot` statement | l07_03_unit_log_off | Read at step L7.3 to drop log lines |
| Fitting a function argument to a slot (`fit`, `FitBody`), value defaults through a function value | none in this group | The checker records a `Fit` (zedc-check walk.rs) for a lambda or function passed where a function type with another parameter order or with defaults is expected; that is type resolution, step L1.26 |
| `marks` on primitives that can fail at run time | none in this group | Set only when the elaborator is asked for marks by a later step |
| `is` against a function type | none | A function type in `is` is resolved at a later layer |
| `unreachable!` arms ("resolve rejects the forms of layer L2/L6", "a term", "a binding", ...) | none | Unreachable by construction: resolve rejects those forms before elaboration |

DESIGN note: L1.16's "a cycle is an error naming layer L6" is worded for function recursion; a
cycle among values is an error with its own report (see `a_cycle_is_reported_for_each_form...`).
