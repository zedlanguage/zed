# L1.14 name resolution: cases and the tests that cover them

Code under test: `crates/zedc-resolve/src/resolve.rs` (the resolver at layer L1), reached through
`zedc::resolve` and the `l01_14` helpers. Measured with `-C instrument-coverage` and `llvm-cov`
over this group alone: `resolve.rs` went from 70.68% of regions and 66.89% of lines to 74.64% and
71.27% with `complete.rs`. The lines still uncovered belong to forms resolved at later steps; each
is listed below with the group that covers it or the reason none is needed.

| Case | Test that covers it | Or reason none is needed |
|---|---|---|
| Innermost block binding wins | order.rs `the_innermost_block_that_binds_a_name_wins` | |
| Name found at the unit's top level | order.rs `a_name_not_in_a_block_is_found_in_the_units_top_level` | |
| Name found in the prelude | order.rs `a_name_the_unit_does_not_bind_is_found_in_the_prelude` | |
| Each L1 prelude word resolves; `count` waits for L3 | complete.rs `each_prelude_word_of_l1_resolves_to_the_prelude_and_count_waits_for_l3` | |
| A unit's name shadows a prelude word | order.rs `a_units_own_name_shadows_a_prelude_word` | |
| ... at each kind of binder (let, parameter, lambda parameter, `else` pattern field, block) | complete.rs `a_prelude_word_is_shadowed_at_each_kind_of_binder` | |
| A later layer's prelude word is an error naming the layer | order.rs `a_prelude_word_of_a_later_layer_is_an_error_naming_the_layer` | |
| Each form of a later step named as not compiled yet | complete.rs `each_form_of_a_later_step_is_named_as_not_yet_compiled` | |
| Statement order does not matter at the top level | order.rs `statement_order_does_not_matter`, above.rs `the_top_level_declares_in_any_order` | |
| Name bound nowhere | order.rs `a_name_bound_nowhere_is_an_error` | |
| Binder naming a type, at each kind of binder | complete.rs `a_binder_may_not_name_a_type_at_any_kind_of_binder` | |
| Rebinding in one scope, each scope with its repairs | scopes.rs `rebinding_in_one_scope_is_an_error_and_a_nested_scope_may_shadow`; complete.rs `rebinding_is_rejected_in_every_scope_with_the_repairs_that_scope_allows` | |
| Parameter and body block share a scope | scopes.rs `a_parameter_and_the_body_blocks_statements_share_one_scope` | |
| Inner scope not seen outside | complete.rs `a_name_bound_in_an_inner_scope_is_not_seen_outside_it` | |
| Inner scope sees every outer scope | complete.rs `an_inner_scope_sees_every_outer_scope_out_to_the_top_level` | |
| Names in every expression position (operands, call arguments, if, else, interpolation, tuple, index, member receiver, lambda body, test case) | complete.rs `names_resolve_in_every_expression_position` | |
| Block binding used above its definition, with the move repair | above.rs (12 tests) | |
| Overload sets: two parameter types; same types rejected; each use bound to every overload | scopes.rs `functions_of_one_name_with_different_parameter_types_form_an_overload_set`; scaling.rs `a_second_declaration_with_the_same_parameter_types_is_rejected`, `each_use_of_an_overloaded_name_is_bound_to_every_overload_in_order` | |
| Overloads in a block | complete.rs `functions_in_a_block_overload_resolve_and_are_checked_like_bindings` | |
| Two block functions naming each other: offered the top level only when they can move | complete.rs `two_block_definitions_that_name_each_other_are_offered_the_top_level_only_when_they_can_move` | |
| Lambda parameter shadows | scopes.rs `a_lambdas_parameter_shadows_an_outer_name` | |
| Parameter type and default see parameters, not the body | scopes.rs `a_parameters_type_and_default_see_the_parameters_but_not_the_body` | |
| A default naming its own parameter | complete.rs `a_parameter_default_naming_its_own_parameter_resolves_to_it` | |
| Default naming a later parameter or field | above.rs `a_parameter_default_naming_a_later_parameter_is_rejected`, `a_field_default_naming_a_later_field_is_rejected` | |
| Test cases see the scope around the function | scopes.rs `test_cases_are_read_in_the_scope_around_the_function`; complete.rs `test_cases_see_the_scope_around_the_function_and_not_inside_it` | |
| `else` pattern binds its fields in its default | scopes.rs `an_else_pattern_binds_its_fields_in_its_default` | |
| A push names an output port | scopes.rs `a_push_names_an_output_port_of_its_function` | |
| Member call: each form (`x.f`, `x.f()`, `x?.f`, chained) | scopes.rs `a_member_whose_name_is_in_scope_is_recorded_for_the_uniform_call`; complete.rs `a_member_is_a_candidate_uniform_call_in_each_form` | |
| A binding naming itself | scopes.rs `a_binding_that_names_itself_resolves_to_itself`; above.rs `a_binding_that_names_itself_is_not_this_row` | |
| Sort key names the step that compiles it | scopes.rs `a_sort_key_names_the_step_that_compiles_it` | |
| Types in each type form resolve to the prelude; a unit declares no type at L1 | complete.rs `a_type_in_each_type_form_resolves_to_the_prelude`; order.rs `a_type_name_resolves_to_the_prelude_and_a_unit_declares_none_at_l1` | |
| `main` in scope, neither a value nor called (A68) | complete.rs `main_is_in_scope_but_neither_a_value_nor_called` | |
| Corpus fences, one or several programs | fences.rs (6 tests) | |
| Depth and width at small sizes | scaling.rs `nested_blocks_and_overloads_resolve_at_small_sizes`, `each_deep_shape_resolves_at_small_depths` | |
| Imports, qualified names, aliases, ambiguity | l02_03_name_resolution imports.rs, complete.rs | Layer L2.3 |
| Ambiguous qualifier or alias: repair names a member the unit lacks | l02_03_name_resolution ambiguous_qualifier.rs | Row FAIL-ambiguous-qualifier-repair, fixed |
| Structs, methods, type parameters, match arms | l02_03_name_resolution binders.rs | Layer L2 |
| `main_fact`, `blocking_written`, annotations on `main` | none | Rows MAIN-files and BLOCKING-fact (A68) build them; no DESIGN output yet to test against |
| `type_var` (generic type variables) | none | Generics, a later layer |
| `test_ports` (ports in `with` clauses) | none | Ports, layer L5 onward |
