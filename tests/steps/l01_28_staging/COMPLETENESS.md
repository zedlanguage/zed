# Completeness: staging (L1.28)

Row TEST-complete-staging (author P189). The code under test is `zedc::stage`: `color`,
`mix` and `mix_keeping`, the form rule `ends`, `Remix`, and the Trick (`trick`, `passed`,
`split`, `Specializer`). Expected results are from DESIGN.md sec:staging and the steps L1.28
and L1.40c. llvm-cov over `crates/zedc-stage/src/stage.rs`, as a floor: 92.75% of regions
(92.55% of lines) before, 93.20% (92.86%) after.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Constants computed at build | `mix.rs` `constants_are_computed_at_build` | |
| A definition computed from build-stage names (L1.40c `debug`/`mode`) is build-stage and built | `edges.rs` `a_definition_computed_from_build_stage_names_is_build_stage_and_built` | |
| A port read is run-stage; `main` is a function, known at build | `mix.rs` `a_port_dependent_definition_is_run_stage` | |
| `2 ^ 64`, `f64(#NaN)`, `-f64(#inf)` are built | `edges.rs` `the_constants_partial_evaluation_computes_are_built_and_write_as_the_program_does` | |
| A failure atom is a built value | `mix.rs` `a_failure_atom_is_a_value_the_build_computes` | |
| `else` built to its default, and to its value | `edges.rs` `an_else_whose_value_fails_at_build_is_built_to_its_default` | |
| A tuple, a lambda, a cast are built | `edges.rs` `a_tuple_a_lambda_and_a_cast_are_built` | |
| An unread definition is never evaluated | `mix.rs` `a_definition_nothing_reads_is_never_evaluated` | |
| A definition only a test reads is demanded | `edges.rs` `a_definition_a_test_reads_is_demanded` | |
| An unread local definition, by its written name | `mix.rs` `an_unread_local_definition_is_reported_by_its_written_name` | |
| An evaluation error is left to run | `mix.rs` `an_evaluation_error_is_left_to_run` | |
| A form shown to end is built; one not shown is left | `mix.rs` `a_term_whose_form_shows_it_ends_is_built_with_no_fuel`, `a_term_whose_form_does_not_show_it_ends_is_left_to_run` | |
| The form rule on calls and family operators | `mix.rs` `the_form_rule_reads_calls_and_family_operators`; `ends.rs` all | |
| A dead branch is cut; reads in a cut branch still evaluated | `mix.rs` `a_dead_branch_is_cut_at_build`; `arms.rs` cut-read tests | |
| A local definition computed where read | `mix.rs` `a_local_definition_is_computed_where_it_is_read` | |
| A write is left to run | `mix.rs` `a_write_of_a_constant_is_left_to_run` | |
| Warnings kept | `mix.rs` `a_staged_program_keeps_the_warnings_of_its_source` | |
| Sharing: one part under several bindings, arms or places | `dag.rs`, `differential.rs`, `store.rs`, `ids.rs`, `print.rs` | |
| Chains of calls left, failing, answered, at float zeros, at functions | `cone.rs` all | |
| Integer domain: no lower bound, no bound | `edges.rs` `an_integer_domain_at_its_bounds`; `trick.rs` first test | |
| Integer domain of one value; bounds included; negative bounds | `edges.rs` `an_integer_domain_at_its_bounds` | |
| Integer domain whose lower bound is above its upper | same | Keep: no value passed lies in it |
| Nothing passed | same | |
| Values of other kinds passed to an integer domain | same | |
| `i64::MIN`, `i64::MAX` as bounds | `arms.rs` `a_split_function_gives_what_the_function_gives_on_every_value` | |
| Type domain: bool given an int, a literal set, a bare atom, a tuple of bools | `edges.rs` `a_finite_type_domain_is_split_on_its_members_passed_and_nothing_else`; `arms.rs` tuple and literal-set tests | |
| Finite type passed none of its members | same | |
| `int`, `Utf8String`, a payload atom, a function: kept | `trick.rs` first two tests; `arms.rs` `the_trick_never_splits_a_function_domain` | |
| A family type (`->`, `->?`) as a domain: kept | `edges.rs` `a_family_domain_is_never_split` | |
| Values passed by test cases | `edges.rs` `the_values_of_test_cases_are_passed_as_static_calls_are` | |
| Values passed by calls once mixed | `trick.rs` `the_values_passed_are_read_from_the_calls_once_mixed` | |
| `passed` on a parameter out of range; an unknown name | `edges.rs` `the_values_of_test_cases_are_passed_as_static_calls_are` | |
| `split` refusals: no definition, not a function, no such parameter | `trick.rs` `one_specializer_splits_many_functions_as_each_split_alone_does` | |
| A split computes what the function does | `trick.rs` `a_split_function_computes_what_the_function_does`; `arms.rs` | |
| Many splits through one specializer | `trick.rs` `one_specializer_splits_many_functions_as_each_split_alone_does` | |
| The reason prints the domain in type syntax | `trick.rs` last two tests | |
| Kernel terms `Reindex`, `Discard`, `Reduce` with identity, `Fix`, `Gen` | | no L1 source elaborates to them; they come from later-layer forms and ZIR lowering |
| `unreachable!` arms ("a leaf", "asked above", and others) | | not reachable by construction |
