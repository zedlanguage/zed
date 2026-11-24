# Completeness of the l08_02_remaps tests

Each case of DESIGN.md sec:remap_law, sec:grouping, sec:push_pull, sec:level_names and the
bounds table that the remap steps (L8.1, L8.2, L8.2a, L8.2b, L8.2c, EMPTY-level-swap) must
meet, with the test that covers it.

`kernel::` tests build the kernel term a remap elaborates to (`reindex`, `fold`, `discard`)
and run it on the reference evaluator. They check the value each rule gives. They do not check
the source syntax, the static checks or the messages: those need the source forms to compile.

The source-level tests (`moves::`, `rules::`, `collisions::`, `empty::`, `bench::`) run the
programs through the compiler: the value against a display the spec writes, a rejection's text
against the spec's message where it gives one. Forms the compiler does not build yet are tested
in /home/luke/Work/wt/failing-tests under the row that builds them (second list below), and join
this group when they pass.

| Case | Spec | Covering test | Status |
|---|---|---|---|
| Transpose two levels | sec:remap_law, repack | `kernel::transpose_levels` | value checked |
| Permute three levels by name, and back | sec:level_names, transfer table | `kernel::permute_three_levels_and_back` | value checked |
| `as` alone is the identity | sec:remap_law | `kernel::as_alone_is_the_identity` | value checked |
| Flatten to a tuple key, and untuple | sec:remap_law, repack | `kernel::flatten_to_a_tuple_key_and_back` | value checked |
| Bijective key transform `k + 1` | sec:remap_law, repack | `kernel::bijective_key_transform` | value checked |
| Widen a key with the value | sec:remap_law, widen | `kernel::widen_a_key_with_the_value` | value checked |
| Widen a key with derived data `(k, f(k))` | sec:remap_law, widen | `kernel::widen_a_key_with_derived_data` | value checked |
| Widen by a key function, `i div 10` over 100 entries | bounds table | `kernel::widen_by_a_key_function_gives_ten_groups_of_ten` | value checked; the static bound (ten groups of ten, `card`) needs L8.2 |
| Truncate to set leaves | sec:remap_law, truncate | `kernel::truncate_drops_the_values_and_keeps_the_keys` | value checked |
| Truncate to the outer level, and to three levels | sec:remap_law, truncate; worked collision | `kernel::truncate_to_the_outer_level` | value checked |
| Collision when a discriminating level is dropped above surviving values | sec:remap_law, the illegal move | `kernel::dropping_a_discriminator_above_surviving_values_collides` | run-time collision checked; the compile-time message and menu need L8.2 |
| `><` at the innermost level | sec:level_names, `totals` | `kernel::reduce_the_innermost_level` | value checked |
| `><` at two levels, inside out | sec:level_names, derived names | `kernel::reduce_two_levels_from_the_inside_out` | value checked |
| `><` at a middle level | sec:alternatives, "A reduction over a level by its name" | `kernel::reduce_a_middle_level` | value checked |
| `><` at the outermost level | sec:reduction | `kernel::reduce_the_outermost_level` | value checked |
| `><` at every level | sec:reduction | `kernel::reduce_every_level` | value checked |
| `><` with `(++)`, in key order | sec:level_names, `labels` | `kernel::reduce_with_concatenation_in_key_order` | value checked |
| `><` with `max` and `(*)` | sec:level_names, transfer and derived-name tables | `kernel::reduce_with_max_and_with_product` | value checked |
| `><` with a lambda | sec:level_names, derived names | `kernel::reduce_with_a_lambda` | value checked |
| `><` over an empty level, with and without an identity | sec:reduction, obligations table; bounds table row `m >< op` | `kernel::reduce_an_empty_level_with_and_without_an_identity` | value checked |
| Group by a derived key with the residue written | sec:grouping | `kernel::group_by_a_derived_key_with_the_residue_written` | value checked |
| Word count: group, then fold | sec:tour_collections | `kernel::word_count_groups_then_folds` | value checked |
| Scatter and gather as one grouping remap | sec:push_pull | `kernel::a_scatter_and_a_gather_are_one_grouping_remap` | value checked |
| Invert a relation into a set per key | sec:power, `whoTeaches` | `kernel::invert_a_relation_into_a_set_per_key` | value checked |
| Rank insertion `desc`, ties grouped beneath, and `asc` | sec:remap_law, ranking | `kernel::desc_inserts_a_rank_with_ties_grouped_beneath` | value checked |
| A filtered list ranks under its kept positions | sec:remap_law, ranking | `kernel::a_filtered_list_ranks_under_its_kept_positions` | value checked |
| Witness: strictly monotone arithmetic `2*k` | sec:grouping, catalog | `kernel::witness_strictly_monotone_arithmetic` | value checked |
| Witness: `k mod p` over at most `p` integers; one wider collides | sec:grouping, catalog | `kernel::witness_modulo_over_a_range_no_wider_than_the_modulus` | value and collision checked |
| Witness: affine packing; one stride short collides | sec:grouping, catalog | `kernel::witness_affine_packing_and_its_stride_condition` | value and collision checked |
| Witness: unpacking by Euclidean `div`/`mod`, negative keys | sec:grouping, catalog | `kernel::witness_unpacking_is_the_inverse_under_euclidean_division` | value checked |
| Witness: unimodular skew and its inverse | sec:grouping, catalog | `kernel::witness_unimodular_skew_and_its_inverse` | value checked |
| Witness: full column rank, not square; rank one collides | sec:grouping, catalog | `kernel::witness_full_column_rank_that_is_not_square` | value and collision checked |
| Witness: componentwise maps on a tuple key | sec:grouping, catalog | `kernel::witness_componentwise_maps_on_a_tuple_key` | value checked |
| Witness: literal key occurrence (written residue) | sec:grouping, catalog | `kernel::group_by_a_derived_key_with_the_residue_written` | value checked |
| Witness: tupling and permutation | sec:grouping, catalog | `kernel::flatten_to_a_tuple_key_and_back`, `kernel::permute_three_levels_and_back` | value checked |
| Witness: `@injective` at proof grade, and below it | sec:grouping, catalog | none in the kernel | a static fact with no run-time form; source test pending |
| Witness: the uniqueness facet at proof grade | sec:grouping, catalog | none in the kernel | a static fact with no run-time form; source test pending |
| A finitely invertible key map `k div 2` collides; its residue makes it legal | sec:push_pull, conversion table | `kernel::a_finitely_invertible_key_map_needs_its_residue` | value and collision checked |
| Miss at a `->?` level is `#notFound` | sec:level_names, named slicing | `kernel::a_slice_below_the_top_misses_with_not_found` | value checked |
| Miss at an integer-interval level is `#outOfBounds` | sec:level_names, named slicing | `kernel::a_read_past_a_short_list_level` | value checked |
| Pull through an injective rekey misses with `#notFound` off its image | sec:push_pull, conversion table | `kernel::an_injective_rekey_reads_back_with_not_found_off_its_image` | value checked |
| Empty inner level keeps its key where the output can place it; transposed it is dropped | sec:remap_law; author Q4 | `kernel::an_empty_inner_level_keeps_its_key_where_the_output_can_place_it` | value checked; the warning `#emptyLevelDropped` needs EMPTY-level-swap |
| Two sources: matrix product folds the shared level | sec:joins | `kernel::matrix_product_folds_the_shared_level` | value checked |
| Collision message and its menu (truncate, residue, fold, witness, check) | sec:remap_law worked example; sec:diagnostics row "Collision" | none | source test pending |
| Remap output name that names a source level and a value in scope | sec:diagnostics row | none | source test pending |
| Level names through remaps and derived names | sec:level_names | none | source test pending (L8.2b); names have no kernel form |
| Named slicing `m[n: k]`, several names, unknown name | sec:level_names | misses only, above | source test pending (L8.2c) |
| Several sort keys make one rank level; trailing comma rules | sec:remap_law; sec:lexical `,` row | none | source test pending (L8.1 grammar) |
| Binder naming a type in `as`/`into` patterns | step L8.2a | none | source test pending |

## Source-level tests

All 215 tests of the group pass, the 35 benchmarks run apart (2026-11-15, closure-id).

| Case | Covering tests |
|---|---|
| Repack: transpose, permute by `as` binders, `as` alone | `moves::transpose_levels`, `moves::permute_levels_by_as_binders`, `moves::as_alone_is_the_identity` |
| Repack: tuple keys | `moves::flatten_to_a_tuple_key`, `moves::untuple_a_tuple_key` |
| Repack: witnessed bijection `k + 1` | `moves::bijective_key_transform` |
| Widen: with the value, by a key function of the key or of the value, by parity | `moves::widen_a_key_with_the_value`, `moves::widen_by_a_key_function`, `rules::widening_by_the_value_and_by_a_function_of_the_key`, `rules::widen_by_a_key_function_of_the_value_as_an_outer_level`, `rules::widen_a_list_by_the_parity_of_its_keys` |
| Truncate, and a trailing key as sugar for it | `moves::truncate_to_set_leaves`, `moves::truncate_to_the_outer_level`, `moves::a_trailing_key_is_sugar_for_truncate`, `rules::truncation_drops_the_values`, `rules::truncation_to_the_outer_level_drops_a_level`, `rules::a_trailing_key_binder_is_truncation_sugar` |
| One sort key takes no trailing comma (a parse check) | `moves::a_single_sort_key_takes_no_trailing_comma` |
| `><` at the inner, middle and outer level, at two levels, at every level; by `(+)`, `(*)`, `(&&)`, `(\|\|)`; written first | `rules::a_fold_at_the_inner_level`, `rules::a_fold_at_the_middle_level_of_three`, `rules::a_fold_at_the_outer_level_of_three`, `rules::folds_at_two_levels_of_three`, `rules::a_fold_of_a_level_between_two_kept_ones`, `rules::every_level_folded_gives_the_total`, `rules::every_level_of_three_folded_gives_the_total`, `rules::a_fold_by_multiplication_and_a_transformed_leaf`, `rules::folds_by_and_and_by_or`, `rules::a_fold_written_first_folds_its_level` |
| Group levels: `group` and the residue pattern agree; group then fold; word count | `rules::group_declares_the_deeper_level`, `rules::group_by_a_constant_gives_one_class`, `rules::group_on_a_map_by_an_integer_class`, `rules::group_then_fold_each_group`, `rules::word_count_folds_a_constant_leaf`, `collisions::inverting_a_relation_into_sets` |
| Flat map adjoins a level, keeps an empty emission | `rules::flat_map_adjoins_the_emitted_level`, `rules::flat_map_keeps_an_empty_emission_as_an_empty_level` |
| The worked collision: headline, menu, each repair runs; the check reads the pattern, not the data | `rules::the_worked_collision_menu`, `rules::the_worked_collision_repairs_run`, `rules::the_collision_is_found_for_one_entry_per_group_too`, `collisions::the_check_reads_the_pattern_not_the_data` |
| Collision menus by kind of key: constant, projection, value-derived, the value alone, a square | `collisions::a_constant_key_collides_with_its_menu`, `collisions::a_projection_of_a_tuple_key_collides`, `collisions::a_key_computed_from_the_value_collides`, `collisions::the_value_as_the_only_key_collides`, `collisions::a_square_that_is_not_monotone_collides`, `collisions::a_flat_pattern_on_a_derived_key_is_rejected_with_the_residue_repair`, `collisions::a_finitely_invertible_key_is_rejected` |
| `rekey` without a witness: its menu (`group`, `@injective`, `#collision`) | `rules::rekey_without_a_witness_is_rejected_with_its_menu` |
| Witness catalog, accepted entries | `collisions::witness_monotone_arithmetic`, `collisions::witness_strictly_decreasing_arithmetic`, `collisions::witness_tupling_and_permutation_of_witnessed_components`, `collisions::witness_componentwise_maps`, `collisions::witness_unimodular_skew`, `collisions::witness_affine_map_of_full_column_rank_that_is_not_square`, `collisions::witness_affine_packing_at_three_levels`, `rules::modulo_on_keys_within_the_modulus`, `rules::affine_packing_and_one_stride_short`, `rules::div_and_mod_together_recover_the_key` |
| Witness catalog, side conditions broken | `rules::modulo_one_wider_is_rejected`, `rules::affine_packing_and_one_stride_short`, `collisions::witness_rank_one_affine_map_is_rejected` |
| Binder naming a type (L8.2a) | `collisions::a_binder_naming_a_type_in_a_pattern` |
| Empty levels: kept under a computed outer level (the DESIGN example `(k, k.upper)`), under a tuple, by truncation and widening; dropped by a transpose, a flatten, a fold of the outer level; `k.upper` alone collides | `empty::*` |
| Folds of an empty level: identities of `+`, `*`, `&&`, `\|\|`; `#empty` for `max`, `min` at `int` | `empty::a_sum_of_an_empty_level_is_zero`, `empty::a_sum_and_a_product_of_a_level_emptied_by_a_filter`, `empty::and_and_or_of_an_empty_level_are_their_identities`, `empty::max_and_min_of_an_empty_int_level_are_empty` |
| Miss atoms of reads on remap and group results; a constant read past the keys | `empty::the_identity_remap_of_a_list_misses_as_a_list`, `empty::a_shifted_remap_misses_with_not_found`, `empty::a_constant_read_past_the_keys_is_rejected`, `rules::a_read_of_a_remap_or_group_result_may_miss`, `rules::a_float_key_is_read_only_whole` |
| Each form's own errors | `rules::the_pattern_s_own_errors`, `rules::the_source_must_be_a_family_of_the_pattern_s_depth`, `rules::group_s_own_errors`, `rules::flat_map_s_own_errors` |
| An `as` pattern of fewer key levels than its source binds each row whole (row REMAP-fewer-binders): the identity, a tupled key, a read of the row, a truncation, a transpose of three levels by two binders, an empty row; negative control, a pattern of the source's depth | `rules::fewer_binders_than_levels_bind_the_whole_row`, `rules::fewer_binders_keep_rows_apart_in_a_truncation_and_in_a_transpose`, `rules::a_row_bound_whole_may_be_empty`, `rules::as_many_binders_as_levels_bind_no_row` |
| The source is a `map` lambda's parameter or a generic function's: a remap, a fold of every level, `as` alone and `group` give what they give on each inner family written out; over empty families; a function never called compiles, and its pattern's errors are given; two calls whose keys are kept apart for different reasons record both; `group` and a remap of a parameter that is no family, and `rekey`, are rejected as elsewhere | `rules::a_remap_of_a_map_lambdas_parameter`, `rules::a_group_of_a_map_lambdas_parameter`, `rules::a_fold_of_every_level_of_a_map_lambdas_parameter`, `rules::an_identity_remap_of_a_map_lambdas_parameter`, `rules::a_remap_or_group_of_a_map_lambdas_parameter_over_empty_families`, `rules::a_remap_and_a_group_of_a_generic_functions_parameter`, `rules::a_generic_function_never_called_is_accepted`, `rules::a_generic_remap_s_pattern_errors_are_given_without_a_call`, `rules::a_generic_remap_at_two_types_records_both_reasons`, `rules::a_map_lambdas_parameter_that_is_no_family_is_rejected`, `rules::rekey_of_a_map_lambdas_parameter_is_rejected_as_any_rekey` |
| A `map` lambda's or generic function's parameter below known levels of the source, `({ 0 -> r }) as (a -> k -> v) into (k -> a -> v)`, one level and two below, at two types and through a call; a parameter that is no family is rejected with what it holds | `rules::a_remap_of_a_map_lambdas_parameter_below_a_known_level`, `rules::a_remap_of_a_generic_functions_parameter_below_a_known_level`, `rules::a_remap_below_a_known_level_is_checked_at_each_type_and_through_calls`, `rules::a_remap_two_levels_below_a_known_level`, `rules::a_remap_below_a_known_level_rejects_a_value_that_is_not_a_family` |
| A generic fold called at two carriers through a function declared in a block (in a definition's block, a function's body, a `.map` lambda, `main`), directly, through a second block function and through one nested in its body: each call at its own identity; such a function bound to a name and called through it at two identities runs at each | `empty::a_fold_in_a_function_declared_in_a_block_takes_the_identity_of_each_call`, `empty::a_function_declared_in_a_block_and_named_as_a_value_at_two_carriers_runs_at_each`, `three_way::block_functions_at_two_carriers_agree_with_the_model_interpreted_and_built` |
| A generic fold at two carriers through a function value (row REDUCE-generic-identity-values): a lambda bound to a name in a block, a name bound to `top` and a name bound to that name, at the top level and in a block, `top` or a block's function passed to a call whose result does not hold it; two or three calls deciding one fold in force at one read (`.map` calls nested at `int`, `f64`, `int`), each read at the identity of the call that checked it; a generic function whose tuple result holds a fold at its call's carrier and a `.map` of one at `f64`. A function a call returns and that runs later at another carrier is refused | `empty::a_generic_fold_at_two_carriers_through_a_function_value_runs_at_each`, `empty::a_function_a_call_returns_and_runs_at_another_carrier_is_not_compiled_yet`, `kept::a_block_function_named_as_a_value_where_it_is_called_runs_the_body_of_each_call`, `three_way::function_values_and_reads_under_two_identities_agree_with_the_model_interpreted_and_built` |
| Each way to refer to a block's function whose calls run a fold at two types (row PROOF-block-body-kept-when-named): named as a value (a tuple's member, an `if`'s branch, a map's or array's entry, a block's result, captured by a lambda, a function's body, a parameter's default, a port push in `main`, never used, and bound or aliased where the name is used other than in a call) keeps the written body and refuses its fold; bound or aliased and called through the name, or passed to a call that decides its folds, runs a body made at each call's identity (REDUCE-generic-identity-values); calls (by name, UFCS, indexing, in parentheses, curried with `...`, a bracket section, `~f~` infix, from a default, from a lambda run in place, from a generic function's block) run a body made at each call's identity; `::source`, `><` by a function, a law, a test table, interpolation and `==` are refused before elaboration or by the checker. A kept term that names a dropped written body is refused naming the function | `kept::*`; zedc-elab's unit tests `elab::dropped_tests::*` |
| A remap of a parameter declared a partial map with a range on its key (RANGE-keys) in functions that call each other or themselves: only the recursion is reported, with no error of a key or a remap, also where only one of them remaps and where a call passes keys outside the range; a function outside the cycle still has its keys checked; a remap in a lambda or a function in the body is read before the function's check ends, so a call is checked as passing a family (row TEST-range-keys-mutual-recursion) | `recursion::*` |
| A lambda that calls a parameter, returned in a family a call returns (row FAIL-family-lambda-calls-param): in an entry, a tuple in an entry, a family in an entry, an array; and in a family that carries the need of `f(1)` (`h(f) = {"k" -> f(1)}`), bare, beside a value in a tuple, and closing over the value `f` is applied to | `empty::a_family_holding_a_lambda_that_calls_a_parameter_runs`, `empty::a_family_with_needs_holding_a_lambda_that_calls_a_parameter_runs` |
| Scaling | `bench::*` |

## Tests waiting in /home/luke/Work/wt/failing-tests

Each file names its row, the message the compiler gives today, and the expected output quoted
from DESIGN.

| Case | File (row) |
|---|---|
| Witness catalog entries that need a range-bounded `->?` parameter: modulo, packing, unpacking | `RANGE-L1.rs` |
| `@injective` at proof grade on distinct values; repeated values collide | `L16.2.rs` (with L16.3) |
| Rank insertion `desc`, `asc`, several sort keys, trailing comma, a rank without residue collides, a rank over an empty entry | `L8.2.rs` |
| `sort` flat on a list, under kept positions after `where` | `L5.1.rs` |
| Names through remaps and reductions, by-name `into`, the join `lines`, an output name that shadows a value | `L8.2b.rs` |
| `sales::names` | `L7.1b.rs` |
| Named slicing | `L8.2c.rs` |
| The warning `#emptyLevelDropped`, and none after `group` | `EMPTY-level-swap.rs` |
| `><` by `max` (empty `int` level), `min`, a lambda, a named function in a pattern | `REDUCE-by-function.rs` |
| `max` and `min` of an empty `f64` level: `-inf`, `inf` | `FAIL-f64-max-empty-identity.rs` |
| A function a call returns, as the lambda `h3(f, y) = (f(y), f)` is passed and returns, run after the call at another carrier than the one the call ran it at | `REDUCE-identity-escaping-values.rs` |
| `group` of a family of families | `GROUP-nested.rs` |
| `m.map(f)` and `m.map(x -> f(x))` with `f` and `m` unannotated parameters | `FAIL-map-generic-parameter-function.rs` |
| Word count with a trailing `>< (+)` | `REDUCE-family-entries.rs` |
| A group level is never empty, so `>< max` of each group has no `#empty` | `L4.8.rs` |

Not covered, with the reason:

| Case | Reason |
|---|---|
| The uniqueness facet as a witness | L16.3; the spec gives no program that declares it on a key yet |
| `@injective` below proof grade rejected | the spec does not say which claims stay below proof grade on a given checker |
| The empty `f64` sum | prints `-0.0`, the identity of IEEE 754 addition; DESIGN says only that `sum` "gets `0` from its identity" (row SPEC-empty-f64-sum) |
