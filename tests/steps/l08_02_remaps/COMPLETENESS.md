# Completeness of the l08_02_remaps tests

Each case of DESIGN.md sec:remap_law, sec:grouping, sec:push_pull, sec:level_names and the
bounds table that the remap steps (L8.1, L8.2, L8.2a, L8.2b, L8.2c, EMPTY-level-swap) must
meet, with the test that covers it.

`kernel::` tests build the kernel term a remap elaborates to (`reindex`, `fold`, `discard`)
and run it on the reference evaluator. They check the value each rule gives. They do not check
the source syntax, the static checks or the messages: those need the source forms to compile.

The source forms do not compile on main yet. `as` and `into` parse, but the resolver rejects
them as "part of the Zed language but not compiled yet", and with them map and array displays,
`><`, `::`, sort keys, refinements and type declarations (elaborated at step L3.2 and later;
remaps at L8.1 and L8.2). The source-level tests of the second table below are kept on the
branch `wt/remap-tests` and join this group when they pass on main.

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
| `><` over an empty level, with and without an identity | sec:reduction, Boom table; bounds table row `m >< op` | `kernel::reduce_an_empty_level_with_and_without_an_identity` | value checked |
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
| Collision message and its menu (truncate, residue, fold, witness, check) | sec:remap_law worked example; sec:diagnostics row "Collision (T-Reindex)" | none | source test pending |
| Remap output name that names a source level and a value in scope | sec:diagnostics row | none | source test pending |
| Level names through remaps and derived names | sec:level_names | none | source test pending (L8.2b); names have no kernel form |
| Named slicing `m[n: k]`, several names, unknown name | sec:level_names | misses only, above | source test pending (L8.2c) |
| Several sort keys make one rank level; trailing comma rules | sec:remap_law; sec:lexical `,` row | none | source test pending (L8.1 grammar) |
| Binder naming a type in `as`/`into` patterns | step L8.2a | none | source test pending |

## Source-level tests

Each case again in source form, from the spec's own programs and expected outputs: the value is
compared with a display the spec writes, and a rejection's text with the spec's message where
the spec gives it. On main today 1 of these 60 passes (`moves::a_single_sort_key_takes_no_trailing_comma`,
a parse check); the other 59 stop at the resolver's "not compiled yet".

| Case | Covering tests |
|---|---|
| Repack: transpose, permute by name and by `as` binders, `as` alone | `moves::transpose_levels`, `moves::permute_levels_by_name`, `moves::permute_levels_by_as_binders`, `moves::as_alone_is_the_identity` |
| Repack: tuple keys | `moves::flatten_to_a_tuple_key`, `moves::untuple_a_tuple_key` |
| Repack: witnessed bijection `k + 1` | `moves::bijective_key_transform` |
| Widen: with the value, with derived data, by a key function | `moves::widen_a_key_with_the_value`, `moves::widen_a_key_with_derived_data`, `moves::widen_by_a_key_function` |
| Truncate, and `(k1 -> k2)` as sugar for it | `moves::truncate_to_set_leaves`, `moves::a_trailing_key_is_sugar_for_truncate`, `moves::truncate_to_the_outer_level` |
| Rank insertion `desc`, `asc`; ties grouped | `moves::desc_rank_groups_ties_beneath`, `moves::asc_rank`, `moves::a_filtered_list_sorted` |
| Several sort keys make one rank level; trailing comma after two keys; none after one | `moves::several_sort_keys_make_one_rank_level`, `moves::a_trailing_comma_after_several_sort_keys`, `moves::a_single_sort_key_takes_no_trailing_comma` |
| `><` at the innermost level, with `(+)`, `(++)`, a named function, a lambda | `names::reduce_with_plus_names_the_leaf_sum`, `names::reduce_with_concatenation_names_the_leaf_concat`, `names::reduce_with_a_named_function_takes_its_name`, `names::reduce_with_a_lambda_names_the_leaf_reduce` |
| `><` at two levels, and at every level | `names::two_reductions_derive_names_from_the_inside_out`, `names::reduce_at_the_outermost_level` |
| The worked collision: headline, each menu line, no witness line | `collisions::dropping_a_discriminator_is_the_worked_collision`, `collisions::the_dropped_level_menu_has_no_witness_line` |
| Each repair of the worked collision is accepted | `collisions::each_repair_of_the_worked_collision_is_accepted` |
| The check reads the pattern, not the data | `collisions::the_check_reads_the_pattern_not_the_data` |
| `rekey` without a witness: its menu (`group`, `@injective`, `#collision`) | `collisions::rekey_without_a_witness_is_rejected_with_its_menu` |
| Group levels: `group` and the residue pattern agree; a flat derived key is rejected with the residue repair | `collisions::group_declares_the_deeper_level`, `collisions::a_flat_pattern_on_a_derived_key_is_rejected_with_the_residue_repair`, `collisions::inverting_a_relation_into_sets` |
| Witness catalog, accepted entries | `collisions::witness_monotone_arithmetic`, `collisions::witness_modulo_at_the_width_of_the_modulus`, `collisions::witness_affine_packing`, `collisions::witness_unpacking_by_euclidean_div_and_mod`, `collisions::witness_unimodular_skew`, `collisions::witness_componentwise_maps`, `collisions::witness_injective_at_proof_grade` |
| Witness catalog, each side condition broken | `collisions::witness_modulo_one_wider_is_rejected`, `collisions::witness_affine_packing_one_short_is_rejected`, `collisions::witness_rank_one_affine_map_is_rejected`, `collisions::a_finitely_invertible_key_is_rejected` |
| Output name that names a source level and a value in scope | `collisions::an_output_name_that_shadows_a_value_in_scope` |
| Binder naming a type (L8.2a) | `collisions::a_binder_naming_a_type_in_a_pattern` |
| Level names: `::names`, through a permutation, through a join | `names::sales_names`, `names::a_permutation_carries_the_names`, `names::the_join_lines_example` |
| Named slicing (L8.2c): inner level, outermost level, two names, misses at every place, unknown name, a name twice, a string key on a list level | `names::slice_at_an_inner_named_level`, `names::slice_at_the_outermost_level_is_a_lookup`, `names::slice_by_two_names_in_any_order`, `names::slice_a_list_level_misses_with_out_of_bounds`, `names::slice_at_day_zero`, `names::slice_misses_at_every_place`, `names::slice_by_a_name_the_type_lacks`, `names::slice_naming_one_level_twice`, `names::slice_a_list_level_with_a_string_key` |
| Empty levels (EMPTY-level-swap): kept under a computed outer level, dropped by a transpose, ranked like any entry | `names::an_empty_inner_level_keeps_its_key_under_a_computed_outer_level`, `names::a_transpose_drops_an_empty_inner_level`, `names::a_rank_over_the_outer_level_ranks_an_empty_entry` |

Not covered by a source test, with the reason:

| Case | Reason |
|---|---|
| The warning `#emptyLevelDropped` | the test helpers return no warnings from elaboration; a test is added with the helper when EMPTY-level-swap lands |
| The uniqueness facet as a witness | the spec gives no program that declares it on a key; a test needs that example first |
| `@injective` below proof grade rejected | the spec does not say which claims stay below proof grade on a given checker; no test can fix an expected verdict |
