# l08_02_remap_map: `map` composed with remaps (plan row REMAP-map-tests, author P221)

Each case the row lists, and the test that covers it. "Model" means the result is also
checked against the kernel term of the M0 reference evaluator; "by hand" against a display
written out in the test.

| Case | Test | Checked against |
|---|---|---|
| `map` before and after a transpose (repack) | `forms::map_before_and_after_a_transpose` | by hand, model |
| `map` before and after a flattening to a tuple key (repack) | `forms::map_before_and_after_a_flattening_to_a_tuple_key` | by hand, model |
| `map` before and after a key shift `k + 1` | `forms::map_before_and_after_a_key_shift` | by hand |
| `><` at the inner level, `map` on each side; a map that distributes over `+` and one that does not | `forms::reducer_at_the_inner_level_a_map_before_and_after` | by hand, model |
| `><` at the outer level, `map` on each side | `forms::reducer_at_the_outer_level_a_map_before_and_after` | by hand, model |
| `><` at both levels after a `map` | `forms::reducer_at_both_levels_after_a_map` | by hand |
| `><` at the middle of three levels (`sales`), `map` on each side | `forms::reducer_at_the_middle_of_three_levels_a_map_before_and_after` | by hand |
| a `map` folding each row equals the reducer level | `forms::a_map_of_a_fold_equals_the_reducer_level` | by hand |
| widen by a key function, `map` on each side | `forms::map_before_and_after_a_widen_by_a_key_function` | by hand |
| widen by the value: a `map` before it changes the keys (does not commute) | `forms::a_widen_by_the_value_does_not_commute_with_map` | by hand |
| widen with a rank inserted, composed with `map` (order-keeping, order-reversing, constant) | `rank::*` (kernel); source form parked in /home/luke/Work/wt/failing-tests/L8.2.rs `desc_rank_after_a_map` (step L8.2 open) | by hand on the model |
| truncate after a `map` (to set leaves and to the outer level) | `forms::a_map_before_a_truncation_leaves_its_keys` | by hand |
| `map` after a truncation, over the key sets | `forms::a_map_after_a_truncation_reads_the_key_sets` | by hand |
| `map` inside the value expression of a remap | `forms::map_in_the_value_of_a_remap` | by hand |
| `map` of a whole row bound by a shorter `as` pattern (row REMAP-fewer-binders) | `forms::map_of_a_row_bound_by_a_shorter_pattern` | by hand, and equal to `m.map(r -> r.map(v -> v + 1))` |
| a remap inside `map`'s function | `forms::a_remap_in_the_function_of_a_map` | by hand |
| empty source | `forms::map_and_remap_of_an_empty_list` | by hand |
| a constant `map`, then a transpose | `forms::a_map_to_a_constant_then_a_transpose` | by hand |
| the law `xs.map(f) as K` equals `(xs as K).map(f)` for a key-only remap, on random families (transpose; tuple key with an affine component) | `law::map_commutes_with_a_key_only_remap_on_random_families` | model |
| scaling at 1x and 8x of one composed form (map, transpose with `><`, map) | `bench::map_transpose_fold_map_runs_in_linear_time` | T(8n)/T(n) |
| scaling at 1x and 8x of rows bound whole by a shorter `as` pattern (row REMAP-fewer-binders) | `bench::rows_bound_whole_run_in_linear_time` | T(8n)/T(n) |
