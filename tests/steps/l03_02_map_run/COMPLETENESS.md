# L3.2 completeness, plan row MAP-run: `map` and the data forms it needs

Code under test: the map, array and set displays, `.map(f)`, `.where(p)`, lookups that miss,
`in` and `not in`, and `><` by a built-in operator, from name resolution to the run
(`crates/zedc-resolve/src/resolve.rs`, `crates/zedc-check/src/check/walk.rs`,
`crates/zedc-elab/src/elab/walk.rs`, `crates/zed-kernel/src/eval.rs` `Prim::Entries` and
`Prim::Has`) (DESIGN.md steps L3.2 and L3.3, sec:reduction, sec:keypaths, sec:remap_law).

Each case of `runs.rs` is run three ways: by the M0 model (the zed-kernel reference evaluator on
the kernel term the spec defines the form by), by `zedc run`, and by an executable `zedc build`
makes (the native path). The three must print the same text.

| Case | Covering test, or the reason none is needed |
|---|---|
| `{0 -> 1, 1 -> 2}.map(x -> x + 1)` keeps its keys (the step's own test) | `runs::each_case_run_by_the_interpreter_gives_the_models_value` (case `map_keeps_the_keys`), `runs::an_executable_gives_each_cases_value` |
| `map` over an array, a string-keyed map, each level of a nested family | the two tests above, cases `map_of_an_array`, `map_of_a_string_keyed_map`, `map_of_each_level` |
| `map` of a row-level function (`r -> r >< (+)`) over a family of families | cases `sum_of_each_row`, `in_of_each_row` |
| Composition: `xs.map(f).map(g)` equals `xs.map(x -> g(f(x)))` | `runs::map_then_map_is_map_of_the_composite`, cases `map_then_map`, `map_of_the_composite` |
| `where` keeps the keys of the entries it keeps; over string keys; with `map` and `><` | cases `where_keeps_the_keys_of_the_entries_it_keeps`, `where_of_a_string_keyed_map`, `map_then_where_then_sum` |
| Lookups that miss: `#notFound` on a map, `#outOfBounds` on an array, after `where` | `runs::reads_that_miss_give_the_miss_atoms`, case `where_then_a_missed_read` |
| `><` by `+`, `*` and `&&`; an empty level | cases `sum`, `product`, `all_of_bools`, `sum_of_an_empty_row_is_empty`, `fold_of_an_empty_display_is_empty` |
| Set displays and `in` on a set | cases `a_set_display`, `in_of_a_set_tests_an_element` |
| `in` and `not in` test keys | cases `in_tests_a_key`, `in_of_a_missing_key`, `not_in` |
| A loose atom in the entries passes through `map` | case `map_passes_a_loose_atom_through` |
| Refusals: a disjoint key (R11); `map` given two functions or a non-function; `map` of a value with no entries; `where` whose test is not `bool`; a fold of a row that may be empty, in a function's body | `types::*` (5 tests) |
| Forms not built, refused as not compiled: a range, an operator section outside `><`, a metadata read, a fold by an operator with no built-in identity, `where` over entries that may be loose atoms | `types::the_forms_not_built_are_refused_as_not_built`, `types::a_fold_by_an_operator_without_a_built_in_identity_is_not_built`, `types::where_over_loose_atoms_is_not_built` |
| Scaling: `map` and `><` at n and 8n, the kernel run and the whole `zedc run` path | `bench::*` (3 benchmarks, `--bench`); ratios 8.40, 8.01 and 8.39 on 2026-11-14 |
| One-generator `for`, standalone `discard`, `.foldl` and `.foldr`, float folds | Not built (plan row MAP-run lists the steps); refused at name resolution or in the checker |
