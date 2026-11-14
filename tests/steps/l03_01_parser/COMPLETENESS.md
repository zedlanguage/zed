# L3.1 completeness: the parser of layer L3

Code under test: the building of ranges, displays of arrays, sets and maps, indexing,
membership (`in`, `not in`), reductions (`><`), sections, metadata reads (`::`), `for`, range
patterns and family types (`crates/zedc-syntax/src/ast/mod.rs`, `node.rs`, `types.rs`), and
their formatting (`format.rs`) (DESIGN.md sec:grammar, step L3.1). Every alternative of these
rules also has a case in l01_08 `grammar_cases.rs`.

Coverage: shared with the other groups of this row (`ast/mod.rs` 94.4% to 94.5%, `format.rs`
96.8% to 98.8%). The formatter's walk of an index key that starts with `in` (`format.rs` lines
192 to 201) is reached by no unit this zedc builds; see l01_13.

| Case | Covering test, or the reason none is needed |
|---|---|
| Ranges with each end, empty displays and ranges | `forms::ranges_build_with_each_end`, `corners::empty_displays_and_ranges` |
| Displays as arrays, sets and maps; a display is a set or a map; a family type is not a display | `forms::displays_build_as_arrays_sets_and_maps`, `corners::a_display_is_a_set_or_a_map`, `corners::a_family_type_is_not_a_display` |
| Rank-keyed arrays: the desugaring rules, rank order, the empty display and one element, nesting, formatting, resolution | `arrays::*` (6 tests) |
| Indexing and membership; `not in` is one test, negation another | `forms::indexing_and_membership_build`, `corners::not_in_is_one_test_and_negation_is_another` |
| Reductions, folds and sections; nested sections are one section; reductions chain from the left | `forms::reductions_folds_and_sections_build`, `corners::nested_sections_are_one_section`, `corners::reductions_chain_from_the_left` |
| Metadata reads; a read applied to a call result | `forms::metadata_reads_build`, `corners::a_read_applies_to_a_call_result` |
| `for` with binders, source, guard and body; nested in its head and in displays | `forms::a_for_builds_its_binders_source_guard_and_body`, `corners::a_for_nests_in_its_head_and_in_displays` |
| Range patterns and family types | `forms::range_patterns_and_family_types_build` |
| Formatting, parentheses the grammar needs, a statement that opens with a display | `formatting::*` (3 tests) |
| Later forms and parts name their step | `later::*` (2 tests) |
| Large inputs | Benchmarks `bench::*`; `scaling::each_form_is_built_formatted_and_refused_at_small_sizes` |
