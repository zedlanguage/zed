# Completeness: l07_03_unit_log_off

Step L7.3 (DESIGN.md), the unit item `@log(#off);`: it stands at the top level of a unit, at
most once, and turns the unit's logging off; a run gives the same outputs in each kind of
build with or without it. Plan row TEST-complete-ports (author P189). Coverage before and
after is in l01_19_whole_file_ports/COMPLETENESS.md.

| Case | Covering test | Or reason none is needed |
|---|---|---|
| The item recorded on the resolution | `resolution.rs::the_unit_item_is_recorded_on_the_resolution` | |
| The item alone, with and without a line end, first, last without a line end, between two functions, on a function's line, after a comment, before `main`, after a test table | `combinations.rs::the_unit_item_is_recorded_wherever_it_stands_at_the_top_level` | |
| The item in `main`'s block, in a function body, in an `if` branch, refused at its place | `combinations.rs::the_unit_item_in_any_block_is_refused_at_its_place` | |
| Every other unit item refused with its reason; the item twice in a unit | `resolution.rs::every_other_unit_item_is_refused_with_its_reason`, `resolution.rs::a_unit_has_the_item_once` | |
| Built apart from the declarations; below L7 the text is not the item | `items.rs::the_unit_item_builds_apart_from_the_declarations`, `items.rs::below_layer_l7_the_text_is_not_the_unit_item` | |
| An annotation before a parenthesized statement; formatting; the semicolon required | `items.rs` (last three tests) | |
| A run is the same with the item; its test tables run; a refused item stops the run | `run.rs` (all three tests) | |
| The kinds of build: an undefined one named with its line; build stage and build dependent are no kinds of build; outputs the same in each with and without the item | `modes.rs` (all four tests) | |
| `@log` before a declaration | | Left out: that is the declaration annotation of step L7.3, which zedc does not build yet; this group covers the unit item only. |
| Many units | `scaling.rs::each_unit_is_built_formatted_and_refused_at_small_sizes` | Small scaling run (P178). |
