# Completeness: l02_08_import_pinning

Step L2.8 (DESIGN.md, sec:units): the build writes into each unpinned import the content
address of the unit it names, checks each pinned import and stops at a stale one with its
repairs, and keeps the prelude's pin in the pin file `zed.pins` at the package root. Plan row
TEST-complete-ports (author P189). Coverage before and after is in
l01_19_whole_file_ports/COMPLETENESS.md.

| Case | Covering test | Or reason none is needed |
|---|---|---|
| An unpinned import gets the address of the unit it names | `imports.rs::an_unpinned_import_gets_the_address_of_the_unit_it_names` | |
| A matching pin is checked and nothing is written | `imports.rs::a_pinned_import_that_matches_is_checked_and_nothing_is_written`; `command.rs::a_run_writes_the_pins_and_a_second_run_writes_nothing` | |
| The address follows the exports only; a comment-only change keeps the pin | `imports.rs::the_address_follows_the_exports_and_nothing_else`, `imports.rs::a_comment_only_change_keeps_the_pin` | |
| A changed unit makes its pin stale; the build stops with two repairs | `imports.rs::a_changed_unit_makes_its_pin_stale_and_the_build_stops_with_two_repairs`; `command.rs::a_stale_pin_stops_the_run_at_the_import_in_its_file` | |
| A pin that is no address at all stops the build and is left as written | `combinations.rs::a_pin_that_is_no_address_of_the_unit_stops_the_build_and_is_left_as_written` | |
| A stale pin beside an unpinned import: the other is still pinned | `combinations.rs::a_stale_pin_does_not_keep_another_import_from_being_pinned` | |
| A stale pin in a nested scope is reported at its import | `combinations.rs::a_stale_pin_in_a_nested_scope_is_reported_at_its_import` | |
| Selective, aliased and nested imports pinned where each is written; only unpinned ones written | `imports.rs::selective_aliased_and_nested_imports_are_pinned_where_each_is_written`, `imports.rs::only_the_imports_with_no_pin_are_written` | |
| A comment before the semicolon stays after the pin; the formatter keeps the build's text | `imports.rs::a_comment_before_the_semicolon_stays_after_the_pin`, `imports.rs::the_formatter_leaves_a_pinned_unit_as_the_build_wrote_it` | |
| A unit that does not compile alone, is missing, or does not parse is not pinned | `imports.rs::a_unit_that_does_not_compile_alone_is_neither_pinned_nor_checked`, `imports.rs::an_import_of_a_unit_that_is_not_there_or_does_not_parse_is_not_pinned` | |
| Many importers address one unit once; pins do not depend on the roots | `imports.rs::many_importers_of_one_unit_address_it_once`, `imports.rs::the_pins_of_a_package_do_not_depend_on_its_roots` | |
| LF, CRLF, lone CR and mixed line ends kept around the pins (A90) | `command.rs::a_file_with_crlf_lines_keeps_them_around_its_pins`, `command.rs::a_file_with_lone_cr_or_mixed_line_ends_keeps_them_around_its_pins` | |
| The pin file is written with `\n` beside a CRLF manifest (A90) | `command.rs::the_pin_file_ends_its_lines_with_lf_beside_a_crlf_manifest` | |
| The prelude pin: written, checked, stale at the manifest, replaced on a new path, dropped with no prelude | `prelude.rs` (first four tests); `command.rs::the_prelude_pin_is_written_into_the_pin_file_at_the_root` | |
| Pins of kinds a later step writes are kept | `prelude.rs::pins_of_kinds_a_later_step_writes_are_kept_as_they_are` | |
| Pin file lines: no pin, a kind and key twice, a fixed order on round trip | `pin_file.rs` (all three tests) | |
| The pin file made when missing; never written when it appeared, changed or went away during the build | `combinations.rs::the_pin_file_is_made_when_missing_and_never_written_over_a_change` | |
| Many imports, importers and pins | `bench.rs`, `scaling.rs` | Benchmarks and small scaling runs (P178). |
