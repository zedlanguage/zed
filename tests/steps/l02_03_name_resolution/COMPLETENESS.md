# L2.3 name resolution across units: cases and the tests that cover them

Code under test: `crates/zedc-resolve/src/resolve.rs` at layer L2 (imports, qualified names,
aliases, structs, methods, type parameters, match arms), `crates/zedc/src/unit.rs` (loading a
package of units, the manifest, the prelude unit) and `crates/zedc/src/query.rs` (the query
database). Measured with `-C instrument-coverage` and `llvm-cov` over this group alone,
regions% / lines%, before the qualified-type tests of `complete.rs` were added: `unit.rs` 82.55 /
77.63 before and 86.54 / 81.58 after; `query.rs` 59.82 / 55.74 unchanged.

| Case | Test that covers it | Or reason none is needed |
|---|---|---|
| Selective import brings in its names; an undefined one is rejected | imports.rs `a_selective_import_brings_in_the_names_it_lists`, `a_name_the_unit_does_not_define_is_rejected_at_the_import` | |
| Qualified import by last name; alias by its own | imports.rs `a_qualified_import_names_the_unit_by_its_last_name_and_an_alias_by_its_own` | |
| Qualified member undefined; qualifier shadowed by a parameter; qualifier is no value | imports.rs `a_qualified_member_the_unit_does_not_define_is_rejected`, `a_qualifier_is_a_name_that_a_parameter_shadows`, `a_qualifier_is_no_value` | |
| Qualified type: a type of the unit, a non-type, a missing name, an unimported qualifier | complete.rs `a_qualified_type_names_a_type_of_an_imported_unit_or_is_refused`; imports.rs `a_type_of_another_unit_is_not_yet_linked` | |
| Ambiguous name, used or unused; top level shadows it | imports.rs `a_name_two_units_bring_in_is_ambiguous_where_it_is_used`, `an_unused_ambiguous_name_is_no_error_and_a_top_level_definition_shadows_it` | |
| Ambiguous qualifier or alias: the repair | none merged | Fails: row FAIL-ambiguous-qualifier-repair; test in wt/failing-tests/FAIL-ambiguous-qualifier-repair.rs |
| Overloads from two units and the unit | imports.rs `functions_of_one_name_from_two_units_and_the_unit_are_one_overload_set` | |
| One unit imported twice | imports.rs `one_unit_imported_twice_brings_in_one_binder_without_ambiguity` | |
| Block imports: seen in the block, shadow the top level, rebinding either order | imports.rs (4 tests) | |
| `local` declarations | units.rs `a_local_declaration_is_visible_in_its_unit_and_not_through_an_import`, `local_is_a_node_...`, `local_marks_a_top_level_definition_only` | |
| Unit with no file; root with no file; path under the root and back | units.rs (3 tests) | |
| A unit that does not parse | units.rs `a_unit_that_does_not_parse_reports_its_own_error_and_its_importer_none` | |
| A unit or prelude unit that does not lex | complete.rs `a_unit_that_does_not_lex_reports_its_own_error_and_its_importer_none`, `a_prelude_unit_that_does_not_lex_reports_its_own_error_only` | |
| A file the system will not give (import, root, manifest, pins, prelude) | complete.rs `a_file_the_system_will_not_give_is_reported_with_the_repair_wherever_it_is_read` | |
| Source checks: not UTF-8, byte order mark, not NFC, CRLF | source.rs (6 tests) | |
| Import cycles: two, three with a chord, self, disjoint, nested, ties by text order, every root order | cycles.rs (12 tests); units.rs (cycle tests) | |
| Diamond read once | units.rs `a_diamond_is_no_cycle_and_each_unit_is_read_once` | |
| `main::files` in a unit with its own main | units.rs `main_files_in_a_unit_with_its_own_main_is_rejected_unless_the_unit_is_the_root`; scaling.rs | |
| Manifest: names the prelude unit or nothing; entries once, plain strings; refused stops the package | manifest.rs (6 tests); complete.rs `a_manifest_that_does_not_lex_or_parse_or_binds_two_names_is_refused` | |
| Prelude unit name that is no type, or broken, at a type and at a value | manifest.rs `a_prelude_unit_name_that_is_no_type_stands_where_a_type_is_written`; complete.rs `a_prelude_unit_name_that_is_no_type_or_is_broken_at_a_type` | |
| Structs, fields, type parameters, methods, `this`, match arms, type tests, tuple parameters | binders.rs (9 tests) | |
| Later forms (reductions, display, ranges, sort keys, `for`) | later_forms.rs (4 tests) | |
| Later words and types | later_words.rs (5 tests) | |
| Corpus words | corpus_words.rs (5 tests) | |
| The command on a package | command.rs (4 tests) | |
| Queries: an edit keeping exports; an unchanged unit | queries.rs (2 tests) | |
| Manifest build options, `package_build` | l02_08d_build_constant command.rs, staged.rs, reads.rs | |
| Pins: `pin_units`, `write_pins`, `pinned`, too large | l02_08_import_pinning pin_file.rs, command.rs, prelude.rs | |
| `query.rs` `set_build`, `row`, `front_at` | l02_08d_build_constant, l01_28_staging | Used by build and staging |
| `unit.rs` `read_sources` on a file name not UTF-8 or a directory entry that fails | none | Needs a file system that returns such names or errors; the error path is one `map_err` |
