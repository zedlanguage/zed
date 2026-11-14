# l01_35_mlir_study: completeness (step L1.35, the MLIR study)

The code under test is the study's record, `zed/compiler/MLIR.md`, checked against the compiler:
its Operations and Region kinds tables against the variants of `zir/mod.rs` (the reader in
`mod.rs`), and its Layout section against the sizes and node counts of `tests/src/layout.rs`.
Each row is a case; the second column names the test that covers it, or says why no test is
needed.

| Case | Covering test, or reason none is needed |
|---|---|
| **The Operations and Region kinds tables** | |
| every `Op` variant has a row, and every row an operation | `every_operation_has_a_lowering` |
| every `RegionKind` variant has a row, and every row a kind | `every_region_kind_has_a_form` |
| the port operations and the derived nodes, the two exceptions to the naming rule | `the_ports_and_the_derived_nodes_have_their_own_rows` |
| a variant name of one letter, of several words, empty | `a_variant_of_several_words_keeps_its_inner_capitals` |
| **The variant reader** | |
| struct and tuple variants, doc comments, attributes, nested brackets, a second enum | `the_reader_takes_struct_and_tuple_variants_comments_and_attributes` |
| one, two and nine struct variants | `the_reader_finds_each_of_a_few_struct_variants` |
| an enum that is missing, or has no closing brace | none: the reader panics with the enum's name, and the only callers pass `Op`, `Derived` and `RegionKind` of the real source, which the two table tests read |
| **The Layout section** | |
| each inline size the record names equals the compiler's | `layout::the_record_names_each_inline_size_as_the_compiler_has_it` |
| each step unit measured, each node at least its inline size | `layout::the_step_units_are_measured_and_each_node_takes_at_least_its_inline_size` |
| an empty struct and a six-field struct | `layout::an_empty_struct_and_a_six_field_struct_are_measured` |
| an empty node and a six-field node | `layout::an_empty_node_and_a_six_field_node_are_measured` |
| a table clause, on a function and on a method | `layout::the_value_a_tables_clause_gives_is_a_node_of_a_function_and_of_a_method` |
| a unit of a few definitions | `layout::the_record_of_a_unit_of_a_few_definitions_is_made` |
| **Syntax-tree node counts, by kind** | `layout::each_kind_of_expression_and_statement_is_counted_once`, 41 rows, each count worked out by hand |
| ranges (below, through, open) | the table: 3 rows |
| `for`, with and without `where` | the table: 2 rows |
| `match`, with and without an arm guard; patterns not counted | the table: 2 rows |
| record (with `y:`), update `with`, map, empty map, set, array, index, `else`, tuple | the table: 9 rows |
| `in`, `><` with a section, `::`, member, `*.`, sort keys, a lambda argument, a lambda called, unary, `is` (type not counted), string hole, `this` | the table: 12 rows |
| `loop` with `until`, `while`, `local`, `initial`, a named loop with `break` | the table: 4 rows |
| indexed definition, annotations (bare, with arguments, of the unit), local function, parameter default, method, struct field default, block body with `<-` and `return` of two, a table row, two statements | the table: 11 rows |
| **Kernel term counts** | |
| the terms of the step units | `layout::the_step_units_are_measured_and_each_node_takes_at_least_its_inline_size` |
| a discard, a family, a fixed point, a reindex, a generator, a fold | none at this step: these terms come only from `for`, `loop`, indexed definitions and `><`, which zedc refuses at L1 ("is part of the Zed language, and this version of zedc does not compile it yet"), so no unit reaches the term stage with one; they join when those forms compile |
| **Scaling** | the reader's time in `bench` (linear in the source); not a correctness test (P178) |
