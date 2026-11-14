# L1.12 completeness: declarations

Code under test: the building of declarations (`crates/zedc-syntax/src/ast/stmts.rs`,
`builder.rs`), over the rules `Unit`, `Item`, `Decl`, `Function`, `Result`, `Params`, `Param`,
`TestTable`, `TestCase`, `Push`, `PushTarget`, `WholePush`, `If` (DESIGN.md sec:grammar, step
L1.12).

Coverage (llvm-cov, regions, before and after this pass): `ast/stmts.rs` 75.6% to 77.2%,
`ast/builder.rs` 86.0% to 86.2%. What is left is `unreachable!` arms and the ports of `main`
(reads of `m.stdout`, `m.signals`, a field `MainArgs` lacks, pushes to inputs and to views of a
port), tested with their steps in l01_19_whole_file_ports, l01_19a_command_line and
l01_21_test_runner.

| Case | Covering test, or the reason none is needed |
|---|---|
| Each alternative of each declaration rule parses to its node | `l01_08_parser::alternatives::*` |
| An equation function is its expression; a block function is its block | `functions::an_equation_function_is_its_expression`, `functions::a_block_function_is_its_block` |
| `main` takes its argument and pushes to its fields | `functions::main_takes_its_argument_and_pushes_to_its_fields` |
| A test table lists input and expected in order | `functions::a_test_table_lists_input_and_expected_in_order` |
| A function inside a block is a statement | `functions::a_function_inside_a_block_is_a_statement` |
| The unit's top level exports nothing; block bodies still export once | `functions::the_unit_top_level_exports_nothing_and_block_bodies_still_export_once` |
| A form of a later layer is refused as not compiled yet | `functions::a_form_of_a_later_layer_is_refused_as_not_compiled_yet` |
| `if` takes both branches; `else if` nests on the right; every branch block exports | `ifs::*` |
| A push sends the whole value to its port | `pushes::a_push_sends_the_whole_value_to_its_port` |
| A display after a signature is a block | `l02_01_parser_structs::body_positions::each_form_whose_brace_is_a_block_is_named` |
| A test clause (`with`) in a test case | `l06_01_parser::test_case::*` |
| Every unit in DESIGN.md's fences builds or names its layer | `fences::every_unit_builds_or_names_its_layer` |
| Many functions, long test tables, deep nesting, long `else if` chains | Benchmarks `bench::*`; `scaling::*` at small sizes |
| A `test with` clause prints the rows it gives to and each port with its value, in the order written | `given::a_test_with_clause_prints_its_rows_and_ports` (what the clause means: l01_21_test_runner/ports.rs) |
