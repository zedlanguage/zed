# L1.11 completeness: statements

Code under test: the building of blocks and their statements (`crates/zedc-syntax/src/ast/
stmts.rs`, `body.rs`), over the rules `Block`, `Body`, `Binding`, `PlainBinding`, `Target`,
`Return` (DESIGN.md sec:grammar, step L1.11).

Coverage (llvm-cov, regions, before and after this pass): `ast/stmts.rs` 75.6% to 77.2%,
`ast/body.rs` 82.0% to 97.6%. What is left in `stmts.rs` is `unreachable!` arms that name the
grammar's only forms, and the `main`, `handles` and `test with` port errors, tested with
the steps that give them (l01_19_whole_file_ports, l01_19a_command_line, l01_21_test_runner).

| Case | Covering test, or the reason none is needed |
|---|---|
| Each alternative of each statement rule parses to its node | `l01_08_parser::alternatives::*` |
| Bindings and the trailing expression | `blocks::bindings_and_the_trailing_expression` |
| The `;` rule: every statement but the trailing expression ends in `;` | `blocks::the_semicolon_rule` |
| A block exports exactly once | `blocks::a_block_exports_exactly_once` |
| A statement of a later layer is refused as not compiled yet | `blocks::a_statement_of_a_later_layer_is_refused_as_not_compiled_yet` |
| A wildcard target binds nothing | `blocks::a_wildcard_target_binds_nothing` |
| `return` with a value or a comma list | `returns::return_forms` |
| The empty family `{}` outside and inside body position; an empty block in body position | `empty_family::*` (4 tests) |
| A brace after an arm's `->` is a block whatever it holds | `empty_family::a_brace_after_an_arm_arrow_is_a_block_whatever_it_holds` |
| A display in each body position, with each repair | `l02_01_parser_structs::body_positions::*` |
| Each block in expression position in DESIGN.md's fences builds or names its step | `fences::every_block_in_expression_position_builds_or_names_its_step` |
| Long blocks and nested blocks | Benchmarks `bench::*`; `scaling::each_benchmark_text_builds_its_tree_at_small_sizes` |
