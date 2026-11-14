# L1.10 completeness: lambdas, `is` tests and types, `else`, tuples

Code under test: the building of lambdas, `is` / `is not` with their type expressions, `else`
with its atom-pattern form and tuples (`crates/zedc-syntax/src/ast/mod.rs`, `types.rs`), over
the rules `Lambda`, `ArrowParams`, `IsTest`, `ElseTail`, `TupleExpr`, `Type` to `TypePrimary`,
`TupleType`, `TypeParam`, `TypeBounds` (DESIGN.md sec:grammar, step L1.10).

Coverage (llvm-cov, regions, before and after this pass, measured before the refinement and
literal tests were added): `ast/types.rs` 91.5% to 94.3%, `ast/mod.rs` 94.4% to 94.5%,
`ast/show.rs` 96.9% to 98.2%. What is left is `unreachable!` arms naming the grammar's only
forms, and `types.rs` lines 332 and 333 (a pattern node that built to no pattern), which the
builder reaches, as read from the code, only for a node of a later layer already refused; no
input was found that reaches them. Line 56, a chain of refinements, has a test below.

| Case | Covering test, or the reason none is needed |
|---|---|
| Each alternative of each lambda, type and tuple rule parses to its node | `l01_08_parser::alternatives::*` |
| Lambda parameters: a name or a list | `lambdas::parameters_are_a_name_or_a_list` |
| A brace after a lambda's `->` is a block | `lambdas::a_brace_after_the_arrow_is_a_block`; the display in that position, `l02_01_parser_structs::body_positions::*` |
| A tuple parameter is destructured from layer 2 | `lambdas::a_tuple_parameter_is_destructured_from_layer_2` |
| `else` and its atom-pattern form | `elses::else_and_its_atom_pattern_form` |
| `else` in a head | `l01_08_parser::heads::*` |
| `is` is a relation; type connectives `&`, `|`, `-`, `!`; function types one level per parameter; a one-tuple type and a morphism type with two bounds | `tests_of_types::*` (4 tests) |
| Type forms of later layers | `later_types::*` (desugaring rules read from the spec; every-value type and named types not compiled yet) |
| A chain of refinements (`TypePostfix`, L10) is refused at its first suffix | `later_types::a_chain_of_refinements_is_refused_at_its_first` |
| A trailing comma makes a one-tuple; it evaluates, matches as a pattern and prints back | `one_tuples::*` (6 tests) |
| The empty tuple and a parenthesized pattern are refused | `one_tuples::an_empty_tuple_and_a_parenthesized_pattern_are_rejected` |
| Tuples | `tuples::tuples` |
| Each expression in DESIGN.md's fences builds or names its step | `fences::every_expression_in_the_fences_builds_or_names_its_step` |
| Deep nesting of patterns and lambdas | Benchmark; `scaling::the_text_of_nested_patterns_and_lambdas_is_written_at_small_depths` checks the text at small depths |
| A literal prints with its radix prefix (`0b`, `0o`, `0x`) and the format its suffix forces (`f32`, `f64`, none) | `literals::a_literal_prints_with_its_radix_and_its_forced_format` |
