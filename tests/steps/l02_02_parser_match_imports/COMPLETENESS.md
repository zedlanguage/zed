# L2.2 completeness: `match`, imports, annotations

Code under test: the building of `match` with its patterns and guards, the three forms of
import with pins, and annotations (`crates/zedc-syntax/src/ast/stmts.rs`, `builder.rs`,
`mod.rs`), and their formatting (`format.rs`), over the rules `Match`, `Arm`, `Pattern`,
`AtomPattern`, `FieldPat`, `SignedLit`, `Import`, `Pin`, `Annotation` (DESIGN.md sec:grammar,
step L2.2). Every alternative of these rules also has a case in l01_08 `grammar_cases.rs`.

Coverage: the code of this group is shared with the other groups of this row; its share of the
figures is reported in l01_12 and l02_01. No uncovered line was found that belongs to these
forms alone.

| Case | Covering test, or the reason none is needed |
|---|---|
| A tree sum matched on atoms and structs | `matches::a_tree_sum_matches_on_atoms_and_structs` |
| Guards and literal patterns | `matches::guards_and_literals` |
| Nested and typed patterns | `matches::nested_and_typed_patterns` |
| A match as an operand | `matches::a_match_is_an_operand`, `formatting::a_match_as_an_operand` |
| Malformed matches | `matches::malformed_matches_are_syntax_errors` |
| The three forms of import; a pin after the path; a malformed pin, with its fault; malformed imports | `imports::*` (4 tests) |
| Annotations before declarations and on operands; malformed annotations | `annotations::*` (3 tests) |
| Forms and annotations of later layers name their step | `later::*` (2 tests) |
| Formatting: arms one to a line, nesting, imports and annotations | `formatting::*` (4 tests) |
| Large inputs | Benchmarks `bench::*`; `scaling::each_form_is_built_formatted_and_refused_at_small_sizes` |
