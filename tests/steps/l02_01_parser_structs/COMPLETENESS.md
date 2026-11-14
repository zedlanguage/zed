# L2.1 completeness: structs, methods, displays, `with`

Code under test: the building of structs, methods, record displays and `with` updates
(`crates/zedc-syntax/src/ast/stmts.rs`, `builder.rs`, `mod.rs`), the row "Display in body
position" (`ast/body.rs`) and their formatting (`format.rs`), over the rules `Struct`, `Field`,
`Method`, `TypeDecl`, `RecordDisplay`, `Update`, `KeyPath` and the `with` suffix (DESIGN.md
sec:grammar and sec:diagnostics, step L2.1).

Coverage (llvm-cov, regions, before and after this pass): `ast/body.rs` 82.0% to 97.6%. What is
left in `body.rs`: line 161 (a map entry named as the part that reads as a display) now has a
test, added after the measurement; lines 210 and 222 (a brace with no parent, or under a rule
not listed) are reached by no grammatical input, since every brace the row fires on is the
body of one of the listed forms; line 221 (`proof`) is unreachable at this zedc, which refuses
a `law` as a later form before its body is read.

| Case | Covering test, or the reason none is needed |
|---|---|
| A struct with typed fields, defaults, import fields, any field type of layer 2 | `structs::*` (8 tests) |
| A field declared twice; a path imported twice, however spaced | `structs::a_field_declared_twice_is_an_error`, `a_path_imported_twice_is_kept_once_however_it_is_spaced` |
| `grammar struct` and a struct `law` member are of a later layer | `structs::a_grammar_struct_is_of_a_later_layer`, `a_struct_law_member_is_of_a_later_layer` |
| Type declarations: unions, recursive unions, record and applied types, names declared twice | `types::*` (4 tests) |
| Methods on a receiver type, a block body with tests, `this` | `methods::*` (3 tests) |
| `with` updates: nesting, chaining, suffixes after the braces, the arithmetic to its left, a path updated twice, keyed paths of layer 5 | `updates::*` (6 tests) |
| Record displays, blocks, sets and maps, a display field given twice | `blocks::*` (6 tests) |
| Bare name values, `and` and `else` chains | `name_values::*` (5 tests) |
| A payload destructured by field name, a tuple parameter | `patterns::*` |
| A display in body position at each form whose brace is a block: a signature, the head and the `else` of an `if`, a fallback's `else`, a lambda's `->`, a match arm's `->`, the head of a `for`, `loop` | `body_positions::each_form_whose_brace_is_a_block_is_named` |
| Each kind of display (set of one, set of several, record, map) with its repair | `body_positions::each_kind_of_display_gets_its_repair` |
| The part that reads as a display: a top-level comma, a record field, a map entry | `body_positions::the_part_that_reads_as_a_display_is_named` |
| `proof` as a body position | None at this zedc: a `law` is refused as a later form before its body is read |
| Formatting of each form | `formatting::*` (7 tests) |
| Forms of later layers name their step | `later::each_form_names_the_step_that_compiles_it` |
| Large inputs | Benchmarks `bench::*`; `scaling::*` at small sizes |
