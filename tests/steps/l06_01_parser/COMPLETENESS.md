# L6.1 completeness: the parser of layer L6

Code under test: the building of `loop` with primes and step names, `with` boundaries,
`initial x = e;` and `initial x = e with carryForward;`, the guards `while` and `until`,
`break`, indexed definitions, generation pushes `x' <- e`, expression statements and the call
`*.` (`crates/zedc-syntax/src/ast/initial.rs`, `sentinel.rs`, `drop.rs`, `stmts.rs`), with the
rows "`initial` outside a loop", "A loop variable not updated on every path of a step",
"Collision" and the others of sec:generations, and their formatting (DESIGN.md sec:grammar,
sec:generations, step L6.1).

Coverage (llvm-cov, regions, before and after this pass, measured before `path_parts.rs` was
added): `ast/initial.rs` 89.4% to 92.7%, `sentinel.rs` 98.8%, `drop.rs` 92.9%. What is left in
`initial.rs`, read from the code and not proved unreachable:

- the arms of `stmt_kids` and `walk` for statements that do not stand in a loop's body at this
  zedc (a method, a struct, a `type`, an import, a unit annotation), which are refused or do
  not parse there;
- `unreachable!` arms (lines 1330, 2011, 2679, 2728, 2749, 3259, 3487);
- some branches of the repair texts (`fresh`, `drop_name`, `narrowed`, `first_key`) for
  combinations no test has reached yet.

The parts of an expression whose update counts on every path (a map display, a record display,
a `with` update, a string hole, `is`) and the `else` default with a payload pattern, and an
`initial` statement in a nested block, were among the lines left and now have tests in
`path_parts.rs`.

| Case | Covering test, or the reason none is needed |
|---|---|
| Each form builds and formats: loops with and without a step name, `break`, spread calls, indexed definitions with keys and boundary, pushes, expression statements, primes | `forms::*` (7 tests), `formatting::*` (4 tests) |
| A keyed push stays refused | `forms::a_keyed_push_stays_refused` |
| Corners: a step name read by a nested loop's `break`, `with` sentinels, primes on a receiver and a field, `while` and `until` together, an indexed definition with no key, spread on a call result, an expression statement that writes no generation | `corners::*` (8 tests) |
| `initial`: every form, any place in the body, reserved word, `with` only on an indexed definition, bare and `with initial` items, outside a loop, for a name not updated, every form of update, a value that reads the loop, two sentinels, entries given twice, entries inside a frame | `initial::*` (17 tests) |
| `initial` in a block nested inside the loop's body | `path_parts::an_initial_statement_in_a_block_inside_the_loop_body_is_refused` |
| A read of the step index in every kind of expression; a name the value binds and reads in its own scope | `initial_reads::*` (2 tests) |
| A read of the loop's name outside a binder's scope, in a value that binds the same name elsewhere | FAIL-initial-reads-shadowed (plan row, priority 0; test copy in `wt/failing-tests/FAIL-initial-reads-shadowed.rs`), not merged while it fails |
| `with carryForward`: every construct with paths, every path that updates or breaks, nested blocks, entries, fields, qualified names, several writers, `mutable` refused, other words after `with`, keyed entries, the two repairs, `*.` calls | `carry_forward::*` (28 tests) |
| An update in a part run on every path: a map display key and value, a record display field, a `with` update, a string hole, the operand of `is` | `path_parts::an_update_in_a_part_run_on_every_path_counts` |
| An update in the default of an `else` with an atom pattern, with no payload, a positional payload and a named one | `path_parts::an_update_in_the_default_of_an_else_with_an_atom_pattern_is_on_some_paths` |
| Edges of the `with` clause: keys below the domain, a domain with no low edge, keyed items of another variable, a name given twice in a loop, `initial` after annotations or with a key, local `mutable` outside a loop, a `mutable` repair that does not parse, `mutable` inside a statement | `clause_edges::*` (8 tests) |
| A `with` clause in a test case: each place it is refused and each repair | `test_case::*` (14 tests) |
| Forms of later layers name their step; declared names bound and refused once | `later::*` (2 tests) |
| Large inputs | Benchmarks; `scaling::each_form_is_built_formatted_and_refused_at_small_sizes`, the `*_at_small_sizes` tests of `carry_forward` and `initial` |
