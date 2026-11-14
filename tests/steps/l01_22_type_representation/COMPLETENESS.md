# Completeness: type representation (L1.22)

Row TEST-complete-types (author P189). The code under test is `zedc_types::kernel_type`
(`crates/zedc-types/src/kernel_type.rs`), which gives the kernel type a written type denotes for
the bounds check and for `is`; `zedc::check::declared_text`, which prints it; the elaboration
of `e is T`; and the kernel's type algebra in `crates/zed-kernel/src/types/` (connectives,
printing, the order of union members, the node tables). Expected results are from DESIGN.md
step L1.22, sec:type_language and sec:diagnostics ("Types in a message"). The new tests are in
`complete.rs`. llvm-cov, as a floor, over the tests of l01_22, l01_23, `deep_types`,
`deep_search` and the unit tests of zedc-types, benchmarks left out (regions; branch counts
need a nightly compiler, so regions stand in for branches): `kernel_type.rs` 70.05% before,
96.77% after (lines 77.69% to 98.46%); `ty.rs` 87.83% to 87.86%; `print.rs` 93.48% to 93.52%.
The lines no test reaches, with those of l01_24 to l01_29 and the kernel's unit tests merged,
are listed per function in `/home/luke/Work/wt/coverage/TEST-types-unreached-paths.txt`; the
ones in this group's code are in the last rows of the table, and the rest are row
TEST-types-unreached-paths. The cases of `ty.rs` are in `crates/zedc-types/COMPLETENESS.md`.
Row TEST-types-unreached-paths, with l01_24 to l01_29 merged in: `kernel_type.rs` 96.77% to
99.08% of 217 regions (7 unreached to 2), by
`is_rejects_a_port_in_an_intersection_a_difference_and_a_bound`; the 2 left are the
`unreachable!` arms, which no source reaches (the reason is in the table).

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| A base type name: `int`, `rat`, `f64`, `f32`, `bool`, `String`, `Never` | `complete.rs` `the_connectives_and_the_extremes_denote_sets`; `forms.rs` `the_extremes_and_the_base_types` | |
| `()` (the empty tuple) and `(int,)` (a one-tuple) | `complete.rs` `the_connectives_and_the_extremes_denote_sets`; `is.rs` `a_one_tuple_and_a_morphism_type_with_two_bounds_elaborate` | |
| `#_`, `(..)`, `{..}`, `#a(..)`, and `#a(..)` in a union | `complete.rs` `the_connectives_and_the_extremes_denote_sets`, `an_atom_with_every_payload_denotes_itself`; `kinds.rs` | |
| Union, intersection and difference; an empty meet and a difference of a type with itself are `Never`; tuple types of one length are not met when built | `complete.rs` `the_connectives_and_the_extremes_denote_sets`; `laws.rs` (random expressions against membership) | |
| Complement within each universe | `forms.rs` `complement_is_taken_within_each_universe`; `laws.rs` `a_type_and_its_complement_split_every_universe` | |
| A function type is curried one level per parameter; `->?` partial at every level; `() -> V` has `()` as its one key; a pair parameter is one level; a partial level whose result is an exact function | `complete.rs` `function_types_are_curried_and_partial_at_each_level`; `is.rs` `function_types_are_curried_one_level_per_parameter` | |
| `L .. U -> V`: a guarantee within the permission, a guarantee of `Never`, equal bounds | `complete.rs` `bounded_function_types_keep_both_bounds`; `forms.rs` `morphism_types_carry_two_domain_bounds` | |
| A guarantee outside its permission (error); the check refused (the "could not decide" error) | `complete.rs` `a_bounds_error_and_a_port_error_both_stand_in_written_order`; `is.rs`; `../l01_23_subtyping/bound_paths.rs`, `../l01_23_subtyping/refusals.rs` | |
| A port name (`Lines`, `Files`) alone, in a tuple, in a union, as a function result, after `is not` | `complete.rs` `a_port_name_denotes_no_type_wherever_it_stands`, `is_rejects_a_port_in_every_position_in_written_order`; `is.rs` | |
| A port name in an intersection, on either side of a difference, in either bound of `L .. U -> V`: the whole type denotes none (each `?` of `kernel_form` on a refused part, lines 107, 110, 127), each port named once in written order and no bounds error beside it | `complete.rs` `is_rejects_a_port_in_an_intersection_a_difference_and_a_bound` (row TEST-types-unreached-paths) | |
| Two errors in one type: in written order | `complete.rs` `is_rejects_a_port_in_every_position_in_written_order`, `a_bounds_error_and_a_port_error_both_stand_in_written_order` | |
| `is` on a type that admits some functions and not others: a function type, in a tuple, `() -> V`, after `is not`, a bounded function type | `complete.rs` `is_rejects_a_type_with_some_functions_in_every_position`; `is.rs` | |
| `is` on a bounded type `T for X in …`: one variable, two, inside a tuple component; it denotes no type | `complete.rs` `is_rejects_a_bounded_function_type_naming_its_variables` | |
| `is` on a type that admits every function or none: a function type less itself, `int & rat`, `Never`, `#_`, `(..)`, `()` | `complete.rs` `is_accepts_a_type_with_every_function_or_none` | |
| `is` and `is not` elaborate to a match on the type | `is.rs` `is_is_a_match_on_the_type` | |
| Printed forms: universes, finite and cofinite scalar sets, tuples, atoms, morphism bounds | `forms.rs`; `surface.rs` (each read back as the same type) | |
| The order of union members: numbers by value, two literals of one value by carrier (`f32`, `f64`, `rat`), however the union was built | `complete.rs` `literals_of_one_value_print_by_their_carrier`; `kinds.rs`, `surface.rs` | |
| `rat` literals: one type for equal values, the canonical text, large exponents | `rat_literals.rs` | |
| Deep types built, compared, printed and released on a small stack | `deep_types.rs` (its own binary) | |
| Node tables keep a node only while it is held, on one thread and two | `table_life.rs` | |
| Types of `n` parts at the rule of low complexity | `scaling.rs` (benchmarks run apart) | |
| `kernel_form` on `Apply`, `AtomApply`, `Record`, `Array` (lines 52-58) | | `unreachable!`, kept as a soundness guard: name resolution records each of these as a form a later step compiles and fails, and the checker and the `is` elaboration run only on a unit that resolved (`../l01_26_type_resolution`; the full reason is in `crates/zedc-types/COMPLETENESS.md`). Only a test calling `declared_text` on an unresolved type reaches them |
| `order::of_value` and `cmp_values` (print/order.rs 156-169) | | Called only by the checker's message for a cast every value of whose operand fails, when two values give two atoms (`check/walk.rs`); no measured test has two. Row TEST-types-unreached-paths |
| `hash::mix` with `address::SHORT` (hash.rs 9) | | The feature `short-addresses`, off in this build; `../l01_37a_short_addresses` runs with it on |
