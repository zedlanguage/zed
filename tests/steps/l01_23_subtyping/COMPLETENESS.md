# Completeness: semantic subtyping (L1.23)

Row TEST-complete-types (author P189). The code under test is the kernel's emptiness and
subtyping check in `crates/zed-kernel/src/types/` (`types.rs`, `empty.rs` and `empty/`, `bdd.rs`
and `bdd/`, `rec/`, `bes.rs`, the decider of recursive groups) and the checker's type `Ty` in
`crates/zedc-types/src/ty.rs` (its cases are in `crates/zedc-types/COMPLETENESS.md`). Expected
results are from DESIGN.md L1.23 and sec:type_language, and, for the group decider, from the
Büchi game reference in `bes_families.rs`, which reads the same equations. The new tests are in
`complete.rs`. llvm-cov, as a floor, over the tests of l01_22, l01_23, `deep_types`,
`deep_search` and the unit tests of zedc-types, benchmarks left out (regions; branch counts
need a nightly compiler, so regions stand in for branches): `bes.rs` 94.39% before, 94.85%
after (lines 93.21% to 93.47%); `empty.rs` 95.45% to 95.54%; `empty/sweep.rs` 97.38% to 97.80%;
`types.rs` 95.84% to 95.85%. The lines no test reaches, with l01_24 to l01_29 and the kernel's
unit tests merged in, are listed per function in
`/home/luke/Work/wt/coverage/TEST-types-unreached-paths.txt` and are row
TEST-types-unreached-paths, except those given a reason below.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| The spec's subtyping examples; identities decided as equality both ways | `cases.rs` | |
| Emptiness and subtyping against an exact oracle: scalar leaves, universes, tuples of length 1 and 2 | `oracle.rs` | |
| Lists of periodic lengths, alone or with an integer, each inhabited verdict shown by a value | `witnesses.rs` | |
| The cell table of a product less a union of tuple types (exhaustive tuple `match`) | `cells.rs` | |
| Tuple parts open on one component, decided in one pass | `one_pass.rs` | |
| 2-CNF tuple parts over two-valued components | `two_sat.rs` | |
| The meet of boxes with an unbounded column | `meet_join_oracle.rs` | |
| Refusals: each cause, a value sought before any refusal | `refusals.rs`, `refusal_cost.rs` | |
| Finite listing of a type's values | `listing.rs` | |
| Recursive definitions: accepted, rejected, emptiness and subtyping coinductively | `rec.rs`, `judgments.rs` | |
| Admission of a group (monotone in emptiness), named groups and a random sweep | `admission.rs`, `admission_sweep.rs` | |
| Equal domain bounds of a morphism in a group | `bound_sameness.rs` | |
| The bound check `L .. U -> V` once per written type, wherever written | `bound_paths.rs` | |
| Members under `&` and `\` | `setop.rs` | |
| The digest and order of a recursive type independent of what was built before | `rec_order.rs` | |
| The front sweep against an oracle | `sweep_agreement.rs` | |
| The R6 selector reduction | `r6_reduction.rs` | |
| Decider step 1: edges no least fixed point uses (an `And` child that is its `And` parent, a self loop) | `bes.rs` (the X14 families), `group_oracle.rs` | |
| Step 2: a component with no tuple cycle (greatest fixed point), one with no `Mor` edge (least) | `bes.rs`, `group_oracle.rs`, `judgments.rs` | |
| Step 3: lower and upper bounds; nodes where they agree | `bes.rs`, `group_oracle.rs` | |
| Step 4: a component of the undecided nodes with one `Mor` edge (two least fixed points) | `bes.rs`, `group_oracle.rs` | |
| Step 4: a component of the undecided nodes with no tuple cycle left, settled by one fixed point | `complete.rs` `an_undecided_component_without_a_tuple_cycle_is_settled_by_one_fixed_point` | |
| Step 4: the deletion cascade entered | `bes.rs`, `group_oracle.rs` | |
| Step 4: a node killed in the cascade (`delete_cascade`): a tuple cycle killed at the cascade's start for want of a seed, and one killed when the death of a node removes its one seed | `bes.rs` `a_cycle_left_without_a_seed_is_killed_by_the_cascade` | |
| Step 4: a node dead at the cascade's start by its own rule (bes.rs 674-675) | | Unreachable while kept: the cascade's nodes are those with `lo != hi` (bes.rs `decide`, the `u_set` filter), so `hi` is true at each, and `hi` is the last greatest fixed point of `bounds`, so each node's rule holds under it: an `And` or `Mor` node has no child outside the set with `hi` false, an `Or` node has a child with `hi` true. Kept as a guard: the loop that sets the counters must handle a count of 0 |
| Finite listing of a type of tuples recursive through two definitions (`Filer::file`, the component of more than one definition) | `listing.rs` `a_tuple_type_of_types_recursive_through_each_other_is_taken_out` | |
| Finite listing of a negated union with no choice left (`part_boxes`) | `listing.rs` `a_negated_union_with_no_choice_lists_its_values` | |
| The atoms a recursive type names (`atom_names`); the `Debug` text of a group's trees | `rec.rs` `a_recursive_type_names_its_atoms`, `a_group_writes_its_trees_for_debugging` | |
| Step 5: a refused component, and the nodes that depend on it | `group_refusal.rs`, `cycle_dup.rs` | |
| The answers do not depend on how nodes are numbered | `bes.rs` | |
| A system with no node; a single `Top` node | `complete.rs` `a_system_with_no_node_has_no_answer` | |
| `Top` and `Bot` arms in `lfp`, `gfp`, `delete_cascade` and `refusal` (bes.rs 390-391, 473, 521, 648, 657-658, 781) | | Unreachable: these run over nodes of a component with a cycle, and a `Top` or `Bot` node has no child (`Bes::add` and `Bes::set` assert it), so it is in no such component. `Mor` shares the arms at 473 and 781 and does not reach them either: 781 needs two undecided children and a `Mor` node has one; 473 needs a `Mor` node in the tuple component of its child, and tuple components do not follow a `Mor` edge (bes.rs 286), so only a `Mor` node that is its own child would, which no type builds (inferred, not proved). Kept: each is one arm of a match the compiler requires to name every kind |
| `Stamp::advance` when the stamp reaches `u32::MAX` (bes.rs 245-246) | | Needs 2^32 stamps, an unusual size (P178) for a benchmark, not a test |
| Deep types on a small stack | `deep_rec.rs`, `deep_search.rs` (its own binary) | |
| Scaling: tuple and morphism parts, payload pinwheels, the X13 families | `scaling.rs`, `payload_scaling.rs`, `x13.rs` (benchmarks run apart) | |
