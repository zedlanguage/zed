# Completeness of the L22.8 tests (vacuity and the trivial-model report)

Author P189, 2026-11-14, row TEST-complete-misc. Code under test: the prototype of the
trivial-model report in `trivial.rs` (DESIGN.md sec:theories, item 3), checked against the brute
force of `brute.rs`. The vacuity warning of item 2 is not implemented: plan row L22.8 (needs
L22.2) builds it, and its tests come with it. A test named `file::name` is in this directory.

Coverage by llvm-cov over the correctness tests of this group (benchmarks left out), before and
after this pass: `trivial.rs` lines 97.19% → 99.73% (72 → 7 lines not reached), regions
97.70% → 99.57%, functions 98.56% → 99.52%. Each line still not reached is listed below with its
reason.

| Case | Test that covers it | Or the reason none is needed |
|---|---|---|
| A law that names no field, each form: `==`, `!=`, `!`, `&&`, `\|\|`, `.implies`, parentheses, `&&` tighter than `\|\|`, an implies chain read from the left | `cases::each_form_of_a_law_is_read_as_written` | |
| A law over fields, each form, with model counts by hand; `!x.implies(y)` is `!(x.implies(y))` (DESIGN sec:lexical, expression ladder row 3) and `(!x).implies(y)` differs | `cases::each_form_of_a_law_over_fields_is_read_as_written`, `brute::laws_with_not_and_implies_agree_with_brute_force` | |
| Binders written `a b` and `a, b`; a field of arity 0, 1 and 2; a field applied to a field | `cases::each_form_of_a_law_over_fields_is_read_as_written`, `corpus::*` | |
| The model on one value: holds, or the first law that fails is named | `cases::the_model_on_one_value_names_the_first_law_that_fails`, `corpus::comm_ring_lists_the_one_element_ring` | |
| Each choice of a field (`#a`, `#b`, each argument) written as a function | `cases::each_choice_of_a_field_is_written_as_a_function` | |
| Fields grouped by the laws that name them; a field no law names is free, singular and plural | `cases::fields_are_grouped_by_the_laws_that_name_them`, `corpus::twenty_fields_with_no_law_are_free` | |
| The count of models printed as a product over groups | `cases::the_count_is_printed_as_a_product` | |
| A group with no model, one model, several models | `cases::each_group_prints_no_model_one_model_or_several`, `hardness::nae_fano_has_no_model` | |
| A law that names no field and fails: no model for any group, its render line | `cases::a_law_that_names_no_field_decides_for_every_group` | |
| A closed law fails: no "models on two values" line is printed | | DESIGN does not say whether this line is printed then; no test pins either form. |
| Exhaustive mode: the count of choices and of wrong turns | `cases::the_exhaustive_report_counts_its_wrong_turns`, `hardness::dead_ends_grow_exponentially_on_pigeonholes`, `hardness::dead_ends_on_random_3_cnf` | |
| Default mode stops at the first choice that leads to no model, after it found a model: "not decided", the chain of laws, the menu (DESIGN sec:theories item 3) | | Fails: plan row FAIL-trivial-stop-after-model, test in /home/luke/Work/wt/failing-tests/FAIL-trivial-stop-after-model.rs. The report prints "at least 1 model(s), for example" with the model where DESIGN says "not decided". |
| Default mode stops before any model: "not decided", the chain, the menu | `hardness::nae_fano_has_no_model` (the report DESIGN prints for Fano) | |
| The forest fragment: atoms, `!` atoms, conjunctions, a field named twice in an atom; not an `\|\|`, not a cycle | `cases::the_forest_fragment_is_atoms_and_conjunctions_without_a_cycle`, `corpus::the_corpus_agrees_with_brute_force_and_has_no_dead_ends` | |
| An `\|\|` of `&&`s is refused ("not decided, since law … is not checked"); a short `\|\|` with a few `&&`s is joined | `hardness::an_or_of_ands_is_refused`, `hardness::a_short_or_and_a_few_ands_are_joined_without_refusal` | |
| A field held to several choices is tested again on the other side of a shared atom; the size of a shared atom, and none for an atom that is not shared | `cases::a_field_held_to_several_choices_is_tested_again_on_the_other_side`, `scaling::the_shared_field_atoms_take_the_steps_of_their_formulas` | |
| A law with an unknown character, or a missing operand, is not read | `cases::a_law_with_an_unknown_character_is_not_read`, `cases::a_law_with_a_missing_operand_is_not_read` | |
| Random theories agree with brute force | `brute::the_report_agrees_with_brute_force_on_random_theories`, `scaling::the_picks_agree_with_brute_force`, `scaling::the_frontier_agrees_with_brute_force` | |
| The corpus theories (codec, `CommRing`) | `corpus::codec_with_no_size_law_lists_the_identity`, `corpus::comm_ring_lists_the_one_element_ring` | |
| The steps each family takes, at small sizes | `scaling::*`; the benchmarks in `bench.rs` | |
| The vacuity warning (item 2): a law no model of two values satisfies is warned at | | Not implemented: plan row L22.8. |
| `trivial.rs` lines 504, 761, 3272 (`unreachable!`) | | Internal consistency checks; no theory reaches them. |
| `trivial.rs` line 1676, a field node whose every child is dead | | Inferred not reachable: every field node has the leaves `#a` and `#b`, which are never dead. |
| `trivial.rs` line 2057, a cube of `CubeSet::Listed` | | Dead code: `Listed` is only built empty (lines 2598, 2609, 2641). |
| `trivial.rs` line 1243, a second class of one node whose joint key is already present | | Open: not reached by any theory tried (the random theories of `brute.rs` included); inferred to need two classes with the same list of children. |
