# M0.7 completeness: the canonicalizer

Code under test: `zedc::canon` (crates/zedc-zir/src/canon): `address`, `address_of_body`,
`serialize`, `unit_address`, the binder pass and the single rewrite steps (`binders.rs`), the
domain normal form (`domain.rs`) and the serialization (`serial.rs`), against DESIGN.md step
M0.7. Lines reached by this group's tests (llvm-cov, without the `bench` module):

| File | Before | After |
|---|---|---|
| binders.rs | 81.6% (98 of 533 missed) | 98.7% (7 missed) |
| domain.rs | 86.6% (9 of 67) | 97.0% (2) |
| mod.rs | 90.2% (13 of 132) | 100% |
| serial.rs | 62.2% (145 of 384) | 97.4% (10) |

The lines still not reached are listed at the end of the table, each with its reason.

| Case | Covering test, or the reason none is needed |
|---|---|
| Every form of kernel term (lambda, application, primitive, primitive as a function, `let`, `if`, `match`, family, both reindex kinds, discard, fold with and without identity and at each depth, definedness and lattice `fix`, `gen` with the guard before and after, read, push, literal) has an address of its own | `cases::each_form_of_term_value_and_pattern_has_an_address_of_its_own` |
| Every form of value (bool, int, `i64` boundaries, big integers at ±2^63, kept powers `3^100`, `-3^100`, `3^101`, rationals kept and reduced, float, `f32`, bare atom, atom with empty payload, atom with arguments and named fields, tuple, path, family) has an address of its own | `cases::each_form_of_term_value_and_pattern_has_an_address_of_its_own`, `alpha::literals_are_hashed_by_their_exact_value`, `alpha::one_one_r_and_a_big_get_the_addresses_of_their_values` |
| Every form of pattern (wildcard, bind, literal, atom, tuple, fields, type test) has an address of its own | `cases::each_form_of_term_value_and_pattern_has_an_address_of_its_own` |
| Evidence of each grade, and a fold's or fix's evidence, reaches the address | `cases::each_form_of_term_value_and_pattern_has_an_address_of_its_own` |
| Binder renaming at every binding form: lambda, `let`, pattern bind, family variable, a definedness fix's `this` and key, and a binder inside the fix's step | `cases::each_form_keeps_its_address_when_its_local_names_change`, `alpha::pattern_and_recursion_binders_are_normalized` |
| A lattice fix binds nothing: its `this` and key are not binders (crates/zed-kernel/src/term.rs, `Term::Fix`), so a name read there is free | `cases::each_form_keeps_its_address_when_its_local_names_change` (its step is a lambda over the iterate) |
| A name read under a pattern that does not bind it is free and hashed by name | `cases::each_form_keeps_its_address_when_its_local_names_change` (arms read `b` only where the pattern binds it) |
| Shadowing: a later binder of the same name hides the earlier one | `alpha::shadowing_decides_which_binder_a_name_means` |
| The rename step records the written name and level as a hint facet | `alpha::the_rename_step_records_the_written_name_and_its_place` |
| One pass and single steps agree on every form | `cases::each_form_reaches_one_normal_form_in_one_pass_or_by_single_steps`, `alpha::the_normal_form_is_the_rules_applied_one_step_at_a_time` |
| α-equivalence agrees with an independent test | `alpha::addresses_agree_with_an_independent_alpha_equivalence_test` |
| A dependency change changes its dependents; a local rename does not | `alpha::a_dependency_change_changes_its_dependents_but_a_local_rename_does_not`, `alpha::an_invoice_total_has_one_address_whatever_its_line_is_called` |
| Facets in any order and repeated give one address; hints dropped | `rules::facets_in_any_order_and_repeated_give_one_address` |
| Each rule lowers its rank and no later rule raises an earlier one; the facet rank | `rules::every_rule_decreases_its_rank_and_no_later_rule_raises_an_earlier_one`, `rules::the_facet_rank_counts_the_pairs_out_of_order_and_the_facets` |
| Confluence: any rule order gives one normal form | `rules::the_normal_form_does_not_depend_on_the_order_of_the_rules` |
| The version tag separates rule sets | `rules::the_version_tag_separates_rule_sets` |
| Two normal forms share a serialization only when equal | `rules::two_normal_forms_share_a_serialization_only_when_equal` |
| Primitive numbers fixed, each used once, reaching the address | `prim_codes::*` |
| Domain normal form: finite set met in, endpoints moved onto the class, least class, pieces joined, every empty domain one form | `domains::one_set_of_integers_has_one_normal_form`, `domains::the_normal_form_admits_the_same_integers_and_is_unique` |
| Domain ends at -∞ and ∞, at ±2^70, at the `i64` boundaries; classes of modulus 2^70; already normal, and distinct from no domain | `cases::domain_endpoints_and_classes_past_64_bits_have_addresses_of_their_own` |
| `Domain::ints`, the interval with no other fact | `cases::domain_endpoints_and_classes_past_64_bits_have_addresses_of_their_own` |
| `address_of_body` equals `address` of the definition with no domain and no facets | `cases::a_body_held_in_place_has_the_address_of_its_definition` |
| `unit_address`: export order does not matter, the arrows of an overloaded name in any order, distinct export sets distinct | `cases::a_unit_address_hashes_its_exports_sorted_by_name_then_address` |
| Long chains, many facets, deep terms at small sizes | `scaling::chains_facets_and_deep_terms_are_canonicalized_at_small_sizes`; large sizes in the `bench` module |
| serial.rs lines 41–48, 83, 101, 138, 145, 531: the writer's `TooLarge` refusal when the system refuses memory for an exact number | None: reaching them needs an allocation the system refuses, which a small test cannot cause; the refusals of exact numbers that reach it are tested in crates/zed-kernel/src/num.rs |
| binders.rs lines 179, 251, 609, 649, 660, 726: `unreachable!` arms | None: each caller handles the binding forms (and builds a `match` from its arms) before reaching them |
| binders.rs line 234: `map_children` on a definedness fix | None: every caller (the rename step, `rename`, the rebuild of the one pass) handles a definedness fix as a binding form first |
| domain.rs line 101: `runs` with the bottom class | None: `Domain::normal` returns the empty domain before calling `runs` with the bottom class |
| domain.rs line 116: `joins` with an infinite end | None: pieces are disjoint and sorted, so only the last piece can end at ∞ and only the first can start at -∞, and neither has a neighbor on that side |
