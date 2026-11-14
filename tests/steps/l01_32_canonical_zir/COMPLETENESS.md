# l01_32_canonical_zir: completeness of the correctness tests

DESIGN M0.7 and L1.32: the four rewrite rules (binders, hints, facets, domain) on ZIR, the
one-pass normal form, the content address and the bottom-up key. Code under test:
crates/zedc-zir/src/zir/canon.rs, and the M0.7 rules it reuses from crates/zedc-zir/src/canon/,
whose own cases are listed by m0_07_canonicalization.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| **Binder rule** | | |
| Tuple pattern binders renamed together and apart; order kept | stability.rs `renamed_binders_keep_the_address` | |
| Atom pattern with one binder; the hint of the written name on the argument it binds, then dropped | stability.rs `the_normal_form` | |
| Fields pattern: binders renamed in field order, each hint on its own argument, steps `binders, binders, hints ×3` | binders.rs `a_fields_pattern_s_binders_are_renamed_in_field_order` | |
| A wildcard or a literal before a binder takes no level; which field a binder is under changes the address | binders.rs `a_wildcard_or_a_literal_takes_no_level` | |
| Binders nested in a field (a tuple, an atom) counted in preorder | binders.rs `binders_nested_in_a_field_count_in_preorder` | |
| Each arm counts from 0; the first arm with no binder is skipped | binders.rs `each_arm_counts_its_binders_from_0`, `a_fields_pattern_s_binders_are_renamed_in_field_order` | |
| A match one region down, in a lambda's body | stability.rs `renamed_binders_keep_the_address`, fuzz.rs | |
| A match inside a match arm | binders.rs `a_match_inside_a_match_arm_is_renamed_too` | |
| Binders already at their level: nothing to do; a written binder after one counts it | binders.rs `canonical_binders_are_already_normal` | |
| A binder spelled as a level that is not its position's (`($$5, y)`, `($$1, $$0)`) | none merged | FAIL-zir-canon-misplaced-level-binder: kept as written, so the address differs from `(a, y)`'s |
| Binding where a literal was matched is a different graph | stability.rs `renamed_binders_keep_the_address` | |
| **Hints, facets, domain** | | |
| Hints renamed or dropped keep the address | stability.rs `hints_do_not_reach_the_address` | |
| Facet order and repeats keep the address | stability.rs `facet_order_and_repeats_do_not_reach_the_address`, scaling.rs `an_edge_of_a_few_facets_is_sorted_and_keyed` | |
| The facet order is total, transitive, and ties exactly the equal values (kind, bits) | facet_order.rs (4 tests) | |
| One set of integers in any spelling has one address | stability.rs `one_set_of_integers_has_one_address` | |
| Values reach the address; an empty payload reaches it | stability.rs `values_reach_the_address`, `an_empty_payload_reaches_the_address_and_the_bytes` | |
| Every NaN is one word | stability.rs `every_nan_is_one_word` | |
| Wide numbers: sign, numerator and denominator, kept powers, products of powers, cut limb counts | wide_constants.rs (9 tests) | |
| A state edge has no facts and is left alone; a graph with no match and no facts is normal | binders.rs `a_graph_with_no_match_has_nothing_for_the_binder_rule` | |
| **Rewrite system** | | |
| Every step lowers the ranks; the normal form has rank 0 | fuzz.rs `every_step_lowers_the_ranks`, binders.rs, stability.rs `the_normal_form` | |
| The one pass reaches the graph the steps reach: random graphs, and each pattern form above | fuzz.rs `the_one_pass_normal_form_is_the_one_the_steps_reach`, binders.rs `steps` helper | |
| Shuffles and renamings keep the address | fuzz.rs `shuffles_and_renamings_keep_the_address` | |
| Canonicalizing is idempotent, and the normal form reads back from binary | stability.rs `the_normal_form` | |
| **Address and key** | | |
| The address is pinned (VERSION) and printed as 64 hex digits | stability.rs `the_address_is_pinned`, `the_normal_form` | |
| The bottom-up key agrees with the address, including on a change inside a region | fuzz.rs `the_key_agrees_with_the_address` | |
| A graph too large for memory to encode (`TooLarge`) | none | An unusual size (P178); no small input reaches it |
| **Size** | bench/ | Unusual sizes are benchmarks (P178) |
