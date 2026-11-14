# l03_09_egraph: completeness of the correctness tests

DESIGN sec:verification rung 2 (and rung 3 at a commutative ring): the sparse polynomial normal
form, the decision of an identity, its witness and its refusal. Code under test:
crates/zed-kernel/src/poly.rs (`decide`, `normal_form`), with the sides elaborated from Zed
source. The library's internals (the product's shape, packing, modular arithmetic, the support
product, the work charges) have their own unit tests in crates/zed-kernel/src/poly/tests.rs,
named below where they cover a case.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| **Normal form** | | |
| Products of sums expanded; like monomials merged; a literal power is a monomial | forms.rs `the_normal_form_prints_the_highest_degree_first_then_by_the_names_order`; poly/tests.rs `products_of_sums_are_expanded`, `like_monomials_are_merged`, `a_literal_power_is_a_monomial` | |
| Printed order: highest degree first, then by the binders' order; signs; a wide coefficient | forms.rs `the_normal_form_prints_the_highest_degree_first_then_by_the_names_order` | |
| Constants; a sum that cancels to 0; times 0; powers 0 and 1 | forms.rs `constants_and_the_powers_0_and_1` | |
| A base of 0, 1 or -1 (a constant, or the negation of one) with an exponent past `u64::MAX` | forms.rs `constants_and_the_powers_0_and_1` | |
| A base that evaluates to -1 but is not a constant node (`(0 - 1) ^ 18446744073709551617`) | none | Refused as a wide exponent: the rule in `trivial_base` looks only through negation. Not a wrong answer; noted in the TEST-complete-zir report, not pinned |
| The widest exponent a monomial holds, `u64::MAX` | forms.rs `constants_and_the_powers_0_and_1` | |
| Rational coefficients at `rat` (`r / 2 - r / 3`, `0.5 * r`); a division at `int` is an atom | forms.rs `rationals_are_coefficients_only_at_rat`; poly/tests.rs `rational_coefficients_at_rat` | |
| A term that is not ring arithmetic is an atom (`abs(x)`, a non-literal exponent, strings) | forms.rs `a_term_that_is_not_ring_arithmetic_is_an_atom`; poly/tests.rs `other_terms_are_atoms` | |
| A `let` read through; an unused `let` | forms.rs `a_let_is_read_through`; witness.rs `a_let_is_shared` | |
| A call is an atom and never refutes | witness.rs `a_call_is_an_atom_and_never_refutes` | |
| A chain of sums is one sum | poly/tests.rs `a_chain_of_sums_is_one_sum` | |
| **Decision** | | |
| The plan row's identities proved, the wrong one refuted at (1, 1) | rows.rs (5 tests) | |
| Refuted with the smallest values first; at `rat` | witness.rs `small_values_first`, `at_rat` | |
| The points are deterministic, alone and in a batch | rows.rs `the_points_are_the_same_alone_and_in_a_batch`; poly/tests.rs `the_points_are_deterministic` | |
| Proved as products of powers of the same factors; a false split refuted at a point | factored.rs (5 tests); forms.rs `an_exponent_past_u64_max_is_refused` (same power past `u64::MAX`) | |
| At a ring: a true identity proved (by factors and by expansion); a false one only `Differs` | forms.rs `at_a_ring_a_true_identity_is_proved_and_a_false_one_only_differs`; refusal.rs `a_ring_identity_is_decided_as_an_int_one` | |
| Atoms that differ: `Differs`, never refuted | forms.rs `a_term_that_is_not_ring_arithmetic_is_an_atom`; poly/tests.rs `a_ring_or_an_atom_is_never_refuted` | |
| Commutativity at `rat` | forms.rs `rationals_are_coefficients_only_at_rat` | |
| No point can be evaluated (denominator `2^61 - 1`): witness from the expanded difference; a true law proved | forms.rs `where_no_point_can_be_evaluated_the_witness_is_read_from_the_expanded_difference` | |
| A difference zero modulo P at every point (`x ^ (2^61 - 1) - x`) | poly/tests.rs `a_difference_zero_modulo_p_has_no_witness` | |
| **Refusal** | | |
| Work past the limit: the message with predicted ms, work, agreed points and the menu | refusal.rs `a_power_past_the_limit_is_rejected`; calibration.rs | |
| Sums in one name are never refused; four sums proved or refuted | refusal.rs (4 tests) | |
| Exponent past `u64::MAX`, from `normal_form` (no points) and from `decide` at `int` and at a ring (agreed points listed) | forms.rs `an_exponent_past_u64_max_is_refused` | |
| A product whose degree passes `u64::MAX` | forms.rs `an_exponent_past_u64_max_is_refused`; poly/tests.rs `refused_shapes` | |
| A false law with a wide exponent is refuted before the exponent is looked at | forms.rs `an_exponent_past_u64_max_is_refused` | |
| No obligation of the corpus is refused | measure.rs `no_obligation_is_refused` | |
| **Product choice and internals** | | |
| Dense against sparse product, by shape | choice.rs (3 tests); poly/tests.rs `the_dense_and_sparse_products_agree`, `the_choice_of_product_by_shape`, `mul_cost_at_its_corners` | |
| Packed keys, keys past `u128`, the support product, a wide index squared | poly/tests.rs `packed`, `sparse_keys_past_u128`, `support`, `the_support_product_agrees_with_the_sparse_one`, `the_square_of_a_wide_index_is_exact`, `the_product_takes_the_support_product_where_it_is_cheaper` | Internal representation, not reachable by a choice of source beyond what choice.rs reaches |
| Work charges | poly/tests.rs `work_of`, `merged_terms`, `the_charges_are_the_measured_ones`; calibration.rs | |
| **Size** | scaling.rs (small sizes), bench/ | Unusual sizes are benchmarks (P178) |
