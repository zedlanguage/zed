# Completeness: the reduced product (L1.39)

Row TEST-complete-reduced (author P189). The code under test is the cell as the reduced product
of the lattices, the type, the linear relation and the binding time
(`crates/zedc-preimage/src/product.rs`, `Scope`, `Product`, `arms`, `forward`, the affine hull,
the lazy scope, holes, pendants, the `@exact` search), and the checker's reading of it at each
arm (`crates/zedc-check/src/check/arms.rs` and the arm checks in `walk.rs`). Expected results
are from DESIGN.md step L1.39, sec:domains and sec:constraints.

llvm-cov of this group's tests (benchmarks skipped), as a floor, regions (lines) before → after:
`crates/zedc-check/src/check/arms.rs` 12.87% (17.46%) → 43.25% (45.93%);
`crates/zedc-check/src/check/walk.rs` 29.05% (30.03%) → 33.19% (34.47%);
`crates/zedc-check/src/check/mod.rs` 26.96% (30.81%) → 28.20% (32.17%);
`crates/zedc-preimage/src/preimage.rs` 62.32% (64.22%) → 63.94% (65.69%);
`crates/zedc-preimage/src/product.rs` 93.41% (92.97%) → 93.40% (92.97%). The store was
well covered through its API; the checker's reading of the arms was not, which is what
`completeness.rs` adds, and where both defects below were found.

Tests in `completeness.rs` unless a file is named.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| The arm of `n >= 0 && n <= 10 && n mod 4 == 1` holds `int[1..=9]`, congruence `1 mod 4`; its `else` loses 1, 5, 9 | `spec.rs` `an_arm_that_fixes_n_mod_4_within_0_to_10_holds_1_to_9` | |
| The same through the checker: accepted at width 4, rejected at 3; the function runs as its arms say | `the_design_arm_of_n_mod_4_within_0_to_10_holds_9_at_most` | |
| The arm of `n >= 2 && n <= 4 && n mod 4 == 1` is unreachable and the program accepted | `spec.rs` `an_arm_no_value_reaches_is_unreachable_and_the_program_is_accepted`; `an_arm_no_value_reaches_is_accepted_whatever_its_body` | |
| An arm whose test calls a definition is narrowed through the call (`clamp(x) > 10` unreachable), in the store | `helpers.rs` all; `random.rs` `an_arm_unreachable_only_through_a_called_function_is_compared` | |
| The same through the checker, with `clamp` a definition, a `let`-bound lambda, or a name bound to an `if` | `arm_test_through_call::*` | fixed by FAIL-check-arm-test-through-call: a test on a call of a definition is kept as an application the scope reads through (`Ck::callable`, COMPLEXITY C26); `the_design_programs_run_as_their_arms_say` runs the program |
| `debug = false; mode = if debug { 1 } else { 2 };` is accepted and `mode` is static, 2 | `spec.rs` `a_binding_read_from_a_static_if_is_static`; `the_design_programs_run_as_their_arms_say`; `an_arm_no_value_reaches_is_accepted_whatever_its_body` | |
| `isPrime(p)` in a test: the interval `int[0..=100]` and the congruence `0 mod 2`, a range not enumerated | | needs L3 (DESIGN: "once L3 lands"); the range rule is in `controls.rs` `a_listed_set_is_enumerated_and_a_range_is_not` |
| `@exact`: `x * x mod 10 == 9` over `int[0..=30]` keeps the interval and allows `{3, 7, 13, 17, 23, 27}`; `m * x mod 10 == 1` allows `m` in `{3, 7, 13, 17}`; `x == 4` over `int[0..=10^12]` empty by one point | `exact.rs` all | |
| `@exact` written in source | | step L15.1; covered as refused in `l01_39b_on_demand` |
| Each prelude reduction alone: single value, congruence and ends, type widening, an empty interval removing `int`, parity | `controls.rs` | |
| A congruence moving the ends an arm reads, odd and even | `a_congruence_moves_the_ends_the_arm_reads` | |
| Enumeration of a listed set: members kept, other names static, a failing constraint on static names, a range not listed, widths | `controls.rs` the enumeration tests; `finite_from_type.rs` all | |
| Exclusion by complement of an exact element: `!=`, `i64::MAX` | `spec.rs` `a_negated_equality_excludes_the_literal_by_complement`, `a_negated_equality_with_i64_max_keeps_the_integers_past_it` | |
| Complement read by the checker: `else` of `!=`, of `||`, of `!`, an `else if` chain, the `else` of `mod` | `the_complement_of_an_exact_test_bounds_the_other_arm` | |
| No exclusion where the form does not show the element | `controls.rs` `a_constraint_whose_form_does_not_show_it_ends_removes_nothing` | |
| Iteration to a fixed point; parts passing a bound back and forth | `nests.rs` `two_parts_that_pass_a_bound_back_and_forth_reach_the_empty_scope`, `a_walk_through_a_shared_name_reaches_the_fixed_point` | |
| The linear relation: two names bound by each other; a join keeping the affine relation; the hull | `spec.rs` `a_relation_between_two_names_bounds_each`, `a_join_keeps_the_affine_relation_of_its_sides`; `hull.rs` | |
| Binding time: meet and join, a binding from a parameter is run time | `spec.rs` `a_meet_takes_the_earlier_binding_time_and_a_join_the_later` | |
| Disjunction, relation and nesting read by the checker | `a_disjunction_a_relation_and_a_nest_each_bound_the_arm` | |
| A `let` binding narrowing its inputs; a typed lambda; a static width | `let_terms.rs`; `a_binding_a_typed_lambda_and_a_static_width_carry_the_arm_bound` | |
| A function or lambda with an untyped parameter: the need it passes on reads its arm's tests | `generic_need_arm::*` | fixed by FAIL-check-generic-need-ignores-arm: the need is read under the arm with the parameters taken as int (`Ck::ints_as_int`, COMPLEXITY C26) |
| Unreachable arms by parity, a self-contradicting relation, the `else` of a test every value meets, a static `false` | `an_arm_no_value_reaches_is_accepted_whatever_its_body` (each with a reached control) | |
| Nests of tests in every grouping and order; random nests | `nests.rs` all | |
| Tests on `||` alternatives that limit each other in a loop | `loops.rs` all | |
| Literals following a parameter's carrier (L1.26a) | `follow.rs` all | |
| The soundness of each arm against the interpreter on random bodies | `random.rs` all | |
| Holes, pendants, refused disjuncts and their warnings, shortest-path seeds, linked components, two disjunctions, the lazy scope against the eager one, written constraints by address, integer roots | `holes.rs`, `pendants.rs`, `refused.rs`, `seed_edges.rs`, `linked.rs`, `two_disjunctions.rs`, `lazy.rs`, `written_address.rs`, `roots.rs`, `xst/` | |
| Float `^` and the NaN class | `pow_nan.rs` | |
| Deep terms, deep conditions, named rules and families from cross-review | `deep_let.rs`, `deep_condition.rs`, `named_test.rs`, `families.rs`, `disjoint.rs`, `path_check.rs`, `if_shortcut.rs` | |
| Scaling | `scaling.rs`, the `bench` modules | |
| A call's result as an operand (`bitNot(clamp(n), width: 3)`) | | a call is an opaque int in the checker's arm scopes (`arms.rs`, COMPLEXITY C26); DESIGN asks narrowing through a call only for a test, which FAIL-check-arm-test-through-call holds |
| Declared constraints making an empty element | | step L10.4 |
| A `match` arm narrowing | | `match` on ints is not compiled by this zedc yet |
