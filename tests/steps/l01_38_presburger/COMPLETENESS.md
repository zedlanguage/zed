# Completeness: the linear-relation domain (L1.38)

Row TEST-complete-presburger (author P189). The code under test is the linear-relation domain,
crate `crates/zedc-presburger` (module `presburger` and its submodules, re-exported as
`zedc::store::presburger`): the formula constructors and printing, `satisfiable`, `decide`,
`project`, `project_each`, `project_each_boxed`, `row_box`, `entails` and rung 2, the refusals
and their repairs, `eliminated` and `colors`, and the translation of a function's terms into a
relation (`zedc::store::preimage::relations`) as the checker reads it. Expected results are from
DESIGN.md step L1.38 and its paragraph "Where this document does not say", and sec:constraints;
where DESIGN is silent (the printed form of a row, the box of `row_box`), from the doc comment
of the function, which is cited at the test.

llvm-cov over the 22 source files of the domain (`presburger.rs` and `presburger/`, leaving out
test and benchmark modules, the scaling and seed helpers, and `conjuncts.rs` and `hull.rs`, which
are step L1.39's and TEST-complete-reduced's), as a floor, regions (lines): this group's tests
and the crate's unit tests, benchmarks left out, 93.55% (93.50%) → 93.89% (93.82%); with every
benchmark of the group and of the crate as well, 94.45% (94.38%). Per file the tests moved
`formula.rs` 96.28% (97.98%) → 98.48% (99.75%), `refusal.rs` 95.71% (97.83%) → 99.14% (99.28%),
`deep.rs` 96.66% (96.91%) → 97.67% (98.07%), `presburger.rs` 93.00% (92.47%) → 93.64% (93.05%),
`one_row.rs` 99.49% → 99.83% of regions. Whole crate, every file: 85.55% (85.81%) → 85.85%
(86.09%) without the crate's small-size unit tests; 88.78% (88.86%) with them.
No test failed against DESIGN, so no FAIL row was filed.

Tests in `completeness.rs` unless a file is named.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| `Formula::top` and `bottom` through `satisfiable`, `decide`, `project`, `project_each`, `entails`, `eliminated` | `true_and_false_answer_every_question` | |
| `and` and `or` of no operand, one operand, a constant operand, nested operands | `conjunctions_and_disjunctions_of_none_one_and_constant_operands` | |
| A chain built by `and_with` one operand at a time equals the chain built at once | `a_chain_joined_one_operand_at_a_time_is_the_chain_joined_two_at_a_time` | |
| `negate`: double negation, negated constants, negation normal form (DESIGN: "put in negation normal form") | `negation_removes_double_negations_and_constants` | |
| Forgetting a symbol weakens a formula, by the parity of the negations above it | `forgetting_a_symbol_weakens_by_the_parity_of_negations` | |
| A set (`IntervalSet`) read as a formula holds exactly at its members: empty, a point, gaps, half-lines, every value | `a_set_as_a_formula_holds_exactly_at_its_members` | |
| `either` takes the shared conjuncts out of two arms and drops a complement | `either_takes_out_the_shared_conjuncts_and_drops_a_complement` | |
| A row is reduced by the gcd of its coefficients and its constant rounded inward; an equation the gcd does not divide has no point | `a_constraint_is_reduced_by_the_gcd_of_its_coefficients` | |
| `Lin` sums, scaling by 0, 1, -1, k; products of two atoms as an atom (rung 2) | `terms_are_added_scaled_and_multiplied` | |
| Printed form of rows and terms (DESIGN is silent; `Con::show` doc: constants on the right, first atom positive) | `constraints_and_terms_are_printed_with_the_first_atom_positive_on_the_left` | |
| Each conclusion of rung 2 prints (proved, refuted with a countermodel, not proved) | `each_conclusion_of_rung_2_is_printed` | |
| A relation prints with its definitions and `defined()` conjoins them | `a_relation_is_printed_and_conjoined_with_its_definitions` | |
| `entails` between relations whose definitions share a number is a programming error, stated by a panic | `entailment_between_relations_whose_definitions_share_a_number_panics` | |
| Split repair names skip the names the program takes | `split_names_skip_the_names_a_program_takes`; `checker.rs` `the_split_repair_names_functions_the_program_does_not_define` | |
| The names of a condition are its variables, once each, in order of first use | `the_names_of_a_condition_are_its_variables_once_each_in_order` | |
| Factors and formulas print with the names the program wrote (`Factor::is`, `of`, `atom`, `written`) | `factors_and_formulas_are_written_with_the_names_the_program_wrote` | |
| The refusals Growth, Shadows, Disjuncts, Tie and Unordered each have their message (DESIGN's two quoted messages) and end with what the checker kept | `each_refusal_reason_ends_with_what_the_checker_kept`; `omega.rs` `each_cause_of_a_refusal_has_its_own_message` | |
| A refusal offers only the repairs its data supports | `a_refusal_offers_the_repairs_its_data_supports`; `checker.rs` `following_each_repair_of_the_menu_makes_the_program_check` | |
| The cause of a wider set: the whole question first, then a symbol, then a disjunction | `the_first_cause_of_a_wider_set_is_the_whole_question_then_a_symbol_then_a_disjunction` | |
| A refused projection keeps the box of its rows: one-term rows, the widest bounds over a disjunction, each wider row tightening each atom once | `a_refused_projection_keeps_the_box_of_its_rows` (pigeons; the CROSSING rows raised by 8, refused with Growth, box hand-derived) | |
| `row_box`: hull of a disjunction, a disjunct with no point passed over, a disjunct that does not bound, lower-only bounds, a negation, top and bottom, equations, a two-term row | `the_box_of_rows_reads_one_term_rows_equations_and_disjunctions_that_bound_in_every_case` | |
| A projection over every value the points take, an over-approximation allowed with disjunctions left (DESIGN: "holds every value") | `a_refused_projection_keeps_the_box_of_its_rows`; `projection_oracle.rs` all; `disj_groups.rs` hull tests | |
| `project_each` with a repeated and an absent symbol | `project_each_answers_a_repeated_and_an_absent_symbol` | |
| `eliminated` is exact or declined | `elimination_is_exact_or_declined` | |
| Colors: the coarsest stable refinement tells apart only what the structure does | `colors_tell_apart_only_what_the_structure_does`; `canonical.rs` all | |
| Test hooks change no answer and their counters reset | `the_test_hooks_change_no_answer_and_their_counters_reset` | |
| Translation of `+`, `-`, a constant product, `^` 0, 1 and of a constant, Euclidean `div` and `mod` by negative constants and by 1, `abs`, `min`, `max`, a branch, `!`, `!=`, `&&` beside `\|\|`, `true`, `false`, an equation with no integer point, agree with the interpreter at every point of `-7..=7` | `tests_at_the_edges_of_the_operators_agree_with_the_interpreter`; `random.rs` `random_tests_agree_with_the_interpreter` | |
| `^ 2` is a product of two symbols and goes to rung 2 | `ladder.rs` `a_square_is_bounded_only_from_a_premise_on_its_factor` | |
| `div`/`mod` by a symbol: rung 2 alone; a divisor that may be zero proves neither | `mod_symbol.rs` all | |
| Float, rational and generic parameters are not read as integers | `carrier.rs` all | |
| Pugh's equalities, including a row with no unit coefficient | `omega.rs` `a_ledger_equation_with_no_unit_coefficient_is_solved`, `opposite_rows_meet_in_an_equality_or_nowhere` | |
| Real shadow tested at the first inexact step, dark shadow after, splinters only when the dark shadow has no point | `controls.rs` `a_question_between_the_shadows_is_decided`; `scaling.rs` `chains_of_inexact_eliminations_are_answered`, `a_point_in_a_splinter_of_a_splinter_is_found` | |
| Splinters searched a batch at a time; tie that shares a row refused; tied variables that share no row eliminated together | `names.rs` `the_splinters_are_searched_a_batch_at_a_time`, `a_tie_that_shares_a_row_is_refused`, `tied_equalities_are_kept_as_rows_and_decided` | |
| No answer depends on names or row order | `names.rs` every-naming tests; `omega.rs` `the_answer_does_not_depend_on_the_order_of_the_constraints`, `..._of_the_disjuncts`; `oracle.rs` `answers_do_not_depend_on_names_or_order` | |
| Split into parts sharing no variable; the least cause of the parts | `omega.rs` `joint_stage_hulls_are_exact`, `pipeline_stage_hulls_are_exact` | |
| Two-variable part decided exactly | `oracle.rs` `large_coefficients_over_two_variables_match_enumeration`; `controls.rs` | |
| UTVPI rows by the parity of zero-weight cycles; acyclic in topological order; the three searches agree | `stages.rs` `acyclic_and_cyclic_unit_rows_are_decided`, `unit_rows_around_cycles_are_decided`, `a_dense_octagon_with_a_parity_obstruction_has_no_point`, `the_race_agrees_where_the_pairs_stop_against_duong`; `model.rs` | |
| Box stages: empty box, a single-point box, the five trial points, a rational point not shown empty | `stages.rs` `rows_with_an_empty_box_have_no_point` to `rows_the_one_pass_test_does_not_show_empty_stay_refused` | |
| Proportional columns merged and lifted back by Bézout factors | `stages.rs` `proportional_columns_of_mixed_signs_are_decided`; `oracle.rs` `proportional_columns_match_enumeration_of_their_aggregates` | |
| Three variables by Megiddo and LLL; Reeve's tetrahedra; flat directions | `live3.rs` all | |
| Disjunctions: removal by the base, rounds, one-level lookahead, a refused disjunct never taken for a point, least sorted keys | `names.rs` `a_disjunct_the_solver_refuses_is_not_taken_for_a_point`, `a_refused_disjunct_beside_one_with_a_point_gives_one_answer`; `model.rs`; `disj_groups.rs`; `nest_empty.rs` | |
| Atoms sharing a color: settled or refused with Unordered | `names.rs` `a_formula_whose_atoms_share_a_color_is_settled_or_refused`; `one_row.rs` | |
| Rung 2: products from the premises on their factors; countermodel only where the interpreter's product holds | `entailment.rs` all; `ladder.rs` all; `product_parity.rs` all | |
| The checker: a refused question rejects the function with its cause; a decided one rejects nothing | `checker.rs` all | |
| The z3 fixtures reproduce exactly | `preimage.rs` `the_z3_fixture_reproduces_exactly` | |
| `xs[i + 1]` in bounds ⇒ `i ∈ [0..=n-2]`, countermodel `n = 1, i = 0` | | needs L3 (DESIGN: "once L3 lands") |
| Shared parts (`deep.rs`) compare, hash and decide as written out | `shared.rs` all | |
| Values past 64 and 128 bits | `omega.rs` `a_model_may_hold_values_past_128_bits`, `a_bound_past_i64_is_exact`; `checker.rs` `a_bound_past_the_64_bit_range_keeps_the_question` | |
| The 36 imbl/archery functions the benchmarks reach | | library code, not this crate's (brief) |
| The known slow or refused cases (negated chain at seed 39*7919+1, residue-interval chain at 27*104729+7, windows refused with Growth at n = 6, modular case 2937) | | benchmarks by P178; not brought back into correctness tests |
| Lines reached only by benchmarks (about 1,180 of the 22 files: `cells_by_classes`, `CellWalk::catalog_live`, `try_pick_disjoint_wide`, `cells_of`, `parse_one_point_disj`, `GuardedChain::of`, `modular::solve_short_x_interval`, and inline benchmark fixtures in `extend.rs`) | | fast paths for large structured families whose answers the correctness tests above check on the general path; the 16 functions of this crate that only benchmarks reached are covered by single-case tests since ef1cc9ca4 (TEST-split-l0138) |
| The cell sweep (`cell_sweep::cells_of`): chains of guarded definitions with twin copies at each level, a definition two guards both pick on part of the range of `i` (the involution sweep, at the last level or at every level), definitions affine in `i`, a target `t_n == v`, `t_n >= v`, `t_n <= v`, `v <= t_n <= v` or none, a top-level disjunction on `i` alone, a bounded parameter `k`; each answer against enumeration of the chain's values | `cell_sweep.rs` all | the bound targets of the every-level family, and that family with `k`, are refused with Disjuncts at n = 3 to 5: row FAIL-pres-overlap-every-level-refused |
| Lines no test or benchmark reaches (2,111 of the 22 files at 4f8d22e94; `cell_sweep.rs` reaches 314 more, see row TEST-presburger-unreached-paths for what is left): the involution and disjoint cell sweeps (`cell_sweep::sweep_involution`, `sweep_disjoint`, `holds_1var_span`, `holds_2var_span`, `parse_unit_target_eq`, about 450 lines), `slack::fill_row_model` and the wide-row sweeps (about 150), `find_probe_points`, `ScalarImages::record_step` and `exception_step`, `Exception::missing` and `residue`, `extend::quotient_offsets`, `modular::ScalarWitness::quotient` | | no input of the present tests or benchmarks has these fragments' shapes; each is a fast path whose answer equals the general path's. Row TEST-presburger-unreached-paths finds an input for each, or shows it dead and removes it |
