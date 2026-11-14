# Completeness: preimage catalog (L1.25)

Row TEST-complete-preimage (author P189). The code under test is `crates/zedc-preimage/src/preimage.rs`
(the backward transfer: the catalog of entries, its forward pass, the piecewise-affine summaries,
the class-by-class reading of remainders, the stops), `crates/zedc-preimage/src/address.rs` (the
address of a term up to binder names) and the reference catalog `preimage_ref.rs` the tests compare
against. Expected results are from DESIGN.md step L1.25 and sec:domains, "Backward transfer, and
`@ensure`": affine maps, Euclidean `div` and `mod` by a constant, `min` and `max` invert exactly;
a branch is the union of its arms under their guards; nonlinear arithmetic and a divisor that is
not a constant are read by interval revision, necessary only; a failure meets no demand, `==`
compares failures as data, and a failing operand meets an ordered comparison with a constant
nowhere; hashes, string operations other than `len` and foreign calls stop the transfer, each stop
is reported with its term and keeps the whole box, necessary; a necessary box the forward transfer
shows meets the demand everywhere is marked exact; a listed box is enumerated only when the
catalog's answer is not exact.

Coverage by this group and the `zedc-preimage` unit tests (llvm-cov, benchmarks skipped):

| File | Before the pass | After |
|---|---|---|
| `preimage.rs` | regions 73.23%, lines 72.22% (2781 missed) | regions 73.13%, lines 72.28% (2778 missed) |
| `address.rs` | regions 71.79%, lines 70.84% (275 missed) | regions 95.90%, lines 96.54% (36 missed) |
| `preimage_ref.rs` | lines 86.98% | lines 87.14% |
| `divisors.rs`, `holes.rs`, `shared_ints.rs`, `spans.rs` | 98.72%, 95.68%, 97.35%, 98.61% | unchanged |

The region count of `preimage.rs` falls by a tenth of a point because the new unit test of the
chain cliff instantiates more of the generic code than it reaches; the line count rises. With the
groups that read the crate through the reduced product as well (`l01_38_presburger`,
`l01_39_reduced_product`, `l01_39a_bit_words`, `l01_39b_on_demand`), `preimage.rs` is at 95.62% of
lines (439 missed) and 94.73% of regions, `address.rs` at 97.31% of lines, and the crate at
93.34%; `images.rs` (95.59%), `loops.rs` (97.30%), `threshold.rs` (96.93%) and `product.rs`
(92.88%) are read only by those groups and are covered there, not here.

What stays uncovered in `preimage.rs` with all five groups, by kind:

- about 15 `unreachable!` arms, for shapes the callers rule out;
- early `return None` refusals for shapes the catalog does not handle, which fall back to the
  next method and give the same box (each fallback is covered from its other callers);
- the relational code (`relation`, `instance`, `projected`, `identity_classes`) on relational
  shapes no small term of this group produces; its common paths are covered by `l01_38` and
  `l01_39`;
- the `BoxSet::Read` paths and the lazy `marks` landmarks, reached only from reads of families;
- the `same` term comparison for `Lam`, `Let`, `If` and `Follow` nodes, the undo log for
  `Projection` and `DefinedCall`, and `scan`, `reads_mod` and `by_class` through `Let` and
  `Follow`, which only a remainder test spelled through a `let` inside a summary over classes
  reaches; `a_remainder_spelled_through_a_let_a_call_or_not_reads_as_written_plainly` spells a
  remainder through a `let`, a call of an operator and `!`, and the catalog reads each of them
  before it reaches those paths, with the box of the plain spelling;
- `both_ints`, the `PrimFn` callee in `pa` and `by_class`, and a constant past 64 bits in `pa`:
  `pa` is asked only after the constant folder and the call rewriter have run, and they leave
  no such node (inferred from the code, not shown by a probe); `x + 2^70 < 2^70 + 5` is read exactly by the affine entry instead.

`address.rs` keeps 36 lines of `fmt` and evidence printing. `preimage_ref.rs` keeps its own
refusal arms, which the catalog under test reaches first.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| A plain input under each kind of demand: a point, a ray, a range, a set of pieces, nothing, everything, true, false | `completeness.rs` `a_plain_input_meets_each_kind_of_demand` | |
| A closed term keeps the whole box or none of it | `a_closed_term_keeps_the_whole_box_or_none_of_it`; `scaling.rs` `closed_terms_have_the_values_of_the_tree_walk` | |
| An input the term does not read keeps its set | `an_input_the_term_does_not_read_keeps_its_set`; `exact.rs` `inputs_the_term_does_not_read_keep_their_sets` | |
| A demand of the wrong type holds at no point | `a_demand_of_the_wrong_type_holds_at_no_point` (soundness only: the checker never asks it) | |
| `x + c`, `c + x`, `x - c`, `c - x`, `c * x`, `x * c` with c positive, negative, zero | `shifts_and_scalings_invert_with_the_constant_on_either_side`; `entries.rs` `shifts_and_scalings_by_a_constant_invert_exactly`; `constant_minus.rs` (11 tests) | |
| Euclidean `div` and `mod` by a positive, a negative, 1, -1 and 0 | `euclidean_div_and_mod_by_each_kind_of_constant`; `entries.rs` `euclidean_division_and_remainder_by_a_constant_invert_exactly`; `random.rs` `a_remainder_inverts_to_its_first_and_last_periods_and_one_piece_between` | |
| `div` and `mod` by 0 compared with a constant under the demand that holds everywhere: exact | | FAIL-preimage-div0-false-exact: the box is `[..]`, marked necessary |
| A divisor that is not a constant: read by revision, necessary | `a_divisor_that_is_not_a_constant_is_read_by_revision`; `entries.rs` `a_division_that_can_fail_keeps_only_the_points_that_do_not` | |
| Negation, `abs`, powers with a constant exponent of each parity and of 0 | `negation_abs_and_powers_invert_at_their_endpoints`; `entries.rs` `abs_and_negation_invert_at_their_endpoints`, `a_square_bound_is_read_as_a_power_and_inverted_exactly`; `powers.rs` (13 tests) | |
| `min` and `max` with a constant, either side | `min_and_max_with_a_constant_invert_exactly` | |
| `min` and `max` of two terms; one operand failing | `min_and_max_of_two_terms`; `exact_oracle.rs` `min_and_max_read_where_the_other_operand_fails` | |
| Each of `<`, `<=`, `>`, `>=`, `==`, `!=` with the constant on either side, under true and false | `each_comparison_with_a_constant_on_either_side_inverts_exactly` | |
| A comparison of two terms: their difference | `entries.rs` `a_comparison_of_two_terms_constrains_their_difference` | |
| `==` and `!=` of two tests: the union of their agreements | `a_comparison_of_two_tests_is_the_union_of_their_agreements` | |
| `!`, `&&`, `||` under true and false: meet, join, swap | `not_and_or_meet_join_and_swap_under_each_demand`; `entries.rs` `tests_combine_by_meet_and_union` | |
| A test that can fail inside `&&`, `||` | `entries.rs` `a_test_that_can_fail_is_not_combined_as_a_boolean`, `a_strict_disjunction_with_a_failing_side_is_necessary_only` | |
| A branch: the union of its arms under their guards; a constant guard; nested branches | `a_branch_is_the_union_of_its_arms_under_their_guards`; `entries.rs` `a_branch_is_the_union_of_its_arms` | |
| An atom (a failure as data) in an arm, compared with a constant, under true and false | `an_atom_a_wide_constant_and_a_bool_argument_are_read_exactly` | |
| A `let` read through; names hidden and shadowed | `a_let_is_read_through`; `scopes.rs` (10 tests) | |
| A call of a lambda, of an operator, of a closure; a constant bool argument picking the arm | `calls_are_read_through_and_foreign_ones_stop`, `an_atom_a_wide_constant_and_a_bool_argument_are_read_exactly`; `entries.rs` `a_call_is_read_through`, `a_summary_reached_from_another_call_keeps_only_what_it_narrows`; `scopes.rs` `one_function_called_twice_is_summarized_for_each_argument` | |
| A recursive call stops where it calls itself | `stops.rs` `a_call_that_never_returns_stops_where_it_calls_itself`; `scaling.rs` `ifs_under_recursion_whose_arms_are_one_shared_term_stop_at_the_call` | |
| A foreign call on an input: a stop, reported | `calls_are_read_through_and_foreign_ones_stop`; `stops.rs` `a_foreign_call_stops_the_transfer` | |
| A foreign call on constants: a stop, reported | | FAIL-preimage-foreign-constant-unreported: the box is kept, necessary, with no stop |
| A primitive with the wrong number of operands: a stop, reported | | FAIL-preimage-arity-stop-unreported: the box is kept, necessary, with no stop |
| String operations: a stop; `len` read through; on constants alone, run | `stops.rs` `a_string_operation_stops_the_transfer`, `a_string_operation_on_constants_only_is_run`, `a_length_under_arithmetic_is_read_through_to_its_stop` | |
| A stop in an arm that never runs | `calls_are_read_through_and_foreign_ones_stop` checks the box (`[3..]`, exact) only | DESIGN does not say whether the stop in the untaken arm is reported; the test does not look at the stops |
| `fold`, `gen`, `fix`, a tuple component between the demand and an input | `stops.rs` (`a_fold_...`, `a_gen_...`, `a_fix_...`, `a_term_outside_the_scalar_catalog_is_reported`); `calls_are_read_through_and_foreign_ones_stop` | |
| Copies of one stop; stops over one shared term | `stops.rs` `copies_of_a_stop_are_two_stops_shown_once`, `stops_over_one_shared_term_are_each_reported` | |
| A listed box: enumerated with one input of several members, not with two | `a_listed_box_with_two_inputs_of_several_members_is_not_enumerated`; `entries.rs` `a_listed_box_is_enumerated_and_a_range_is_not`; `scaling.rs` `a_listed_set_is_enumerated` | |
| The forward pass marks a necessary box exact | `entries.rs` `the_forward_pass_confirms_a_box_the_backward_pass_cannot` | |
| An exact search: classes, witnesses, inputs it touches | `exact.rs` (5 tests); `scaling.rs` `an_exact_search_reads_only_the_inputs_it_touches`; `exact_oracle.rs` `a_point_that_fails_keeps_the_exact_search_from_marking_its_box_exact` | |
| Constants and ends past i64 and i128; a constant past 64 bits in an affine term | `an_atom_a_wide_constant_and_a_bool_argument_are_read_exactly`; `wide_constants.rs` (6), `wide_ends.rs` (7), `kept_ends.rs` (3), `entries.rs` `bounds_past_i64_keep_the_box`, `a_literal_of_2_to_the_200_is_an_exact_end` | |
| Sums at the ends of i64 | `overflow.rs` (5 tests) | |
| A remainder test spelled through a `let`, a call of an operator, `!`, or with a constant past 64 bits: the box of the plain spelling | `a_remainder_spelled_through_a_let_a_call_or_not_reads_as_written_plainly` | |
| Guards on remainders read class by class | `s22.rs` `a_chain_of_guards_on_remainders_is_read_class_by_class`, `remainders_compared_every_way_are_read_exactly` | |
| Chains of shared terms, guarded chains, slow families | `s22.rs` (43 tests); `scaling.rs` (13); `deep.rs` (3) | |
| A chain on both sides of PREIMAGE-chain-cliff (`x mod 3` guards at k = 320 and 350; mixed guards on `y` at k = 2000) | `crates/zedc-preimage/src/preimage.rs` unit test `chains_are_read_exactly_on_both_sides_of_the_cliff` | The second chain past its cliff (k = 2150 takes 0.5 s and grows fourfold each 50 more) is a benchmark's size, timed in `preimage/tests/bench.rs` |
| One term in any allocation order; a shared part read as the same term | `shared.rs` `shared_terms_have_one_preimage_in_any_allocation_order`; `scopes.rs` `a_shared_part_is_read_as_the_same_term` | |
| Each primitive's claimed tonicity | `tonicity.rs` (4 tests) | |
| Random terms: sound, and exact where claimed, against the interpreter and the reference catalog | `random.rs` (7), `exact_oracle.rs` (6), `ref_memo.rs` (7) | |
| Every kernel form (`Fam`, `Reindex` with each witness, `Discard`, `Fold` with each grade, `Gen` with each position, `Read`, `Push`, `PrimFn`, each match pattern) has one address up to binder names, and distinct forms have distinct addresses | `crates/zedc-preimage/src/address.rs` unit test `every_kernel_form_has_one_address_up_to_binder_names` | |
| Let-bound names of the checker's environment, relations between inputs | | Read by the reduced product; covered by `l01_38_presburger` and `l01_39_reduced_product` |
| A box refused by the reduced product does not depend on the names of the inputs | | FAIL-product-refused-box-renamed (found by the random test of `l01_39_reduced_product`, `pendants.rs`, seed 6277671696228035587) |
| Holes piled in the trees of the on-demand projection | | FAIL-linked-piled-holes-count (found by the random test of `l01_39_reduced_product`, `linked.rs`, seed 10423609239771793175) |
