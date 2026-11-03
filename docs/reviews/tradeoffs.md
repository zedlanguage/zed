Complexity tradeoffs: a review of the code history (item TRADEOFF-DOC, 2026-11-03). Base: zed-impl main at 059aafa.

A complexity tradeoff is a place where the code gives up some inputs, or some precision, to avoid the cost of a complete algorithm. Each confirmed site now carries a comment that begins `Complexity tradeoff:` (in Zed prelude files, the same words as a `//` comment). The comment names: what is given up and the answer those inputs get; why (the cost of the complete algorithm); the property of the input that triggers it; the test and the COMPLEXITY.md row; and what a complete solution would need.

113 reports from the history search, which overlap, came down to 57 distinct sites. The first verification found 5 more sites of the same kind that no report named (the four narrowings and `StopKind::Outside`), so 62 sites were judged: 43 confirmed and 19 discarded.

## Confirmed sites

Status before: yes (all five parts written at the site), partial (some written), no (none). Action: "completed" (the existing comment was extended), "new" (no comment before). Sites marked "violation" switch behavior at a size or magnitude and carry "violates the no-thresholds rule; to be replaced".

| site | what is given up | why | trigger | test | COMPLEXITY row | status before | action |
|---|---|---|---|---|---|---|---|
| `zedc/src/store/presburger.rs` `Omega::run`, `Refusal::Growth` | systems the box neither empties nor satisfies after every row-keeping elimination: refused, "not decided" | Fourier–Motzkin growth, doubly exponential | 3+ variables, every elimination adds terms, rows not all `±x ± y + k` | `l01_38_presburger::omega::each_cause_of_a_refusal_has_its_own_message`, `checker::a_satisfiable_question_with_no_elimination_that_keeps_the_rows_is_refused`, `scaling::the_shifted_sparse_family_scales` | S18; Kept "Fourier–Motzkin pairs" | partial | completed |
| `presburger.rs` `search`, `Refusal::Shadows` | points that lie only in a splinter of a splinter: refused | nested splinters, exponential in variables | inexact elimination inside a splinter | `omega::each_cause_…`, `checker::a_question_whose_point_lies_past_one_splinter_is_rejected`, `scaling::pughs_example_in_a_chain_scales` | S18 | partial | completed |
| `presburger.rs` `pick`, `Refusal::Disjuncts` | formulas needing a disjunct choice undone: refused | NP-complete (3-coloring) | 2+ conflicting disjunctions | `omega::each_cause_…`, `omega::a_disjunct_refused_by_the_solver_is_reported_by_its_own_cause` | S16, S18 | partial | completed |
| `presburger.rs` `project` / `project_each` / `tighten` | gaps only a combination of disjuncts shows: set wider than the values | one projection per combination, exponential | 2+ disjunctions | `l01_38_presburger::random::random_tests_agree_with_the_interpreter` | S7, S16 | partial | completed |
| `presburger.rs` `hull_from` (violation) | bounds past `i64`: no bound | O(1) machine ends | magnitude past `i64` | `omega::a_bound_past_i64_is_searched_within_i64`, `omega::a_model_may_hold_values_past_128_bits` | none | no | new |
| `presburger.rs` `products` | nonlinear goals beyond products of premise pairs: `NotProved` | integer polynomial entailment undecidable | a product atom | `entailment::a_product_is_bounded_only_through_the_premises_on_its_factors` | none | partial | completed |
| `zedc/src/run.rs` `linear_questions` | functions whose question is refused: rejected | as the three refusals | a refused question | `checker::a_satisfiable_question_…`, `checker::a_question_whose_point_lies_past_one_splinter_is_rejected`, `checker::the_linear_questions_of_a_unit_scale` | S18 | partial | completed |
| `zedc/src/store/product.rs` `Lattice for` type `widen` | members gained in a loop: whole base type | no ascending chain condition | `next` adds a value in a base part | `l01_39_reduced_product::controls::a_type_widens_to_its_whole_base_type` | none | partial | completed |
| `product.rs` `Lattice for` type `narrow` | a smaller `next` in a part not held whole: `self` kept | infinite descending chains | a part neither empty nor whole | `controls::a_type_widens_to_its_whole_base_type` (its narrowing cases) | none | partial | completed |
| `product.rs` type facet listing | intervals wider than 2 × pieces: not listed into the type | listing cost in members | members > 2 × pieces (relative) | `controls::a_listed_set_is_enumerated_and_a_range_is_not` | none | partial | completed |
| `product.rs` `Scope::refusals` | refused narrowing: scope wider, silently | as the refusals | a refused question | no test yet | S18 | partial | completed |
| `product.rs` `Scope::enumerate` | constraints with 2+ open names, not shown to end, or not listed | product of members; halting | those three forms | `controls::enumeration_keeps_the_members_a_written_constraint_holds_at`, `controls::a_listed_set_is_enumerated_and_a_range_is_not` | none | partial | completed |
| `zedc/src/store/interval.rs` `End::from_i128` (violation) | ends past `i64`: infinity or rounded out | O(1) machine ends | magnitude past `i64` | `l01_25_preimage_catalog::entries::bounds_past_i64_keep_the_box`, `omega::a_bound_past_i64_is_searched_within_i64` | none | partial | completed |
| `interval.rs` `IntervalSet::widen` | loop bounds no literal names | infinite ascending chains | bound not a landmark | `m0_05_widening_and_iteration::widening::a_moved_endpoint_goes_to_the_next_landmark_or_infinity`, `widening::interval_widening_chains_stay_on_the_first_ends_and_the_landmarks` | S13 | partial | completed |
| `interval.rs` `IntervalSet::narrow` | tighter ends between old ends and landmarks: moved back out | infinite descending chains | a finite end of `next` with an old end or landmark beyond it | `widening::a_narrowing_keeps_old_ends_and_takes_a_bound_for_an_infinite_one`, `widening::interval_narrowing_chains_stay_on_the_first_ends_and_the_landmarks` | none (S13 is the widening phase) | partial | completed |
| `zedc/src/store/revision.rs` `map2` | gaps between merged pieces | k·m pieces, k^n along a chain | operands of several pieces (relative) | `l01_24_refinement_lattices::scaling::a_chain_of_operators_keeps_to_its_operands_pieces`, `scaling::an_image_holds_every_result_and_keeps_to_the_most_pieces_of_a_region`, `scaling::the_interval_operations_scale` | S4, S14 | partial | completed |
| `zedc/src/store/lattice.rs` `FiniteSet::widen` | all members, at a member not written | infinite ascending chains | non-landmark member | `widening::a_finite_set_widens_to_the_top_at_a_member_the_program_does_not_write` | S13 | partial | completed |
| `lattice.rs` `Congruence::narrow` | refinements to a larger modulus | infinite descending chains | narrowing below a non-top class | `widening::a_congruence_narrows_at_most_three_times` | none | partial | completed |
| `zedc/src/store/affine.rs` `Bounds::offset` (violation) | bounds past `i64`: dropped | as `End::from_i128` | magnitude past `i64` | `l01_24_refinement_lattices::bounds::an_offset_moves_every_member` | none | partial | completed |
| `affine.rs` `Bounds::leq` | order between bounds with different terms | a Presburger entailment | bounds with other terms | `bounds::the_order_is_sound_and_holds_of_meets_and_joins` | none | partial | completed |
| `affine.rs` `Bounds::widen` | symbolic bounds that appear in a loop | infinite ascending chains | a new bound in `next` | `bounds::widening_chains_are_finite`, `loops::a_counting_loop_keeps_its_symbolic_bound` | none | partial | completed |
| `affine.rs` `Bounds::narrow` | tighter symbolic bounds on a side that has some | infinite descending chains | a side of `self` with a symbolic bound | `loops::a_counting_loop_keeps_its_symbolic_bound`, `loops::a_loop_counting_down_keeps_its_symbolic_bound` (both fail when the narrowing takes no bounds; control run, not committed) | none | partial | completed |
| `zed/prelude/lattice.zed` `intervalWiden` | as `IntervalSet::widen` | as there | as there | as there | S13 | partial | completed |
| `lattice.zed` `intervalNarrow` | as `IntervalSet::narrow` | as there | as there | as there | none | partial | completed |
| `lattice.zed` `finiteSetWiden` | as `FiniteSet::widen` | as there | as there | as there | S13 | partial | completed |
| `lattice.zed` `congruenceNarrow` | as `Congruence::narrow` | as there | as there | as there | none | partial | completed |
| `zed/prelude/revision.zed` forward revision | as `map2` | as there | as there | as there | S4, S14 | partial | completed |
| `zedc/src/store/preimage.rs` `summon` landmark snapping | exactness of a call's preimage | one summary per interval, 2^k | argument ends not landmarks | `l01_25_preimage_catalog::scopes::one_function_called_twice_is_summarized_for_each_argument`, `scaling::nested_calls_are_summarized` | S13, S15 | no | new |
| `preimage.rs` `through`, `StopKind::Recursion` | transfer through recursion | unfolding need not end | a call cycle | `stops::a_call_that_never_returns_stops_where_it_calls_itself` | S12, S15 | partial | completed |
| `preimage.rs` `StopKind::Outside` at `fix`, `gen`, `fold` | transfer through loops: whole box, stop reported | unfolding need not end | a loop term between demand and input | `stops::a_term_outside_the_scalar_catalog_is_reported` (through `sum`); at a loop (TD-tests): `stops::a_fold_between_the_demand_and_an_input_stops_the_transfer`, `stops::a_gen_between_the_demand_and_an_input_stops_the_transfer`, `stops::a_fix_between_the_demand_and_an_input_stops_the_transfer` | none | partial | completed |
| `preimage.rs` `union` | unions that are not boxes: hull | box lists grow 2^k | boxes differing on 2+ inputs, neither within the other | `scopes::a_union_of_boxes_is_exact_when_it_is_a_box` | none | partial | completed |
| `preimage.rs` `project` (HC4) | relations between operands | exact region costs the points | no exact catalog entry | `entries::a_strict_disjunction_with_a_failing_side_is_necessary_only` | none | partial | completed |
| `preimage.rs` `mod_pre` | remainders in middle periods | pieces in width / c | more than two periods | `random::a_remainder_inverts_to_its_first_and_last_periods_and_one_piece_between` | none | partial | completed |
| `preimage.rs` `enumerate` | boxes not listed, 2+ multi-member axes, or not shown to end | product of axes; halting | those forms (relative) | `entries::a_listed_box_is_enumerated_and_a_range_is_not` | none | partial | completed |
| `preimage.rs` `witness` / `exact_preimage` | unbounded inputs, terms not shown to end: no answer | search need not end; undecidable | infinite end, recursion | `exact::a_witness_is_the_first_point_found_or_none`, `exact::exact_preimages_of_ranges` | S17 | partial | completed |
| `preimage.rs` `POWER_FACTORS` (violation) | powers of more than 64 equal factors: read as products | stated reason (`i64`) is invalid | more than 64 factors | `scopes::equal_factors_written_twice_are_read_as_a_square` (below the constant only) | none | partial | completed |
| `zedc/src/stage.rs` `ends` | terms that end but whose form does not show it | halting is undecidable | recursion, `fix`, `gen`, calls through parameters | `l01_28_staging::mix::a_term_whose_form_does_not_show_it_ends_is_left_to_run`, `mix::a_term_whose_form_shows_it_ends_is_built_with_no_fuel` | none | partial | completed |
| `zedc/src/check/mod.rs` `resolve` | literal classes fixed to int: calls at f64/rat rejected | 3^k elaborations | a literal joined a parameter's class | `l01_26_type_resolution::adoption::a_body_keeps_the_arrows_with_the_fewest_adoptions` | Kept "undeclared parameters (check), `apply`" | partial | completed |
| `zed-kernel/src/types.rs` `Type::values(cap)` (violation) | lists past `cap`: `None` | product of components | more than `cap` values | `l01_23_subtyping::scaling::listing_values_past_the_cap_stops_early` | none | partial | completed |
| `types.rs` `Type::listed` | types with more values than written: not finite | product of components | rows exceed component values (relative) | `scaling::listing_a_diagram_with_exponentially_many_paths_scales`, `trick::a_finite_domain_…` | none | partial | completed |
| `zed-kernel/src/types/empty.rs` module header | parts that need a multi-component split: inhabited | coNP-hard | emptiness needing a split in 2+ components | `l01_23_subtyping::scaling::a_type_not_proved_empty_promises_no_key` | K1, K2, Kept emptiness row | partial | completed |
| `zed-kernel/src/num.rs` `MAX_BITS` (violation) | integers past 2^20 bits: `Overflow` | result size exponential in exponent bits | result over 2^20 bits | `m0_09_kernel_evaluator::a_power_by_a_huge_exponent` | none | partial | completed |
| `zed-native/src/lib.rs` `isa`, `opt_level none` | optimized machine code | n^1.6 and n^1.4 passes | every function | (TD-tests) `l01_36_cranelift::levels`: programs at `opt_level` `none` and `speed` give the same values, counts and table rows; `zed-native` unit test `the_default_level_is_opt_level_none_with_a_single_pass_allocator` | Z15 | partial | completed |

## Discarded reports

| site | reason |
|---|---|
| `presburger.rs` `exact_step` / `inexact_step` fill rule | same tradeoff as Growth; documented there |
| `utvpi.rs` Bellman–Ford–Moore, O(V·E) | exact; superlinear cost, no input given up (S18 marks it open) |
| `bdd.rs` `Part::Expr` fallback | exact; the representation changes, the answers do not (K1) |
| `bdd.rs` `forced` / `settle` | exact; cost above O(n log n) is an open item (L1.23), no input given up |
| `bdd.rs` `Bdd::paths` | display only |
| `empty.rs` tuple SCC quadratic case | exact; cost only |
| `empty.rs` coinductive assumption | gives the correct answer for finite values; not a cost tradeoff |
| `cost.rs` frontier (F20) | exact; cost only |
| `provenance.rs` base (K25) | exact; cost only |
| `preimage.rs` in-place read of a call (S15 "still in place") | exact; cost only |
| `presburger.rs` `parts` splitting | exact; splits independent variables |
| `types/rec.rs` contractive, regular, monotone rules | language rules (DESIGN), not cost choices |
| `types.rs` `decidable` (`is` against a function type) | language rule: a function type cannot be tested at run time |
| `stage.rs` `trick` | language rule (split only on a finite domain). The arms are one per value in `passed` that lies in the domain, so they are bounded by the call sites whatever the domain (docs/thresholds.md section 7: "at most one per call site"), and `Domain::Ints(Some, Some)` is split however wide; keeping the general body for an unlisted domain saves no cost |
| `check/mod.rs` 733–740, a type variable not in the signature is dynamic | language rule |
| `text.rs` `StringTooLong` | a `usize` addressing limit, not a cost choice |
| `preimage.rs` string and foreign stops | missing catalog entries or no body to read, not a cost choice |
| `lattice.rs` `Card` join (hull) | a length is one interval of the nonnegative integers by design (sec:domains); the join drops gaps by the domain's definition, not to save cost. `Card`'s widen and narrow call the interval ones, documented there |
| `cell.rs` `Premise::Widened`; `revision.zed` HC4 "no bound" entries | bookkeeping; "no bound" is the exact preimage there |

## Counts

Reports 113; distinct sites 57 from the reports plus 5 found in verification, 62 in all; confirmed 43; already fully documented 0; newly documented 2; completed 41; discarded 19; size-switch violations 6 sites (4 rules: `i64` ends at three sites, `POWER_FACTORS`, `MAX_BITS`, `Type::values(cap)`); without tests 2, and `StopKind::Outside` has no test of a stop at `fix`, `gen` or `fold`. Since then TD-tests added the tests of `opt_level none` and of the loop stops, so 1 site is without tests: `Scope::refusals`.

## Findings

1. `product::Scope::refusals` is inserted into at three places (and unioned in `join`) and read nowhere, so a refused Presburger question widens the scope with no report. The `presburger.rs` module doc claimed the refusal was "reported by the checker"; that sentence is corrected in this commit. Fix: report the set as a warning at the scope, with a test.
2. The COMPLEXITY.md Kept row "emptiness and subtyping of tuple and morphism parts" and docs/thresholds.md section 9 call emptiness exact; `empty.rs` is sound and incomplete (the pigeonhole test). Fix: reword both.
3. docs/thresholds.md section 4 says splinters are gone; `search` still takes one level of splinters. Fix: reword.
4. Violations of the no-thresholds rule: `i64` interval ends (`End::from_i128`, `hull_from`, `Bounds::offset`), `POWER_FACTORS` (its stated reason is false, since `Int` is unbounded), `MAX_BITS`, `Type::values(cap)` (tests only).
5. No test: `Scope::refusals`, `zed-native` `opt_level none`; and no test of a preimage stop at `fix`, `gen` or `fold` (`StopKind::Outside`). Fix for the last: a `stops` test whose demand reads an input through a `fold`. Done in TD-tests for `opt_level none` and for stops at `fold`, `gen` and `fix`; `Scope::refusals` remains.
6. No COMPLEXITY.md row: `hull_from`, `products`, product type widening, type facet listing, product enumeration, `End::from_i128`, `Congruence::narrow`, `IntervalSet::narrow`, product type narrowing, the four `affine` sites, preimage `union`, `StopKind::Outside`, `project`, `mod_pre`, `enumerate`, `POWER_FACTORS`, `stage::ends`, `Type::values`, `Type::listed`, `MAX_BITS`.
7. Sites in files being rewritten on active branches, documented here on main: T6 (`types/empty.rs`, `types.rs`), ST (`store/product.rs`), S22a and T11-S22 (`store/preimage.rs`), and OSP-diag (`check/mod.rs` `resolve`, `run.rs` `linear_questions`, `zed-native/src/lib.rs` `isa`; from `git diff --stat main...wt/osp-diag`). These comments need carrying over when those branches merge.
