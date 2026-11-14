# M0.10 completeness: the finite-model harness

Code under test: the harness of crate `zed-tests` (tests/src: `instances.rs` for the instances,
`check.rs` for checking an equation or a property, `seed.rs` for the random seed, `kernel.rs` for
the term builders) and, through it, the M0.9 evaluator (`zed_kernel::eval`) on every law of the
catalog; all against DESIGN.md step M0.10. Lines of the four harness files reached by this
group's tests (llvm-cov, without the `bench` module): 34 missed before, of 395, 25 after;
`instances.rs` 87.5% before, 100% after. The evaluator itself is the subject of step M0.9; this
group reaches 68% of eval.rs, the rest being the parts of the evaluator no law of the catalog
uses, such as ports and text.

| Case | Covering test, or the reason none is needed |
|---|---|
| Laws 1 to 10, each with the counterexample its side condition needs | the `law_01_*` to `law_10_*` tests of `laws_01_10.rs` |
| Laws 11 to 20, each with its counterexample | the `law_11_*` to `law_20_*` tests of `laws_11_20.rs` |
| Laws 21 to 28, each with its counterexample (sec:categories) | the `law_21_*` to `law_28_*` tests of `laws_21_28.rs` |
| Law 16 with loose atoms: the atom-strict class passes; `is`, `match` and `else` that turn the failure into a bool are refuted on `x div 0`; a predicate that tests the failure and returns it passes | `law_16_a_check_on_the_output_is_a_check_on_the_input`, `law_16_an_is_test_that_turns_the_failure_into_a_bool_is_refuted` (with the passing form), `law_16_an_else_…`, `law_16_a_match_…` |
| A law at the bound of 16 generations | `laws_11_20::law_14_holds_out_to_the_sixteenth_generation` (law 14's own test stops at 10) |
| Derived forms the laws use (map, scan, folds, flip, rank, refine, disjoint union, fresh names) | the tests of `derived.rs` |
| Witness bijectivity, affine packing under Euclidean `div`/`mod` with negative quotients, truncated division refuted | the tests of `witnesses.rs`, `row_major_packing_and_its_euclidean_unpacking_are_inverse_with_negative_rows`, `truncated_division_fails_the_inverse_law_on_negative_quotients` |
| Recursion: chaotic-order agreement, memo-pull equal to the wavefront, cycle stall, nested fixes | the tests of `recursion.rs` |
| Each recursion under the wavefront, memoized pull and eight seeded chaotic orders | `cases::every_recursion_runs_under_the_wavefront_pull_and_eight_chaotic_orders` |
| Smoke: keypath uniqueness; progress and preservation for reindex, discard, fold; confluence over arrival orders | the tests of `smoke.rs` (reindex's progress is the keypath test: a family or a collision, never a stuck term) |
| Smoke: confluence over schedules and the dependency theorem across schedules, cycles included | `recursion::every_schedule_counts_paths_on_every_three_node_graph_or_stalls_on_the_same_keys`, `every_schedule_agrees_on_random_graphs_with_dependencies_out_of_key_order`, `a_cycle_through_a_nested_fix_stalls_the_outer_entries_only` |
| Instances: `int[-8..=8]`, the nine floats bitwise, the budget of 4,096, 512 random ones, the one-level maps within the budget | `cases::the_instances_are_the_ones_design_names` |
| Sequences of length 4 in shortlex order: every one once, by length then alphabet, the empty bounds | `cases::shortlex_gives_every_sequence_once_by_length_then_alphabet` |
| Partial maps: each key absent or bound, once each, keys in order, no keys or no values | `cases::partial_maps_give_each_key_absent_or_bound_once` |
| The random generator: repeats from its seed, SplitMix64, `int` reaches both ends, `seq` every length, `fresh` repeats from the seed it returns | `cases::the_random_generator_repeats_from_its_seed_and_stays_in_range` |
| The harness reports a law that fails, with instance and both outcomes | `law_16_*` (`refuted_on_div_zero` checks the report in full); `check::tests::holds_names_the_failing_instance` |
| The harness reports a property that fails, and a counterexample not found | `cases::a_property_that_fails_is_reported_with_its_instance_and_reason`, `cases::a_counterexample_that_is_not_found_is_reported`; for an equation, `check::tests::refuted_insists_on_a_counterexample` (check.rs line 56) |
| Errors agree by kind, floats bitwise with NaN canonical | `check::tests::agreement_is_bitwise_on_floats_and_by_kind_on_errors` |
| seed.rs lines 23–26: `ZED_TEST_SEED` set, and set to text that is no number | None in this group: the variable is read by every random test of the binary at once, so setting it inside one test would change the others' seeds; it is set from the shell to repeat a run, and the parse is two library calls |
| kernel.rs `lines_of`, `beyond_machine` | None here: builders for other groups (texts of lines, the memory message), not used by any M0.10 law |
| Linear scaling of the recursion schedules and of fold and lattice ascents | the tests of `scaling.rs` at small sizes; large sizes in the `bench` module |
