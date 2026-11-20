# Completeness: crate zedc-types

Row TEST-complete-types (author P189). The crate holds `kernel_type.rs`, the kernel type a
written type denotes, and `ty.rs`, the checker's own type `Ty`: a kernel set beside tuples,
functions, type variables, atom payloads and the unknown, with union, meet, difference,
subtyping, the fit of an argument to a function's arrows, and the text of a type. Its unit
tests are the `tests` module at the end of `ty.rs` (65 tests, and 2 benchmarks in `ty/tests/bench.rs`,
run apart); the step tests reach it through the checker. The test binary lists those 67; the
own test of `tests/src/seed.rs`, which the crate compiles in by `#[path]`, runs in zed-tests
only (TEST-seed-test-once). Expected results are from DESIGN.md
L1.22, L1.23, sec:type_language, sec:type_resolution and sec:diagnostics. llvm-cov, as a floor
(regions; branch counts need a nightly compiler, so regions stand in for branches), over the
crate's unit tests and the tests of l01_22, l01_23, `deep_types` and `deep_search`:
`kernel_type.rs` 70.05% before, 96.77% after; `ty.rs` 87.83% before, 87.86% after. With
l01_24, l01_25, l01_26, l01_26a, l01_27 and l01_29 merged in, 241 lines of `ty.rs` are reached
by no test; they are listed per function in
`/home/luke/Work/wt/coverage/TEST-types-unreached-paths.txt` and classified below. This pass
added no unit test here: the cases of `kernel_type.rs` are tested through the language in
`tests/steps/l01_22_type_representation/complete.rs`, whose COMPLETENESS.md lists them. Row
TEST-types-unreached-paths, over the same ten test targets and the crate's unit tests: 7 of the
217 regions of `kernel_type.rs` were unreached (96.77%); a test of port names in an
intersection, a difference and the bounds of a bounded function type reaches 5 of them, and the
2 left (99.08%; lines 128 of 130) are the `unreachable!` arms below.

Second pass of row TEST-types-unreached-paths (2026-11-17), over the whole local suite
(`tools/run_tests.sh --cov`, every step test, unit test and probe, 1,759 profiles merged): 456
lines of `ty.rs` and 19 of `kernel_type.rs` were reached by no test, and 741 of zed-kernel
`types/**` (most in `types/empty.rs`, 369). The list, per function, is again in
`/home/luke/Work/wt/coverage/TEST-types-unreached-paths.txt`. 16 functions of the zed-kernel
unit binary and 36 of `libzed_kernel.so` had profile data that did not match, so some zed-kernel
lines in the list may be reached. The pass added the `Array` test below (lines 63-79 of
`kernel_type.rs`), pairs of function types with different numbers of parameters (l01_26
`deep_ops.rs`), and found and fixed two wrong refusals, each with a test that failed before:
FAIL-types-fn-arrows-bounded-variable (`through_fn` read a bounded variable only through a
function of one arrow) and FAIL-check-lambda-into-fn-union (a lambda in a slot of two function
types, or of one beside values, was typed alone). The rest of the list is row
TEST-types-unreached-paths-2.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| `kernel_type`: every arm of `kernel_form` that a resolved type can reach | `tests/steps/l01_22_type_representation/complete.rs` (see its COMPLETENESS.md) | |
| `kernel_form` on `Apply`, `AtomApply`, `Record` | | `unreachable!`, kept as a soundness guard (the match has no wildcard, so the arms stay). No Zed source reaches them: the resolver's type walk (`zedc_resolve::resolve`) visits every part of every written type and records each of these forms as one a later step compiles (`later`), except `AtomApply` in a printed type, which only `check/read.rs` `parse_type` reads and which never calls `kernel_type`; `resolve_text` fails when it records one; the checker (`check::walk::check_with`, which calls `bounds` and `declared_text`) runs only from `elab::elaborate_in`, and the `is` elaboration (`elab/state.rs` `ty`) only inside it; the compiler elaborates only in `front::checked` after `resolve_text` succeeds (on the recovery path of L1.29d too), and `mutate::mutants` only after `resolve` succeeds. Only a test calling `declared_text` on an unresolved type reaches them. Row TEST-types-unreached-paths |
| `kernel_form` on `Array`: `is` against `[T]` alone, in a union, in a tuple and in either bound of `L .. U -> V` | l01_22 `complete.rs` `is_rejects_a_list_type_and_a_bound_holding_one` | The row above listed `Array` as unreachable; the resolver passes a list type to the `is` elaboration, which refuses it here (LIST-type-written) |
| Carrier masks and bits | `ty.rs` `every_carrier_has_its_own_bit_and_the_numbers_are_the_number_bits` | |
| The index of arrows: the verdict of every set of arrows, on narrow and wide shapes; a refused arrow tried and dropped; a refusal with no arrow that fits | `ty.rs` `the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows` and the three after it | |
| The fit of an argument: small types, a bounded variable, functions in the results, each against a cover of their values | `ty.rs` `a_fit_of_small_types_is_a_cover_of_their_values` and the two after it | |
| Type variables: where a shared row's variables first appear, a variable in a payload inside a tuple, variables of types made after others are dropped | `ty.rs` `vars_in_gives_a_shared_row_s_variables_where_it_first_appears` and the two after it | |
| A function in a payload leaves no kernel type | `ty.rs` `a_function_in_a_payload_leaves_no_kernel_type` | |
| The index of shapes and of tuples: met, subtracted, compared by meets, holding a value, against every pair; the same whatever the hash and the order | `ty.rs` `shapes_found_by_the_index_are_those_of_the_rule_of_one_shape` to `filings_find_the_same_tuples_whatever_the_hash_and_the_order` | |
| Subtyping, meets and differences of `Ty` through programs: records, payloads, tuples with variables, refused buckets and their text | `tests/steps/l01_22_type_representation/kinds.rs`; `tests/steps/l01_23_subtyping/` | |
| Union, `is` narrowing, literals, fits and calls in the checker | `tests/steps/l01_26_type_resolution/`, `l01_26a_generic_literals/` (their COMPLETENESS.md) | |
| Loose atoms, `else` and `#errs` | `tests/steps/l01_27_absences/` | |
| Debug text: `write_debug`, `debug_ty`, the `fmt` impls at 1209 and 3380, the hasher `write` at 800 | | Debug text is for developers and DESIGN gives none |
| Debug text of a signature's needs (`debug_need`): every kind of need, holding a type, written as the derived `Debug` of `Need` writes it | l01_26 `deep_ops.rs` `a_signature_writes_each_need_as_the_derived_debug_of_the_need_writes_it` | It failed before TEST-types-unreached-paths-2: `Need::alike`, `Need::via`, `Component`'s site and `Remap`'s rank were left out |
| `Facts` `eq` and `hash` (2255, 2263) | | Constant bodies (`true`, nothing hashed): the facts are a cache that takes no part in equality |
| `Via` `eq`, `hash` and the loop of its `Drop`: two types that carry call chains compared, a shared chain dropped | `ty.rs` unit test `two_chains_of_calls_are_equal_link_by_link` | |
| `unreachable!` arms in `made_held` (2022, 2064) | | Unreachable by the match above each |
| Panic and assert arms inside the unit tests | | Run only when a test fails |
| `NeedKind::Order` in `map_tys`, `every_ty`, `into_tys` | l01_26 `held_functions.rs` `a_choice_between_generic_functions_with_needs_is_accepted` | The `Component` arm of `every_ty` (2937) stays unreached and is part of row TEST-types-unreached-paths |
| `errs_members`: an operand whose atoms already hold an `#errs` the program wrote, with a payload of one or two numbers, a function of one or two parameters, a prelude function, a generic function or a choice of two | l01_27 `merge.rs` `a_merge_with_an_errs_the_program_wrote_has_unknown_members` | The `None` return when the operand holds no `#errs` (3200) is a guard: its one caller tests `holds_errs` first |
| `fits_in` under `fits_sig_with`: a returned generic function with needs compared with each solved variable read as its type | l01_26 `held_functions.rs` `a_returned_generic_function_fits_a_function_result_by_its_needs` | Row FAIL-returned-generic-need-fit: the same function fits `(positional k: f64) -> f64` passed itself but not returned by another |
| `write_vars`: a named variable printed after `String` | l01_26 `signatures.rs` `a_named_variable_prints_on_its_side_of_string` | |
| `text_in_union`, `Binds::get_mut` and the two `IntoIterator` impls of `Binds` | | Removed by TEST-types-unreached-paths: no caller |
| About 40 early returns in single lines: `holds_nodes`, `rest`, `descend`, `outer`, `at`, `join_payloads`, `known_held`, `member`, `apart`, `value_class` (`f32`), `own_shape`, `near_form`, `payloads_in`, `diff`, `fns`, `tie`, `form`, `cut`, `verdict` (the unknown), `refused_in_group`, `meet_rest`, `contains_here` (a family), `meet` (the unknown), `tried`, `refused_cover`, `meet_within`, `keep_missing`, `bounds_hold`, `walk`, `parts`, `plan`, `family_parts`, `index_keeps` | | Each is a path a test should take or code to remove. Row TEST-types-unreached-paths-2 |
| `through_fn`: a bounded variable that only a function parameter holds, through a function of two arrows (`((x: T) -> int) & ((x: bool) -> int)`), under another name, with a bound that is wider, a result that differs, or a different number of arrows | l01_26 `deep_ops.rs` `a_bounded_variable_only_a_function_of_several_arrows_holds_fits_under_any_name` | Before FAIL-types-fn-arrows-bounded-variable, a function of two arrows returned `None` here and the same type written with `U` was refused |
| `through_fn`: two function types whose arrows take different numbers of parameters | l01_26 `deep_ops.rs`, the mismatched pairs | |
| A lambda in a slot of several function types (checker, `check/walk.rs` `lambda_takes`, `lambda_in_fns`): fitted to the one whose parameter names and number it matches, reordered by name; among several the names match, those its written parameter types take; where several remain with one kind per parameter, checked alone with those kinds; refused when its names match none | l01_26 `fits.rs` `a_lambda_in_a_union_slot_is_fitted_to_the_function_type_its_parameters_fit`, the test after it and `a_lambda_whose_names_fit_several_function_types_of_a_union_is_chosen_by_its_written_types`; `held_functions.rs` | |
| `Bound`: the shapes of a bucket pinned by bindings, filed in a compressed trie by their places and variables; insert, remove (a node left with no shape and one child is joined into its edge) and the members a row allows | `ty.rs` `bound_trie_agrees_with_a_map_of_paths` (4000 random steps against a map of paths, and the trie's invariants); l01_26 `bench/fits.rs` `shapes_pinned_at_n_different_sets_of_places_scale` | A shape moved by many separate grows is row TEST-types-bound-pin-moves-adversarial |

Row TEST-types-unreached-paths-2 (2026-11-17), from a fresh coverage run of the whole local
suite: llvm-cov `show` run on each object alone (each test binary, `libzedc_types` and
`libzed_kernel`), since one merged report drops the counts of every function whose profile
does not match. To find an input for a line, a probe build (never merged) recorded which
unreached lines each case of the random and recursive-system tests ran, over seeds 1 to 400.
What this pass did:

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| zed-kernel `types/empty.rs` (`nested_pieces` after `laminar_pieces` leaves a test undecided, `read_two_sat`'s unit clause, the two-literal meet asked twice, `swept`'s unordered rows, three branches of `affine_lists_empty`, four of `tuples`) and `types/bdd.rs` (a meet whose left keys are fewer): 49 lines | l01_23_subtyping `oracle.rs` `the_systems_reaching_rare_branches_both_ways_agree_with_the_oracle` (eleven recursive systems, each compared both ways and met, against the closure oracle) | |
| `empty/sweep.rs`: a list sweep's `Inhabited` witness for which `check_list_value` finds no row, so `list_sweep` declines; `empty.rs` prefix chains: the memo of the last miss read again, an emitting node's head evaluated on a memo miss, a partial negative group whose remaining head is cut to empty; `bdd.rs`: two sets of nodes ordered where the first side's subtree is the smaller | l01_23_groups_and_refusals `sweep_agreement.rs` `the_random_positive_chains_under_seed_153_agree_with_their_oracle` and the three tests after it (positive chains under seeds 153 and 339, R7 spine choices under 11, random links under 12; each case against its oracle) | A change to a generator moves these cases off the lines: to find seeds again, record the lines each case runs over seeds 1 to 400 |
| `laminar_pieces` on cells whose parents form a cycle | l01_23_groups_and_refusals `sweep_agreement.rs` `the_search_ends_when_cells_are_read_as_nested_in_a_cycle` | Found by this pass: the search did not end (seed 256, case 394 of the random chains). Inside the search a cell's test can read a type still being decided, so the cells `cons(int \ 1 \ 2, _)`, `cons(int \ 1, _)` and a third were read as each strictly inside the next, round a cycle, and the walk to the root never ended. Cells read so are now counted as crossing (the check is O(n), one visited mark per cell); the case is inhabited (`[3]`) and is decided so |
| The delegating `==`, orders and texts of the kernel's types and parts (`debug.rs` `fmt` of `Node`, `Row`, `Morphism`; `types.rs` `Arrow` `eq`, `Lits` `partial_cmp`, `Refusal` `Display`; `bdd.rs` `Part`, `Expr`, `Bdd`) | zed-kernel unit tests `types::tests::the_delegating_orders_and_texts_of_types_agree_with_what_they_delegate_to`, `types::bdd::tests::the_delegating_orders_and_texts_of_parts_agree_with_what_they_delegate_to` | |
| `fn_cover` returning `Cover::Together` | `ty.rs` unit test `a_fit_with_functions_in_the_results_has_each_verdict_on_built_cases`, the built Together case | |
| Failure branches of test helpers (`ty.rs` 20235-6, 22296, 22421, 22676, 23500; zed-kernel `bucket.rs` 403, `rec/group.rs` 864, `empty.rs` 14353) | | A panic or assertion message, run only when its test fails |
| Branches of test references and random draws not taken (`ty.rs` 19701, 22241, 23050, 23071-2, 23543) | | The paths of the product they stand for are tested by the built cases named in each test |

The rest of the list, most of it early returns in `ty.rs` and the zed-kernel functions
`find_prefix_chains`, `check_chain_witness`, `tuples_on`, `morphisms`, `print.rs` and `bes.rs`,
is row TEST-types-unreached-paths-3.

Row TEST-types-unreached-paths-3 (2026-11-18), from a coverage run of the whole local suite at
zed-impl 5461fb972: llvm-cov `show` on each of the 175 objects alone, as in the second pass;
the 20 executable tests that fail under the coverage build (their timing limits) were left
out. Line numbers below are those of `ty.rs` at 5461fb972. The zed-kernel half of the list is
in `crates/zed-kernel/COMPLETENESS.md`, section TEST-types-unreached-paths-3. What this pass did:

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| `Row::of_data`, `Row::made`, `Row::replaced`, the `data` and `checked` fields of the row data and `data()` (570-572, 590) | | Removed: no caller in the workspace; `check/walk.rs` builds its rows with `Row::new` and reads `data_checked` |
| `Sig::entries` on a function (3559) | | Every caller asks a family (`holds_fn_as_data` under `self.data`; the two reads of `Ty` after `filter(\|s\| s.data)`; `families` pushes only families). Now a `debug_assert!` |
| `Sig::entries`, a family met a second time on the stack after its memo was filled (3544) | `ty.rs` `a_family_held_in_two_entries_is_read_once_and_holds_what_it_holds`; l01_26 `held_functions.rs` `a_family_held_in_two_entries_of_another_is_data_exactly_when_its_entries_are` | |
| `Absorb::sig` and `write_parts` on a parameter that holds `_` beside `int` or a variable (3118-3123, 19015-19019) | `ty.rs` `a_signature_whose_parameter_holds_the_unknown_beside_int_prints_the_unknown_alone` | |
| A payload not known (`None`) against a known one: `==`, `union`, `union_all` (1194-1195, 2073) | `ty.rs` `a_payload_not_known_equals_only_one_not_known_and_stays_not_known_in_a_union` | |
| `holds_only_own_variables` over a row or payload shape shared by a parameter and the result (2464, 2469) | `ty.rs` `a_row_shared_by_a_parameter_and_the_result_is_read_once_for_the_variables_it_holds` | |
| `Replace::made_held`: a variable owned by two nested functions, hidden by the outer one and shown again (2812-2813; corrected by row TEST-types-unreached-paths-4: the inner one finds it hidden already, so it is never hidden twice) | `ty.rs` `a_variable_owned_by_two_nested_functions_is_replaced_in_neither` | |
| `with_held_fns` keeping a tuple or payload that holds no function, and a variable beside them (3007, 3018) | `ty.rs` `replacing_held_functions_keeps_the_parts_that_hold_none` | |
| `fits_sig` by the hull of the result ints, and `WrittenRange` ends (4537-4543, 13515-13519) | `ty.rs` `a_function_fits_where_its_result_range_lies_within_the_range_expected` | |
| `ParamRange::int` on component ranges, `ParamRange::parts` named, positional and on a type that is not one row (4574, 4596, 4611) | `ty.rs` `a_range_on_a_component_of_a_tuple_parameter_prints_in_its_place` | |
| `==` of rows, payload shapes and signatures past the recursion's stack (858, 957, 1051) | l01_26 `deep_types.rs` `types_deeper_than_the_recursion_s_stack_compare_by_their_contents` | |
| `FoldForm::what` for a scan, by `++` on strings (4133) | l03_02 `types.rs` `a_refused_scan_is_named_as_a_scan` | |
| `FoldForm::example` for a scan (4143) | | Guard: `scan_end` (`check/walk/fp_ops.rs`) refuses through `levels_of` every receiver that is not a family, with its own repair `[1, 2, 3].scan(...)`, and folds the receiver without its loose atoms, so the branch of `fold_level` that asks `example` is never reached by a scan; the same test checks that refusal |
| `Debug` of `Binds` and three other `Debug` texts (1455, 1498, 1841-1843, 5678-5680) | | Text for developers; DESIGN.md gives none to test against |
| `unreachable!` arms (2931-2932, 2973-2974) | | Guards: the match before them takes every case |
| `binding` of the `Absorb` and `HeldFns` walkers (3061-3063, 3222-3224) | | Guards: `binding` is called only from `rebuild` on a type's variables and from `sig_parts`, which these walkers reach only through types whose variables they keep (both return `None`, which keeps the variable) |
| `Absorb::remade` with nothing changed (3133) | | Guard (inferred): `may_absorb` is true only where the walk changes a part |
| `Facts` `eq` and `hash` (3592-3600) | | Recorded in the second pass |
| `FoldForm::Sum` in `fold_name` (4122) | | Guard: `reduce_by` is called only with `Reduce`, `Scan` and `Infix` (`check/walk.rs`) |
| `errs_members` on an operand with no `#errs` (5351) | | Guard: its caller checks `holds_errs` first |
| `Ty::verdict` with the unknown on the other side (12279) | | Reached only through `refused`, asked after `<:` failed, and every type fits `_` |
| Test and print code of the `tests` module (22618 on) | | Run only when a test fails, or a benchmark |

The rest, about 80 lines in `ty.rs` (in `Need::map_tys`, `site_mut`, `alike_at`, `Binds::remove`,
`Cx::unread`, `Holder::member`, `Choices::apart`, `Rest`, `Near::value_class` (`f32`),
`BoundNode::remove`, `Pins::own_shape`, `Comparing::fits`, `keep`, `components_in`, `replace`,
`failing_component`, `PlaceFns::below`, `Forms`, `lone_row`, `refused_in_group`, `meet_rest`,
`walk_held`, `contains_here`, `Pairs::tried`, `Cx::open`, `bound_in_fns`, `held_own`,
`repeated`, `equal_fits`, `uncovered`, `binds_nothing`, `Narrowing::new`, `Approx::made`,
`Domains`, `ArrowIndex::keep_missing`, the `Hash` of `Sig`, `Places::walk`, `Sig::digest`,
`first_seen`, `NameDigests::hash_ty`, `Walk::plan`, `Shared::of`, `walk_parts`, the arrow fit
loop at 20082, and `index_keeps`), listed with their lines in
`/home/luke/Work/wt/coverage/TEST-types-unreached-paths-3-left.txt`, is row
TEST-types-unreached-paths-4.

## Row TEST-types-unreached-paths-4

Line numbers are those of `ty.rs` at zed-impl 373e5d22a, from a new coverage run of the full
local suite there, which left 161 lines unreached; the tests named are in
`src/ty/tests/unreached4.rs`. 82 lines are settled below: 35 by tests, 9 by proofs at the
site, 38 as row TEST-types-unreached-paths-3 settled them (16 of these in the `tests` module). The other 79 are row TEST-types-unreached-paths-5 (see the end of this section).

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| `Same::rest`: functions nested past the comparison's stack that differ only innermost (931) | `deep_functions_that_differ_only_in_the_innermost_result_are_unequal` | |
| `Hash` of a `Width` past `i64` (4620) | `equal_wide_widths_hash_alike` | |
| `errs_members` on builds other than the family `errs` of (5357, 5360, 5363) | `errs_members_reads_only_the_family_errs_of_builds` | |
| `Binds::remove` of a binding, digest and index (5605) | `removing_a_binding_drops_it_from_the_digest_and_the_index` | |
| `Cx::unread` of a function read with a mask and a bound variable (6285, 6286) | `a_function_put_back_for_a_message_reads_its_masks_and_bound_variables` | |
| `member` of a rigid variable of one carrier (6540, 6541, 6561-6563) | `a_rigid_variable_is_a_member_where_its_one_carrier_is_filed` | |
| `some_value` of rigid strings, `f32`, shared rows and the unknown (6809, 6811, 6824, 6847) | `some_value_of_rigid_strings_and_f32_shared_rows_and_the_unknown` | |
| `Choices::apart` naming a field, and the bucket held anywhere (6722, 6729, 6732) | `the_reason_shapes_are_not_told_apart_names_fields_and_the_bucket_held_anywhere` | |
| `Rest::held` of parts that list no value (7228, 7255) | `a_rest_of_parts_that_list_no_value_is_held` | |
| `Near::value_class` of an `f32` (7427) | `the_class_of_an_f32_value_is_its_carrier` | |
| `Bound::lists` with nothing pinned, a member with no keyed variable, and an edge of two steps (8240, 8257, 8264, 8284, 8285) | `a_member_with_no_keyed_variable_reads_the_shapes_pinned_under_any_variable` | |
| `fits_written` and `fits_alone` giving a kept refusal again (8512, 8524, 8724) | `a_kept_verdict_on_functions_is_given_again_with_its_refusal` | |
| `kept_rows_in`: a kept refused no, and a component the search proves empty though it lists a value (8887, 8896, 8903) | `a_kept_verdict_on_rows_is_given_again_with_its_refusal` | |
| `FoldForm::fold_name` of `.sum` (4098) | `each_fold_is_named_as_it_is_written` | |
| `Replace::made_held`: a hidden variable not listed, or counted twice (2786, 2787) | | Guard, proof at the site: each `v` was counted on entering, signatures are left in reverse order, and `bound` leaves out a variable hidden already |
| `Need::site_mut` and `alike_at` on a need with no site (4862, 4874) | | Guard, proof at `site_mut`: their only callers, in zedc-check's `walk.rs`, read only needs `site` gives a site, and the two match the same kinds |
| `BoundNode::remove` of a path with no edge (8115) | | Guard, proof at the site: `Bound::pin` passes the path the shape was filed under |
| `Bound::pin`: a shape outside the bucket, and steps all on the path already (8155, 8163) | | Guard, proof at the site: `exact` is made for the bucket, and a place holds one variable, never one in `done` |
| `fits_alone` dropping names left in `made` (8706, 8707) | | Guard, proof at the site: `fits_in` drains `made` back to its mark before it returns, and the state starts with it empty |
| `Debug` texts (1429, 1472, 1815-1817, 5675-5677) | | As row TEST-types-unreached-paths-3: text for developers |
| `unreachable!` arms (2905-2906, 2947-2948) | | As row TEST-types-unreached-paths-3 |
| `errs_members` with no `#errs` (5348), `Ty::verdict` against the unknown (12503) | | As row TEST-types-unreached-paths-3 |
| `Absorb::remade` (3107), `binding` of two walkers (3196-3198), `Facts` `eq` and `hash` (3568-3576) | | As row TEST-types-unreached-paths-3 |
| Test code of the `tests` module (16 lines, 21343 on) | | As row TEST-types-unreached-paths-3: run only when a test fails, or a benchmark |

Left for row TEST-types-unreached-paths-5 (owner types9), each read in this row but not yet
settled: 9079 and 10105 (an empty list of shapes of an atom; `payloads` does not exclude
`Some([])`), 9216 (`near_form` on a `near` holding `_`), 10117, 10624, 10653, 10796-10798
(`Addressed for Row`, no caller found yet), 11577, 11621, 11728, 12543, 12645, 12646, 12896,
12901, 12914 (a row, shape or family met twice in one walk), 13006, 13302, 13527-13530, 14029,
14149, 14208, 14220, 15174, 15194, 15430, 15433, 15473, 15572, 15573, 15917, 16084, 16142, 16399,
16682, 16687, 16716, 16787, 16792, 17053, 17056, 17064, 17084, 17193, 17323, 17341, 17344-17348,
17354, 17359, 17497, 17750, 18201, 18301, 18575, 18580, 18945, 18946, 19746, 19747, 19922, 20021,
20022, 20064, 20065, 20078, 20079, 20139, 20265, 20287, 20347. Lines 16344-17107 were changed on
main by 97b5d1690 after 373e5d22a, so those in that range must be found again by their text.

## Row TEST-types-unreached-paths-5

Line numbers are those of `ty.rs` at zed-impl e94e784c1, where the 79 lines left by row
TEST-types-unreached-paths-4 (unreached in its coverage run of the full local suite) were
found again by their text. A line counted as reached by a test below was seen reached in a
coverage run of that test. The proofs this row adds as comments move the
later lines down. The tests named are in `src/ty/tests/unreached5.rs`; each was checked red
before green by breaking the line on purpose and reverting it. 39 lines are settled below:
31 by tests, 8 by proofs at the site. No wrong answer was found. The other 40 are row
TEST-types-unreached-paths-6 (see the end of this section).

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| `near_form` against a tuple that holds the unknown (9237) | `a_tuple_less_the_unknown_is_empty` | |
| `payloads_by_rest` and a payload check on an atom whose payload lists no shape (9100, 10126) | `atoms_with_a_payload_of_no_shape_are_within_any_payload` | |
| A payload check where a shape of one item finds no group of its size (10138) | `a_payload_of_one_item_is_in_no_payload_of_two` | |
| `diff` of a tuple and a kind-wide part, the rest kept outside the kernel type (10645) | `a_tuple_less_a_kind_wide_part_keeps_the_rest_outside_the_kernel_type` | |
| `Addressed for Shape` (10817-10819) | `a_payload_shape_at_two_depths_is_read_once` | |
| `tie` against a variable or the unknown (11598) | `a_check_against_a_variable_or_the_unknown_is_not_tied` | |
| `refused_in_group` with no exact kernel type (12564) | `a_refused_check_beside_a_variable_names_its_recursive_type` | |
| The meet of payloads where one side's payload is not known (12666, 12667) | `the_meet_with_a_payload_not_known_takes_the_listed_payloads` | |
| `walk_held`: a row, shape or family met twice (12917, 12922, 12935) | `a_node_met_twice_in_the_walk_of_held_functions_is_entered_once` | |
| `Ty::contains` of a family value (13027) | `a_family_value_is_in_a_type_with_a_family` | |
| `Pairs::tried` filing the holders of a tuple read for many values (13548-13551) | `a_tuple_read_for_many_values_is_filed` | |
| `Domains::no_fn_type` and the walk after it: a row or shape met twice (16734, 16739, 16839, 16844) | `a_node_met_twice_in_the_domain_of_a_meet_is_read_once` (a break makes it exponential; it then passes the 60 s limit) | |
| The names digest of a payload not known (19029, 19030) | `the_names_digest_tells_a_payload_not_known_from_no_payload` | |
| `Shared::of`: a row or function placed by an earlier print of the message (20148, 20149, 20162, 20163); `walk_parts` writing a hoisting function by its reference (20349) | `a_part_placed_by_an_earlier_print_of_a_message_is_written_by_its_reference` | |
| `diff`: payloads listed for an atom outside the type's own set (10674) | | Guard, proof at the site: `prune_payloads` removes such payloads, and skipping them is right in any case |
| `Forms::cut` of a form with no marks numbered (11749) | | Guard, proof at the site: forms are made only in `form_verdict` and `tie`, and both number the marks first |
| `fns_met` on a type with no functions (13323) | | Guard, proof at the site: its one caller is guarded by `both_fns` |
| `Sig::digest` hashing a signature with no digest (18385) | | Guard, proof at the site: `Members::push` computes every digest, and only `unwrap_to_change` drops one, on an owned signature |
| `write_parts` started on neither a type nor a signature (20006) | | Guard, proof at the site: `Ty::write`, `Ty::text_spelled` and `Sig::write` pass only those |
| `Shared::of` started on a row or another print (20105, 20106) | | Guard, proof at the site: its one caller is `write_parts` |
| `Shared::of` settling a part that is neither a row nor a held function (20223) | | Guard, proof at the site: only rows and functions are placed, and the start signature is never below a part |

Left for row TEST-types-unreached-paths-6, each read in this row but not yet settled (line
numbers at e94e784c1, with the function each is in): 11642 (`Forms::form`, a morphism in a
set; probably a guard, not proved), 14050 (`Cx::open`, mask 0), 14170 (`bound_in_fns`),
14229, 14241 (`held_own`), 15195, 15215 (`repeated`), 15451, 15454 (`cover`, an equal
arrow), 15494 (`equal_fits`; a test built from equal arrows did not reach it, since `Cx::open`
renames the arrows' variables), 15593, 15594 (`refused_cover`, a variable no argument gives
values of), 15938 (`met`), 16105, 16163 (`Narrowing::meet_within`), 16425 (`Approx::made`),
16768 (`Domains::kernel_of`), 17126, 17129, 17148, 17168 (`Domains::fns_apart`), 17277
(`keys_apart`), 17407, 17425, 17428-17432, 17438, 17443 (`Domains::inhabited_fn`), 17581
(`Domains::meet`), 17834 (`ArrowIndex::keep_missing`), 18285 (`Places::walk`), 18659, 18664
(`Sig::first_seen`, a node met twice), 19830, 19831 (`Walk::plan`, a union already taken
out), 20371 (`walk_parts`, `Print::Found` not entered), 20431 (`walk_parts`, the swap of
union names, which needs nested hoisting unions with bounded variables).

## Row TEST-types-unreached-paths-6

Line numbers are those of `ty.rs` at zed-impl e94e784c1, the 40 lines left by row
TEST-types-unreached-paths-5, found again on main by their text. The tests named are in
`src/ty/tests/unreached6.rs`, with one program test in
`tests/steps/l01_26_type_resolution/function_variance.rs`; each was checked red before green by
breaking the line on purpose and reverting it. 31 lines are settled by tests, 9 by proofs at
the site. Three wrong answers were found and fixed, each with a test that was red before the
fix (listed after the table).

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| `Forms::form`: a component with no form leaves the tuple with none (11642) | `a_tuple_with_a_component_of_no_form_is_compared_by_parts` | |
| `Cx::bound_in_fns`: a variable of one carrier read as its mask (14170) | `a_variable_of_one_carrier_held_in_a_result_function_is_its_carrier` | |
| `held_own` (was `held_bounded`): an own variable a parameter function holds (14241) | `a_variable_in_a_parameter_function_is_bound_through_it`; `a_generic_function_with_its_variable_in_a_parameter_function_is_passed_at_an_instance` (program test) | |
| `repeated`: a row met many times walked twice (15195) | `a_row_met_many_times_in_the_parameters_is_walked_twice` (a break makes it exponential; it then passes the 60 s limit) | |
| `repeated`: a variable read as a rigid variable in a parameter function (15215) | `a_variable_of_one_carrier_in_a_parameter_function_is_not_repeated` | |
| `refused_cover`: a variable no argument gives values of (15593, 15594) | `a_variable_no_argument_gives_is_named_as_written` | |
| `meet_within` given no results (16105) | `an_intersection_of_no_results_is_within_nothing` | |
| `Approx::made`: a payload shape with fields, read from below (16425) | `a_payload_with_fields_is_empty_from_below` | |
| `Domains::kernel_of` of a type holding a function (16768) | `meets_of_functions_of_function_parameters` (reached; a wrong value here is seen only through 17126, which is checked) | |
| `Domains::fns_apart`: a value type with no kernel type (17126), an empty meet of the values (17129) | `meets_of_functions_of_function_parameters` (17129 reached only: a break there gives the same answer, as the early return skips a `g` that holds no function) | |
| `Domains::fns_apart` case (iii): exact and partial arrows, the function over all of them (17148) | `a_function_type_of_exact_and_partial_arrows_holds_the_function_over_all_of_them` | |
| `Domains::fns_apart`: a function type not read through its arrows (17168) | `meets_of_functions_of_function_parameters` | |
| `Domains::keys_apart`: parameter types with no common value (17277) | `meets_of_functions_of_function_parameters` | |
| `Domains::inhabited_fn`: a signature met twice (17407) | `inhabited_fn_enters_a_signature_met_twice_once` (a break makes it exponential; it then passes the 60 s limit) | |
| `Domains::inhabited_fn`: value types that differ (17425), a value type of no function (17428-17432), function types alone (17443) | `inhabited_fn_reads_each_kind_of_value_type` | |
| `Domains::meet`: partial arrows taking nothing of an exact arrow (17581) | `partial_arrows_taking_nothing_of_the_exact_arrow_leave_no_function` | |
| `Places::walk`: a parameter function that owns a variable of the same name (18285) | `a_variable_a_parameter_function_owns_is_another_variable` | |
| `Sig::first_seen`: a row or shape met twice (18659, 18664) | `first_seen_enters_a_row_or_shape_met_twice_once` (a break makes it exponential; it then passes the 60 s limit) | |
| `Walk::plan`: a union already taken out (19830, 19831) | `the_unknown_printed_for_a_union_and_a_found_result` | |
| `walk_parts`: `Print::Found` not entered (20371) | `the_unknown_printed_for_a_union_and_a_found_result` | |
| `walk_parts`: the larger set of union names kept (20431) | `names_of_a_larger_inner_union_are_kept_by_the_union_around_it` | |
| `Cx::open`: a bound of mask 0 (14050) | | Guard, proof at the site: no bound is 0; a written bound names carriers, and the merge of classes and `restrict` refuse to make 0 |
| `held_own` where `b` may bind no own variable (14229) | | Guard, proof at the site: each caller returns first where `b.binds_own()` is false |
| `cover`: an equal arrow that `equal_fits` refuses (15451, 15454) | | Guard, proof at the site: `equal_fits` is true at every equal arrow; the proof is at `equal_fits` |
| `equal_fits`: an equal arrow holding a bounded variable (15494) | | Guard, proof at the site: `Cx::open` reads or renames each bounded own variable, so no arrow of `q` as read holds one (one step inferred, stated there) |
| `met` on an arrow of `q` with a parameter type proved empty (15938) | | Guard, proof at the site: `covers` filters such arrows out before `cover` |
| `meet_within`: no kernel to reduce (16163) | | Guard, proof at the site: `results` is not empty there, and one kernel is pushed per result |
| `Domains::inhabited_fn`: no arrow whose value type is not the unknown (17438) | | Guard, proof at the site: `v` is such a value type, so `find` gives `Some` |
| `ArrowIndex::keep_missing`: an arrow repeated in `l` (17834) | | Guard, proof at the site: `offered_keys` gives distinct keys, so `ArrowIndex::new` lists each arrow once per key |

The wrong answers found and fixed:

- An own variable with no bound that a function in the parameters holds was compared as
  itself, which nothing binds, so a generic function did not fit the type of its instance:
  `g(h: (x: T) -> int, y: T) = h(x: y)` was refused as `(h: (x: int) -> int, y: int) -> int`
  (a wrong no). `Cx::held_own` now gives the unbounded own variables too (`Binds::free`), and
  `outer_or_class` adds the class variables the checker writes for a generic function's
  variable. Tests: `a_variable_in_a_parameter_function_is_bound_through_it` and the program
  test above.
- `permitted` skipped its pass where an arrow held an own variable only inside a function in its
  parameters, so `((x0: int) -> int) & ((x0: (x: T) -> int) -> int)` was within `(x0: int) ->
  int` (a wrong yes). Test: `an_arrow_holding_a_variable_in_a_function_has_its_permission_checked`.
- The message of `refused_cover` named a renamed variable (`B'1`) and printed the arrow from the
  renamed copy, with `B` as an unbounded `T`. It now quotes the signature as written. Test:
  `a_variable_no_argument_gives_is_named_as_written`.

Two claims of row TEST-types-unreached-paths-5 were checked again. The guard at `Forms::cut`
(11749) holds: forms are made only in `form_verdict` and `tie`, and both number the marks first.
11642 is not a guard: `a_tuple_with_a_component_of_no_form_is_compared_by_parts` reaches it, and
a break there turns the test red.
