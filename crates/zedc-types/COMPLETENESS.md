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
| Debug text: `debug_need`, `write_debug`, `debug_ty`, the `fmt` impls at 1209 and 3380, the hasher `write` at 800 | | Debug text is for developers and DESIGN gives none |
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
