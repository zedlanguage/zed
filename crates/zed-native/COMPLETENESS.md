# Completeness: zed-native unit tests

Row TEST-complete-crates (author P189). The code these unit tests exercise is the runtime side
of the Cranelift backend of step L1.36: the hooks that generated code calls (`src/hooks.rs`),
and through them the tables (`src/tables.rs`), the code generator (`src/codegen.rs`) and the
run entry (`src/lib.rs`). Expected results come from DESIGN.md sec:reduction: a native run of a
program gives the kernel's value, or the kernel's error, whether release is fused or not, and
leaves no cell live. Every new test (in `src/hooks/completeness.rs`) runs its program natively
with fuse on and off and compares both with `zed_kernel::Evaluator::run` on the same term;
`hooks::tests::` names the older tests in `src/hooks.rs`.

Tested elsewhere, not by unit tests:

- `link.rs` and `exe.rs` (linked executables): `tests/steps/l01_36a_executables` and
  `tests/steps/l01_36b_link_identity`.
- `sources.rs` (lookup sources of an executable): `tests/steps/l01_36a_executables`.
- The step's own cases of the backend, with its own COMPLETENESS.md:
  `tests/steps/l01_36_cranelift` (`hooks.rs`, `checks.rs`, `ports.rs`, `decisions.rs`).
- The binary tests named in `Cargo.toml` (`zedc_binary`, `command_line_binary` and the rest).

llvm-cov lines (unit tests of the crate, benchmarks none):

| File | Before | After |
|---|---|---|
| `hooks.rs` | 384/749 (51.27%) | 710/749 (94.79%) |
| `codegen.rs` | 385/734 (52.45%) | 613/734 (83.51%) |
| `tables.rs` | 156/221 (70.59%) | 193/221 (87.33%) |
| `lib.rs` | 197/264 (74.62%) | 208/264 (78.79%) |
| `outcome.rs` | 20/22 (90.91%) | 21/22 (95.45%) |
| `exe.rs`, `link.rs`, `sources.rs` | 216/1196 | 216/1196 (tested by the step groups above) |

Lines of `hooks.rs` the unit tests leave unreached, and why:

- 590, 690, 703: `unreachable!` arms (only closures are entered; a branch or match hook is
  called only on its own node kind).
- 1131, 1168, 1172: `unreachable!` arms inside the older tests.
- 531-536: a port that is neither an input nor a source, where the kernel nevertheless reads it.
  A bug report: the kernel reads ports from the same `World`.
- 724-731: the kernel picks an arm for data that native matching did not match. A bug report:
  both apply the same patterns.
- 737-739, 815, 817: the kernel's match gives a value that is not the arm's tuple. The query's
  arms each give a one-element tuple, and data no arm matches is refused by the kernel as a bug
  of the checker (the `#oops` case below shows the refusal), so no correct program reaches them.
- 912-915: the result is the error word but no message was recorded. A bug report: every path
  that makes the error word records a message (`fail`).
- 899, 925, 927, 933-937: cells left live after the result is dropped. A bug report, reached
  only by a wrong plan that leaks; every run of the tests checks that it does not happen.
- 242: `rt_dec` of a word the heap refuses to release. A bug report: generated code releases only
  words it holds a reference to. The `inc` side is tested by
  `hooks::tests::an_inc_that_fails_*`.
- 373: the stability test of an atom's name word for a word that is neither a cell nor a
  constant. Names are strings, so such a word is refused before the shape is kept.

| Case | Test, or reason none is needed |
|---|---|
| Tuple of data made natively; empty tuple; tuple holding a function (kernel) | `a_tuple_of_data_is_made_natively_and_any_other_tuple_by_the_kernel` |
| Atom by name (fields sorted), by position, empty payload | `atoms_by_name_by_position_and_empty_are_made_without_the_kernel` |
| Atom shape kept across runs of one node (constant names) | `an_atom_of_constant_names_keeps_its_shape_across_runs_of_its_node` |
| Atom shape not kept when the name is made by the run | `an_atom_whose_name_is_made_by_the_run_is_not_kept_and_is_made_again` |
| Atom refused: repeated field name, name not a string, field name not a string, unequal counts; payload holding a function | `an_atom_the_native_rules_refuse_is_the_kernels_refusal` |
| `TupleGet` in range (shared element); past the end and below 0 give `#outOfBounds`; on a non-tuple refused | `a_tuple_element_is_shared_and_any_other_read_is_the_kernels` |
| `Concat` of two strings; of a string and an int | `strings_join_natively_and_any_other_concatenation_is_the_kernels` |
| `Concat` with a constant or a cell that is no string | `a_string_joined_to_a_constant_or_a_cell_that_is_no_string_is_refused` |
| `Len` of a string (scalars, not bytes); of a non-string | `a_string_length_is_counted_natively_and_any_other_length_is_the_kernels` |
| `Len` of 2^63 scalars, past `i64::MAX`: the kernel's big integer, one kernel call | `a_length_past_i64_max_is_the_kernels_big_integer` |
| `CodePoint` of one scalar; of two, of none, of an int | `a_code_point_of_one_scalar_is_read_natively_and_any_other_is_the_kernels` |
| `Read` of an input, of a lookup source (called and compared), of a missing port | `a_port_is_read_as_an_input_a_source_or_the_kernels_error` |
| A primitive (`PRIM` word) and a closure given to the kernel as values; wrong arity refused | `a_primitive_and_a_closure_given_to_the_kernel_are_its_function_terms` |
| Higher-order call entering a closure's code (`rt_callable`, `rt_entry`) | `a_function_value_called_twice_enters_its_code_by_its_registered_address` |
| Captured values read from a closure cell (`rt_cap`) | `a_closure_reads_its_captured_values_from_its_cell` |
| Float `^` through `rt_pow`: IEEE `pow`; negative base to a non-integer power gives the canonical NaN | `float_power_is_ieee_pow_with_the_canonical_nan` |
| `if` on a failure atom (pending result), an int, a string (refused), a lookup port | `a_condition_that_is_no_bool_is_the_kernels_decision` |
| `branch` given a `BOOL` word (generated code never does; direct call), no kernel call | `a_bool_given_to_the_branch_hook_picks_its_arm_without_the_kernel` |
| Native match: first matching arm, binders; owned scrutinee with an unused binder; borrowed scrutinee used after | `a_match_picks_the_first_arm_whose_pattern_the_data_matches` |
| Data no arm matches: the kernel's refusal | `data_no_arm_matches_is_the_kernels_failure`, `a_failure_no_arm_names_is_refused_as_the_kernel_refuses_it` |
| Function scrutinee: bound whole after a literal arm, wildcard, no arm | `a_function_scrutinee_is_matched_by_the_kernel_and_bound_whole` |
| A function as the program's result; a push to an output port (`STATE` word) | `a_function_result_is_refused_and_a_push_passes_the_ports_state` |
| `rt_error`: a borrowed argument to a consuming parameter (wrong plan, made by editing it) | `a_borrowed_argument_to_a_consuming_parameter_stops_at_the_call` |
| A borrowed scrutinee whose arm owns a binder (wrong plan, made by editing it) | `a_borrowed_scrutinee_whose_arm_owns_a_binder_is_refused` |
| `record_releases` and `counted` (feature `counts`): runs and released cells | `recorded_runs_list_the_cells_they_free` |
| Closures turned into terms, built once, cells reused | `hooks::tests::a_chain_of_closures_becomes_a_term` and the three tests after it |
| `inc` failing as the last write and before a `dec` | `hooks::tests::an_inc_that_fails_as_the_last_write_ends_the_run_with_its_error`, `hooks::tests::an_inc_that_fails_before_a_dec_is_the_error_and_the_dec_still_drops` |
| Pattern binder renaming | `hooks::tests::binders_of_a_nested_pattern_are_renamed_in_preorder`, `hooks::tests::patterns_that_bind_nothing_are_kept_and_atom_payloads_are_renamed` |
| Interaction with language features (units, unions, ports, staging and the rest) | None needed here: the backend runs kernel terms after checking; language-level programs run natively in `tests/steps/l01_36_cranelift` and the step groups after it |
