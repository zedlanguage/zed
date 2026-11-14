# l01_36_cranelift: completeness (step L1.36, codegen via Cranelift)

The code under test is `crates/zed-native` (the tables, the generator `codegen.rs`, the hooks of
the runtime, legalization for this back end, the object writer) and the heap of `crates/zed-rt`.
Each value native code gives is checked against the kernel, and its counts against the counting
machine of step L1.34. Each row is a case; the second column names the test that covers it, or
says why no test is needed. Files are named without `.rs`.

| Case | Covering test, or reason none is needed |
|---|---|
| **Scalars inline** | |
| int `+ - * neg`, the overflow and `i64::MIN` edges going to the runtime | `scalars::every_edge_case_gives_the_kernels_value`, `scalars::an_overflow_goes_to_the_runtime_once`, `mul_edges::*` |
| float arithmetic, NaN, the signed zeros, infinities | `scalars::*`, `mul_edges::sampled_float_pairs_over_every_class_agree_bit_for_bit` |
| comparisons `< <= == !=`, `>` and `>=` swapped by legalization | `scalars::comparisons_and_branches_on_scalars_call_no_kernel`, `legalize::*` |
| bool `and or not`; mixed int and float, bool and int: the kernel | `scalars::every_edge_case_gives_the_kernels_value` |
| `min`, `max`, `clamp` on floats, ints and mixed: IEEE minimum and maximum | `minmax::*` |
| float `^` with NaN operands | `pow_nan::*` |
| `sqrt` of `f64` (square, 2, -0.0, a negative, infinity) inline; of `f32` by the kernel | `inline_prims::sqrt_fma_and_code_point_run_inline_on_their_own_inputs_and_give_the_kernels_value` |
| `fma` of three `f64` (one rounding, inf times 0) inline; an `f32` operand by the kernel | `inline_prims::*` |
| code point of a one-scalar string (1, 2 and 4 bytes, a constant, a fresh cell, read twice) inline; of two scalars, the empty string, a join, an int by the kernel | `inline_prims::*` |
| **Strings** | |
| concatenation, sharing, `len` in characters, many appends, handing a string to the kernel | `strings::*`, `string_scaling::*` |
| lengths past `2^62`, `2^63` (a big integer), `2^64` (refused), the empty string doubled | `string_length::*` |
| **Values in the heap** | |
| every shape (tuple, atom, string, closure, empty tuple, bare atom) entering and leaving the heap | `deep_heap::each_shape_of_value_enters_and_leaves_the_heap`, `deep_heap::an_empty_tuple_and_a_bare_atom_are_uncounted_at_any_depth` |
| atoms with named and positional fields, an empty payload, the kernel's refusals of a wrong payload | `hooks::*` |
| `is T` answered from a cell's kind | `kinds::*` |
| a value the kernel hands back, shared parts one cell | `shared_values::*` |
| a cell read once for the kernel, freed and taken again, changed between runs | `kernel_inputs::*` |
| constants: a part read once, a binder below or beside a constant, the uncounted table | `constants::*`, `reuse::*`, `table::*` |
| a closure's term built once however many closures share it | `shared_closures::*` |
| a word kept past the free of its cell; a freed cell below a value; a state word | `reuse::a_word_kept_past_the_free_of_its_cell_is_reported_after_the_cell_is_taken_again`, `deep_heap::a_freed_cell_below_a_value_is_reported`, `deep_heap::a_state_word_is_not_data` |
| release: a value freed at its last use, a tuple before its parts, the order counts reach zero | `release_order::*`, `drops::*` |
| **Decisions** | |
| `if` on a bool inline; on a lookup port | `scalars::comparisons_and_branches_on_scalars_call_no_kernel`, `hooks::a_lookup_port_as_a_condition_is_read` |
| `if` on a failure atom, its arms borrowing or owning a cell, at the root and in a lambda body: the atom | `decisions::native_code_gives_the_kernels_outcome_on_failures_ports_and_unmatched_values` |
| `if` on a cell | `scaling::a_condition_that_is_a_cell_fails_as_the_machine_fails` |
| `match` patterns: tuple, named fields, positional atom, literal, `is`, wildcard, deep, records in pattern order | `deep_heap::*`, `reuse::a_literal_pattern_*`, `hooks::*`, `kept_binders::*` |
| `match` of an int, a string, an atom, a struct no arm of which matches: the kernel's stop | `decisions::*` |
| a struct matched by its field | `decisions::*` |
| `match` of a function: a binder, unused, under `is` and `_`, inside a tuple (the kernel's error) | `function_binders::*`, `decisions::*` |
| a binder its arm does not use | `hooks::a_binder_the_arm_does_not_use_changes_no_count` |
| **Calls** | |
| a resolved call; through a capture; a curried call; a pushing function called twice | `scaling::a_curried_sum_runs`, `checks::*`, `scalars::a_function_that_pushes_and_is_called_twice_runs_natively` |
| a call deeper than a thread's stack | `deep_calls::a_list_built_by_nested_calls_runs_natively_as_in_the_kernel` (small depths; deep ones in `bench`) |
| an argument passed owned to a body that borrows it, freed after the call | `checks::an_argument_passed_owned_to_a_body_that_borrows_it_is_freed_after_the_call` |
| **Ports** | |
| lines split and joined as the interpreter does | `ports::*` |
| a port read once, read twice, and one the run was not given | `decisions::*`, `deep_heap::a_list_read_from_a_port_runs_natively` |
| **Wrong plans** | |
| a missed drop, a missing dup, a borrowed argument to a consuming body, a missing result dup | `checks::*` |
| no plan at all; a call resolved to a region that is no lambda, at the root and inside an arm | `checks::a_plan_with_no_regions_or_a_call_to_no_lambda_is_refused_before_code_is_made` |
| a borrowed scrutinee whose arm owns a binder | `checks::a_borrowed_scrutinee_whose_arm_owns_a_binder_is_refused_at_the_match` |
| a wrong plan deep in the term names its path | `scaling::a_wrong_plan_deep_in_the_term_names_the_path` |
| `>` or `>=` not expanded by legalization | `legalize::each_back_end_refuses_what_it_declared_expanded_by_name` |
| **Whole programs, levels, objects** | |
| every corpus row natively with the machine's counts | `corpus::every_row_passes_natively_with_the_machines_counts` |
| Cranelift `opt_level` none against speed | `levels::*`, `mul_edges::the_optimizing_level_agrees_on_a_sample` |
| the object file reproducible and naming its symbols | `aot::*`, `scaling::each_deep_shape_compiles_to_an_object_file` |
| **Checks no program reaches** | |
| a loop body whose results do not match its ports (`codegen.rs`, the `states` check) | none: lowering makes every loop region; no loop compiles at L1 (`loop` is refused by the front end), so no graph reaches it; it is a check on zedc's own graph |
| `rt_inc` or `rt_dec` on a word the heap refuses | none: generated code incs and decs only words the plan holds, and a freed word is reported earlier, at the read (`reuse::a_word_kept_past_*`) (inferred from the plan checks) |
| a `match` no pattern of which matches natively and the kernel picks an arm | none: the native matcher and the kernel's share the patterns' meaning (`zed_kernel::paths`); this check reports a disagreement, which would be a zedc bug (inferred) |
| the result is the error word with no message recorded | none: every hook that returns the error word records its message first (inferred from `fail` in `hooks.rs`) |
| cells allocated outside every node, in the leak report | none: every allocation in generated code is made by a node; only the counts build of the report shows it (inferred) |
| **Scaling** | in `bench` (deep values, wide functions, strings, tables): not correctness tests (P178) |
