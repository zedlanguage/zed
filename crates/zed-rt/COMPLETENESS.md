# Completeness: zed-rt unit tests

Row TEST-complete-crates (author P189). The code these unit tests exercise is the runtime of
native code: the heap of counted cells (`src/heap.rs`), the limits of `main` (`src/limits.rs`),
the `Lines` ports (`src/ports.rs`) and the run's stack (`src/stack.rs`). Expected results come
from DESIGN.md (sec:kernel for values and equality, sec:memory and step L1.34 for counts and
releases, sec:ports for ports and limits), COMPLEXITY.md R10 for the stack, and the system's own
documentation (getrlimit(2), sigaction(2), signal(7), rt_sigqueueinfo(2)). Tests named
`heap::completeness::…` and so on are in `src/<module>/completeness.rs`; `heap::tests::…` and
the like name the older tests in each module.

llvm-cov lines (every unit test, each in its own process, the shared `scaling::` tests left
out; the crate linked statically so the counts are the instrumented code's):

| File | Before | After |
|---|---|---|
| `heap.rs` | 615/844 (72.87%) | 837/844 (99.17%) |
| `limits.rs` | 380/489 (77.71%) | 391/489 (79.96%) |
| `ports.rs` | 72/80 (90.00%) | 79/80 (98.75%) |
| `stack.rs` | 326/421 (77.43%) | 341/421 (81.00%) |

What the counts cannot show: a test of a limit runs its body in a child process
(`limits::tests::in_child`), and a child that ends as the runtime ends a run, by `_exit` in
`fault_exit` or by `SIGSEGV`, writes no profile. Those lines run in the tests below and are not
counted: `fault_exit`, `on_cpu`, `on_abort`, `stack_stop` and its callers (the guard-page stop
and the refused growth), `on_fault` passing a fault to a `SA_SIGINFO` action or to the default,
and the bodies of the children that stop. The lines left that no test reaches are listed at the
end with the reason.

## Heap

| Case | Test, or reason none is needed |
|---|---|
| `Word::int`, `state`, `err`; `scalar` of `int` at its ends, each `bool`, `f64` (`-0.0` apart from `0.0`); `None` for a string, a tuple, an atom, `f32`, a big integer, a `rat` | `heap::completeness::each_scalar_is_its_own_word_and_every_other_value_is_none` |
| Every NaN is one word (sec:kernel: NaN is canonical) | `heap::completeness::each_scalar_is_its_own_word_and_every_other_value_is_none` |
| `Word::cell` index and generation at 0, at their largest, and both at once | `heap::completeness::a_cell_word_holds_its_index_and_generation_at_their_ends` |
| `Parts` of 0 to 3 words, from a slice and from a vector; a pair held in place | `heap::completeness::a_pair_is_held_in_place_and_any_other_length_apart` |
| `Obj::parts` of a string, a tuple of 1 and 2, an atom, a kernel value, a closure with and without captures | `heap::completeness::the_parts_of_each_kind_of_cell` |
| `uncounted`: scalars take no entry; the empty tuple, a bare atom and an atom with an empty payload are entered once and are their entry when made again; a constant with parts is a new entry at each call; `value_ref` and `value` of each | `heap::completeness::the_table_enters_each_empty_tuple_and_bare_atom_once_and_other_constants_each_time`, `heap::tests::an_empty_payload_is_an_entry_apart_from_the_bare_atom` |
| `alloc`: a freed cell is taken again, last freed first, in its next generation; a new cell when none is free; `live`, `cell_slots`, the `peak` and `allocations` counts; an old word of a cell taken again is a freed word | `heap::completeness::a_freed_cell_is_taken_again_last_freed_first_in_its_next_generation` |
| A cell freed in its last generation is never taken again | `heap::tests::a_cell_freed_in_its_last_generation_is_not_taken_again` |
| `fresh` of every kind of value: scalars, the empty tuple and bare atoms (no cell), a string (empty and not ASCII), a big integer, a `rat`, an `f32`, a keypath, a family, tuples of 1 and 2, nested tuples holding constants, positional atoms of 1 and 2, a struct atom, nested atoms; `value` gives each back; dropping frees each cell | `heap::completeness::a_fresh_value_takes_a_cell_for_each_boxed_part_and_none_for_a_scalar_or_constant`, `heap::tests::a_pair_of_strings_is_three_cells_and_frees_whole` |
| A sequence shared in a value is one cell with a reference per holder, inside a tuple and inside an atom; equal sequences built apart are cells of their own | `heap::completeness::a_shared_sequence_is_one_cell_counted_once_per_holder` |
| `value` keeps what it read, so a second read reads one word (the `converted` count); an atom cell keeps its name and field names; a `fresh` value is kept from the start; a slot taken again holds the new value, not the kept one | `heap::completeness::a_cell_read_once_keeps_its_value_so_a_second_read_reads_one_word` |
| `value` of a closure, of a tuple holding a closure, of a `PRIM`, `SOURCE`, `STATE` or `ERR` word: errors `closure_as_data`, `not_data` | `heap::completeness::reading_a_word_that_is_no_data_value_is_a_bug_in_zedc` |
| `is_function` of a `PRIM`, a `SOURCE`, a closure, a string cell, a constant, an `INT`, `STATE` and `ERR`; of a freed closure (an error) | `heap::completeness::functions_are_closures_primitives_and_lookup_ports` |
| `capture` of each capture; of a cell that is no closure and of a scalar (a bug message); of a freed closure; dropping a closure drops its captures | `heap::completeness::a_capture_is_read_from_a_closure_and_from_nothing_else` |
| `inc`/`dec` of a word that is no cell (scalars, `STATE`, `ERR`, `PRIM`, a constant) writes nothing | `heap::completeness::a_count_write_on_a_word_that_is_no_cell_does_nothing` |
| The `shared` count: once per generation, not again at a count back at 1 and up again | `heap::completeness::a_cell_is_counted_shared_once_per_generation` |
| A count at its largest is an error at the `inc` (`full_count`) | `heap::tests::a_count_at_its_most_is_an_error_at_the_inc_itself` |
| A freed cell read, given a reference, or dropped, before and after its slot is taken again; the text of each `freed` message | `heap::completeness::each_use_of_a_freed_cell_names_what_the_code_did`, `heap::tests::a_drop_after_a_free_inside_a_nest_is_an_error_and_the_next_drop_starts_clean` |
| The text of `bug` | `heap::completeness::a_bug_message_says_the_fault_is_zedcs_and_names_the_place` |
| `dec` of an atom holding a closure holding a shared string: each part dropped once | `heap::completeness::dropping_a_closure_or_an_atom_drops_each_part_once`, `heap::tests::a_drop_uses_the_stack_only_to_free_a_cell_with_parts` |
| `release` keeping nothing: a cell held once (freed with no count write), a shared cell (one reference less), a scalar and a constant (nothing) | `heap::completeness::a_release_keeping_nothing_frees_a_cell_held_once_with_no_write_for_it` |
| `release` keeping the root: nothing written | `heap::completeness::a_release_keeping_the_whole_value_writes_nothing` |
| `release` keeping parts at depths 1 and 2, the scrutinee held once and shared: the counts written in each case | `heap::completeness::a_release_keeps_parts_at_every_depth_held_once_or_shared`, `heap::tests::fused_release_keeps_one_part_with_no_count_write` |
| `release` through a shared cell that reaches a constant | `heap::tests::a_shared_release_stops_at_a_constant_and_writes_no_count_for_it` |
| `release` with a kept path past a cell's parts, into a scalar, and of a freed scrutinee | `heap::completeness::a_kept_path_past_the_parts_of_a_cell_is_a_bug_in_zedc`, `heap::tests::a_path_into_a_scalar_is_an_error` |
| `matches` on a closure, a `PRIM` and a `SOURCE` against every pattern kind: only `_`, a name and a type of functions match | `heap::completeness::a_function_matches_only_a_wildcard_a_name_and_a_type_of_functions` |
| A literal pattern against every pair of 18 values (scalars, NaN, strings, big integer, `rat`, tuples of each length and part, atoms of each name, payload and length, struct atoms with more and fewer fields), each value as fresh cells and as a constant: matches exactly when equal (sec:kernel equality); a string of the same length that differs; a `STATE` word (`not_data`) | `heap::completeness::a_literal_pattern_matches_an_equal_value_of_every_kind_and_form`, `heap::tests::constants_match_without_cells` |
| A literal compared with a cell holding a closure (`closure_as_data`) | `heap::completeness::comparing_a_closure_with_a_literal_is_a_bug_in_zedc` |
| `#_` (any atom) against atoms of every payload and against every other kind, fresh and constant | `heap::completeness::any_atom_matches_each_atom_and_nothing_else` |
| A type pattern on a string cell (decided by its kind, not read; a literal type, read), a tuple (universe, element types, length), an atom (name, payload type), a big integer, a constant, scalars; a `STATE` word (`not_data`) | `heap::completeness::a_type_pattern_reads_a_cell_only_when_its_kind_alone_does_not_decide` |
| An atom pattern: name, payload length, bare against empty payload against one part, a struct payload, a tuple and a string; the binder's word and path | `heap::completeness::an_atom_pattern_needs_the_name_a_tuple_payload_of_its_length_and_its_bareness` |
| A field pattern: fields named out of order, a subset, a field's value that differs, a field the payload lacks, another name, a positional pattern on a struct payload, a field pattern on a tuple payload, fresh and constant | `heap::completeness::a_field_pattern_reads_named_fields_of_a_struct_payload_in_any_order` |
| A tuple pattern: length, the parts entered, a failure part-way (nodes entered so far), the empty tuple, a string, an atom and a scalar against a tuple pattern | `heap::completeness::a_tuple_pattern_needs_a_tuple_of_its_length_and_enters_each_part_it_reads` |
| Matching a constant again enters its parts once | `heap::completeness::matching_a_constant_again_enters_its_parts_once` |
| Nested patterns bind in preorder with their paths, fresh and constant | `heap::completeness::nested_patterns_bind_in_preorder_at_every_depth` |
| `survivors` (feature `counts`): grouped by kind (each kind name) and allocating node; a slot taken again takes the node allocating now; an `Int` in a kernel-value cell is `int` | `heap::completeness::survivors_group_live_cells_by_kind_and_allocating_node` |
| `record_releases`/`released`: nothing before asked, asking twice, order, strings' text, taken out of the record, still recording after | `heap::completeness::releases_are_recorded_in_order_only_once_asked_for` |

## Limits of `main`

| Case | Test, or reason none is needed |
|---|---|
| `write_bytes`: below 1 KiB, at and around each unit's start, tenths rounded down, `u64::MAX` | `limits::tests::a_size_is_written_with_its_binary_unit`, `limits::tests::a_size_at_a_unit_boundary_is_written_rounded_down` |
| `Line` drops what passes 512 bytes | `limits::tests::a_line_drops_what_passes_its_end` |
| `started` is before `boot_now` | `limits::tests::the_process_start_is_before_now` |
| `cpu:` past the limit stops with status 3 and its message; within it runs to the end | `limits::tests::processor_time_past_the_limit_stops_the_run_with_status_3`, `limits::tests::processor_time_within_the_limit_runs_to_the_end` |
| `@timeout`: past, within, and already passed at the start | `limits::tests::a_run_past_its_deadline_stops_with_status_3`, `limits::tests::a_run_within_its_deadline_runs_to_the_end`, `limits::tests::a_deadline_passed_before_the_run_stops_it_at_once` |
| `memory:` past the limit stops with status 3 (`on_abort`); the mappings the limit counts | `limits::tests::an_allocation_past_the_memory_limit_stops_the_run_with_status_3`, `limits::tests::which_mappings_the_limit_on_data_counts` |
| All three limits at once, in their order | `limits::tests::a_run_within_every_limit_runs_to_the_end` |
| `install` refused (SIGKILL, SIGSTOP): the `system` message | `limits::completeness::a_signal_the_system_lets_no_one_catch_is_refused_with_the_message_for_a_start` |
| `set_limit` refused at `getrlimit` (a resource out of range) | `limits::completeness::a_resource_the_system_does_not_have_is_refused_when_its_limit_is_read` |
| `set_limit`: a soft limit above the inherited hard one is lowered to it; a hard limit asked above the inherited one is the inherited one; a hard one below lowers the soft one; never raised again | `limits::completeness::a_soft_limit_above_the_hard_one_is_lowered_to_it_and_a_hard_one_never_raised` |
| `memory_limit` with no limit set | `limits::completeness::no_memory_limit_is_in_force_in_a_process_that_set_none` |
| `setrlimit` refused (lines 361-364) | None reachable: `set_limit` lowers the soft limit to the hard one and the hard one to the inherited one, so it never asks for what `setrlimit` refuses an unprivileged process |
| `timer_create`, `timer_settime`, `clock_gettime(CLOCK_BOOTTIME)` and `data_bytes` failing (lines 147, 184-187, 200-203, 269-272, 309-313) | None reachable: faults of the system, with arguments the calls accept on every Linux the runtime supports |
| A second `SIGXCPU` ignored; `on_cpu` with no limit text | None reachable on demand: the first `SIGXCPU` ends the process; `CPU_LIMIT` is set before the handler is installed |
| `fault_exit` when `write` fails | None needed: standard error closed leaves nothing to report to; the exit status 3 is still given |

## Ports

| Case | Test, or reason none is needed |
|---|---|
| `lines`: empty input, `\n`, `\r\n`, a lone `\r`, at the end and between lines, `\r\r`, `\n\r`, mixed, NUL and tab kept, non-ASCII UTF-8; keys from 0 in order | `ports::tests::lines_split_as_the_interpreter_does`, `ports::completeness::lines_are_keyed_from_0_in_order_and_each_line_end_ends_one_line` |
| A line not UTF-8 at the first key and at a later one, the others read, the port named | `ports::completeness::a_line_that_is_not_utf8_is_an_io_error_at_its_key_and_the_rest_are_read`, `ports::tests::lines_split_as_the_interpreter_does` |
| `write`: one string, the empty string, the empty family, keys given out of order, nested levels, an empty level, a read written back | `ports::completeness::a_push_writes_each_string_of_a_family_in_key_order_and_skips_empty_levels` |
| A string held in several blocks | `ports::completeness::a_string_held_in_several_blocks_is_written_whole_in_order` |
| A value that is no string, alone and inside a family (refused whole); the message's port, value and repair | `ports::completeness::a_push_of_a_value_that_is_no_string_is_refused_naming_the_port_and_the_value`, `ports::tests::lines_split_as_the_interpreter_does` |

## Stack

| Case | Test, or reason none is needed |
|---|---|
| A run on its own stack gives its result; the stack is as large as memory and swap; a panic reaches the caller | `stack::tests::a_run_is_on_its_own_stack_and_gives_its_result`, `stack::tests::the_stack_is_as_large_as_memory_and_swap`, `stack::tests::a_panic_on_the_stack_reaches_the_caller` |
| No limit, `RLIMIT_AS` too small: refused with `reserve` | `stack::tests::a_limited_address_space_refuses_the_reservation` |
| Under a limit: as large as the limit, grows by `GROW`, a second run no further | `stack::tests::a_stack_under_a_memory_limit_grows_as_the_run_reaches_it` |
| Growth refused by the limit: status 3, "needs 256 KiB more" | `stack::tests::a_stack_past_the_memory_limit_stops_the_run_with_status_3` |
| Several stacks, one dropped: each grows on its own | `stack::tests::stacks_under_a_memory_limit_grow_each_on_its_own` |
| A fault outside every stack, std's `SA_SIGINFO` action before | `stack::tests::a_fault_outside_the_stacks_ends_the_process_as_sigsegv_does` |
| The top step refused (`mprotect` of the first part): `too_small` | `stack::tests::a_memory_limit_too_small_for_the_stack_refuses_it` |
| A limit below `GROW`: `GROW.min(len - page)` takes the whole stack, writable at once; the run reaches the guard page and stops with "needs more, past" (the guard-page branch of `on_fault`) | `stack::completeness::a_stack_smaller_than_one_step_is_writable_whole_and_stops_at_its_guard_page` (data held before the limit is freed after it, so the system does not refuse first; the earlier test of the stop always reached the refusal) |
| A fault outside every stack with a plain action before (no `SA_SIGINFO`) | `stack::completeness::a_fault_outside_the_stacks_is_passed_to_a_plain_handler_before` |
| The same with `SIG_DFL` and `SIG_IGN` before: ends by `SIGSEGV` | `stack::completeness::a_fault_outside_the_stacks_with_the_default_or_ignored_before_ends_as_sigsegv_does` |
| A `SIGSEGV` at the lowest writable byte, the top byte, the byte above the stack, the byte below the guard page: passed on, no growth; one byte below the writable part: one step of growth | `stack::completeness::a_fault_on_a_writable_page_or_outside_the_stack_is_not_its_growth` |
| Under a limit, the reservation refused by `RLIMIT_AS` | `stack::completeness::a_limited_address_space_refuses_the_reservation_under_a_memory_limit` |
| Under a limit already full, the handler's stack refused: `too_small` | `stack::completeness::a_limit_already_full_refuses_the_handlers_stack` |
| The text of `unable`, `reserve` and `too_small` | `stack::completeness::each_refusal_to_set_up_the_stack_says_the_program_never_started_and_how_to_repair_it` |
| `sysconf`, `sysinfo` or the guard page's `mprotect` failing; the size past `usize`; `install` of `SIGSEGV` refused (lines 64-76, 107-111, 252, 305-306) | None reachable: faults of the system with arguments it accepts; memory and swap past 2^64 bytes cannot be |
| The retry of the lock-free push onto `GROWING` (line 324) | None reachable on demand: it runs only when two threads make stacks under a limit in the same instant; one run makes one stack |

## Lines no test reaches

| Lines | Reason |
|---|---|
| `heap.rs` 323, 600 | The `_` arm of `items_of` and of `table_parts`: their only callers pass a tuple or an atom (`fresh`'s stack, `shape` after its kind check) |
| `heap.rs` 827, 1034, 1107 | `unreachable!` arms, after a check that the cell is live or the entry is a tuple or an atom |
| `heap.rs` 1063, 1067 | `field_names` of a tuple: a field pattern checks the atom name first, which a tuple does not have |
| `ports.rs` 85 | The older test's `unreachable!` |
| `limits.rs`, `stack.rs` lines run only in a child that ends by `_exit` or `SIGSEGV` | Run by the tests named above, not counted (see the top) |

## Interaction with language features

The runtime is below the language: units, unions, staging and the rest reach it as values,
counts and limits already resolved by the compiler. Their language-level uses are tested in the
step groups that compile to native code (L1.34 counts, L1.36 ports, L2.x limits).
