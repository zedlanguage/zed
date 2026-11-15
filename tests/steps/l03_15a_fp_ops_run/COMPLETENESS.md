# L3.15a completeness, plan row FP-ops-run: the standard operations on lists and maps

Code under test, piece 1: the quantifiers `.any(p)`, `.all(p)`, `.find(p)` (step L3.15a); the
folds `.count`, `.sum`, `.reduce(op)`, `.foldl(init, f)`, `.foldr(f, init)` on a level of any
keys (steps L3.2, L3.3); `.first` and `.last` (sec:corner_cases). From the checker to the run:
`crates/zedc-check/src/check/walk/fp_ops.rs` and `walk.rs` (`member_end`, `fold_dir_end`),
`crates/zedc-elab/src/elab/walk/fp_ops.rs` and `walk.rs` (`member_call`), and the kernel
primitives `firstEntry`, `lastEntry`, `entryAfter`, `entryBefore`, `first`, `last`
(`crates/zed-kernel/src/eval.rs`, codes 69 to 74).

Each case of `runs.rs` is run three ways: by the M0 model (the zed-kernel reference evaluator on
the kernel term the spec defines the word by), by `zedc run`, and by an executable `zedc build`
makes. The three must print the same text. `cases.rs` runs each word through `zedc run` on more
inputs and checks the rejections; `kernel.rs` tests the six primitives on their own; `bench.rs`
(run with `--bench`) holds the scaling tests.

| Case | Covering test, or the reason none is needed |
|---|---|
| Each new primitive: the first and last entry, the entry after and before, at the ends, on an empty level, an atom key, a tuple entry, a loose atom family; `first`/`last` descending through levels | `kernel::*` (8 tests) |
| `.any`, `.all`, `.find` in key order, on lists and string-keyed maps, empty or not | `cases::quantifiers_decide_in_key_order`; `runs` cases `any_holds`, `all_fails`, `all_of_a_map`, `find_the_first_key`, `find_no_key` |
| The walk stops at the deciding entry: a failure of `p` past it is never met, a failure before it is the result (step L3.15a) | `cases::quantifiers_stop_at_the_deciding_entry` |
| Fixed-k cost (step L3.15a's own test): the deciding entry 10th at n and at 8n costs the same | `bench::a_quantifier_decided_at_a_fixed_entry_costs_the_same_at_8n` (hand-built term), `bench::the_elaborated_quantifier_decided_at_a_fixed_entry_costs_the_same_at_8n` (zedc's own term) |
| A quantifier that never decides walks all n entries in O(n log n) | `bench::a_quantifier_that_never_decides_walks_in_n_log_n` |
| `.count`, `.sum`, `.reduce((*))`, `.reduce(max)`, `.reduce((\|\|))` on lists and keyed maps; an empty display; float `.sum`; after `where` | `cases::folds_collapse_one_level`; `runs` cases `count_of_a_list`, `count_of_a_map`, `sum_of_a_list`, `sum_of_a_map`, `reduce_by_times`, `reduce_by_max` |
| `.foldl` and `.foldr` over keys that are not `0, 1, …` in turn, in key order, empty | `cases::folds_collapse_one_level`; `runs` cases `foldl_in_order`, `foldr_in_order`; `bench::a_foldl_walk_runs_in_n_log_n`, `bench::a_foldl_walk_takes_one_frame_per_entry` |
| `.first`, `.last`: the leaf at the least and greatest keypath; `#none` on an empty level | `cases::first_and_last_are_the_ends_in_key_order`; `runs` cases `first_of_a_list`, `last_of_a_list`; `bench::first_and_last_cost_the_same_at_8n` |
| Rejections in the program's words: a quantifier whose function gives no `bool`, given a value that is not a function, given nothing, or on a value with no entries; `.count`, `.last` given an argument; `.reduce` given nothing, by a non-associative operator, or by a lambda (not built, REDUCE-by-function); `.first` of a value with no entries | `cases::a_misused_quantifier_is_rejected_in_plain_words`, `cases::a_misused_fold_or_end_is_rejected_in_plain_words`, `cases::a_fold_by_a_non_associative_operator_is_rejected` |
| The words together on a string-keyed display of n entries, through `zedc run` | `bench::the_words_on_a_keyed_display_run_in_n_log_n` |
| A refusal of an entry step names it in words, not as code | `l01_18_scalar_interpreter::prim_names::a_refusal_names_each_primitive_as_the_program_writes_it` |

## Not built yet, each with its plan row

The tests below fail until their row lands; they are the specification of those rows.

| Test | Words | Row |
|---|---|---|
| `cases::split_lines_and_concat` | `split`, `lines`, `concat(…, sep:)` | FP-ops-strings |
| `cases::order_and_positional_selection` | `sort`, `asc`/`desc`, `.orderedValues`, `take`, `drop`, `slice`, `takeWhile`, `.minBy`, `.maxBy` | FP-ops-order |
| `cases::reverse_order_take_gives_the_last_entries` | the reverse of an order (step L5.1c) | FP-ops-order |
| `cases::concatenation_zip_and_its_law` | `++` on lists, `zip` | FP-ops-concat-zip |
| `cases::scan_and_chunk_by` | `scan`, `.chunkBy` | FP-ops-scan |
