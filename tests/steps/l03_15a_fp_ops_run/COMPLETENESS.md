# L3.15a completeness, plan row FP-ops-run: the standard operations on lists and maps

Code under test, piece 1: the quantifiers `.any(p)`, `.all(p)`, `.find(p)` (step L3.15a); the
folds `.count`, `.sum`, `.reduce(op)`, `.foldl(init, f)`, `.foldr(f, init)` on a level of any
keys (steps L3.2, L3.3); `.first` and `.last` (sec:corner_cases). From the checker to the run:
`crates/zedc-check/src/check/walk/fp_ops.rs` and `walk.rs` (`member_end`, `fold_dir_end`),
`crates/zedc-elab/src/elab/walk/fp_ops.rs` and `walk.rs` (`member_call`), and the kernel
primitives `firstEntry`, `lastEntry`, `entryAfter`, `entryBefore`, `first`, `last`
(`crates/zed-kernel/src/eval.rs`, codes 69 to 74).

Code under test, plan row FP-ops-scan: `x.scan(op)` (the prefix folds in key order, the keys of
`x` kept; step L5.3) and `x.chunkBy(f)` (the runs of equal `f` value, sec:type_language). The
checker's `scan_end` and `chunk_by_end` (`crates/zedc-check/src/check/walk/fp_ops.rs`, frames
`ScanFn` and `ChunkBy` in `walk.rs`) and the elaborator's `scan_term`, `scan_push` and
`chunk_by_term` (`crates/zedc-elab/src/elab/walk/fp_ops.rs`).

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
| `.scan` by `(+)`, `(*)`, `max`, `min`, `(&&)`, `(\|\|)` on lists and string-keyed maps; a single entry; `{}`; after `where` (keys kept, not renumbered); the last entry equals `.reduce(op)` (the law of step L5.3) | `cases::scan_and_chunk_by`, `cases::a_scan_keeps_the_keys_and_folds_each_prefix`; `runs` cases `scan_by_plus`, `scan_by_max`, `scan_of_a_map` |
| A float scan: entry `i` rounds as the canonical tree of sec:reduction item 1 over entries `0..=i`, so the last entry equals `x >< (+)` where a left fold differs | `cases::a_float_scan_rounds_each_prefix_as_its_fold_does` |
| `.chunkBy`: one run for a constant `f`, one run per entry for the identity on distinct values, runs split where a test changes, keys kept inside each run, string keys, `{}` and an empty `where`, an atom from `f` compared as data | `cases::scan_and_chunk_by`, `cases::chunk_by_splits_where_the_value_changes`; `runs` case `chunk_by_a_test` |
| Rejections of `scan` and `chunkBy` in the program's words: given nothing; `scan` by a non-associative operator or by a lambda (not built, REDUCE-by-function); `chunkBy` given a value that is not a function or a function of two arguments; either on a value with no entries | `cases::a_misused_scan_or_chunk_by_is_rejected_in_plain_words` |
| Scaling: the elaborated scan (fewer than 2n folds by the canonical tree) and chunkBy, O(n log n); both through `zedc run` on a keyed display | `bench::the_elaborated_scan_runs_in_n_log_n`, `bench::the_elaborated_chunk_by_runs_in_n_log_n`, `bench::scan_and_chunk_by_on_a_keyed_display_run_in_n_log_n` |

Code under test, piece 2 (plan row FP-ops-strings): `s.split(sep)`, `s.lines` and
`concat(pieces, sep: s)` of step L3.2, as the kernel primitives `split`, `lines` and `concat`
(`crates/zed-kernel/src/words.rs`, codes 75 to 77), resolved as prelude calls
(`zedc-resolve`, `STRING_CALLS`), checked by `strings_end` in
`crates/zedc-check/src/check/walk/fp_ops.rs` and elaborated by `strings_term` in
`crates/zedc-elab/src/elab/walk/fp_ops.rs`.

| Case | Covering test, or the reason none is needed |
|---|---|
| `split` keeps every piece, empty ones included: the empty string, two separators in a row, a separator at the end, an overlapping separator (`"aaa".split("aa")`), a separator longer than the text, the empty separator (one piece per `char32`, `"".split("")` is `[""]`), multibyte characters | `kernel::split_keeps_every_piece`; `cases::split_lines_and_concat`; `runs` cases `split_keeps_empty_pieces`, `split_by_the_empty_separator` |
| `lines` ends a line at `\n`, `\r\n` and a lone `\r`, `\r` then `\r\n`, `\n` then `\r`, no empty line after a line end at the end, `""` has no line | `kernel::lines_ends_a_line_at_each_line_end`; `cases::split_lines_and_concat`; `runs` cases `lines_at_each_line_end`, `count_of_lines` |
| `concat` in key order, keys not `0, 1, …`, `sep` given or not, empty family, one piece; the join law `concat(s.split(sep), sep: sep) == s` over a grid of texts and separators | `kernel::concat_joins_in_key_order_and_undoes_split`; `cases::split_lines_and_concat`; `runs` case `concat_without_sep` |
| A loose atom in an operand passes; a family entry that is not a string is refused | `kernel::string_functions_pass_atoms_and_refuse_other_entries` |
| `concat` of a family of families is rejected with the repair `xss >< (++)` | `cases::split_lines_and_concat` (its `saying` case) |
| The join law on generated strings of n and 8n characters, O(n); `lines` over n characters; `concat` of n pieces | `bench::split_then_concat_gives_the_text_back_in_linear_time`, `bench::lines_runs_in_linear_time`, `bench::concat_of_n_pieces_runs_in_linear_time` |
| The results are a rank of strings: a read by an integer key that misses is `#outOfBounds` | `cases::split_lines_and_concat`: `"a,b".split(",")[1] else "none"` is `b`, and reads at 2 and at -1 miss; a read with no `else` pushed to `m.stdout` is rejected as `String \| #outOfBounds`, seen 2026-11-16 |

## Not built yet, each with its plan row

The tests below fail until their row lands; they are the specification of those rows.

| Test | Words | Row |
|---|---|---|
| `cases::order_and_positional_selection` | `sort`, `asc`/`desc`, `.orderedValues`, `take`, `drop`, `slice`, `takeWhile`, `.minBy`, `.maxBy` | FP-ops-order |
| `cases::reverse_order_take_gives_the_last_entries` | the reverse of an order (step L5.1c) | FP-ops-order |
| `cases::concatenation_zip_and_its_law` | `++` on lists, `zip` | FP-ops-concat-zip |