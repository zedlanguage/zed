# Completeness: l01_19_whole_file_ports

Step L1.19 (DESIGN.md): whole-file ports. `m.stdin` is the family of its lines keyed from 0,
`m.stdout` and `m.stderr` take a string or a family of strings, `main::files` reads a path
whole, `main`'s result is the exit status, and a run can be recorded and replayed.
Plan row TEST-complete-ports (author P189). Coverage before and after is at the end.

## Reading standard input

| Case | Covering test | Or reason none is needed |
|---|---|---|
| Lines keyed from 0; `\n`, `\r\n` and lone `\r` each end a line; a last line needs no end | `lines.rs::lines_are_keyed_from_zero_and_crlf_is_one_line_end`, `lines.rs::each_line_end_ends_one_line`, `line_ends.rs::a_lone_cr_ends_a_line` | |
| A byte order mark is the first character of line 0 | `line_ends.rs::a_byte_order_mark_is_the_first_character_of_the_first_line` | |
| The keys of n lines are `0..<n`; an empty input has none | `lines.rs::the_keys_of_n_lines_are_0_to_n_minus_1`, `lines.rs::an_empty_input_has_no_keys` | |
| A line read inside string interpolation, over input and over no input | `combinations.rs::a_line_of_standard_input_is_read_in_each_position` (interpolated, interpolated_empty_input) | |
| A line read in an `if` condition, both branches | same test (condition_true, condition_false) | |
| The port bound to a name, then read | same test (bound_to_a_name) | |
| The port passed to a helper parameter of type `Lines` | same test (helper_parameter, helper_parameter_empty) | |
| A key computed from an expression | same test (key_computed); `lines.rs::a_computed_line_number_reads_that_line` | |
| One past the last key, a negative key, key 0 of no lines, key 0 of one line | `combinations.rs::a_key_outside_the_lines_gives_out_of_bounds` | |
| A key below -2^63 | same test (below_64_bits) | |
| A key of 2^63 or more, on `m.stdin` and `m.args`; 2^63 - 1; a key past 64 bits held in a name; a tuple index past 64 bits | `key_past_i64.rs` (three tests) | Fixed by row FAIL-ports-key-past-i64. |
| A line of 1-, 2-, 3- and 4-byte UTF-8, a NUL and a tab inside | `combinations.rs::a_line_is_utf8_text_or_io_error` | |
| A line that is not UTF-8: lone continuation byte, overlong NUL, surrogate, above U+10FFFF, cut short at the end | same test; `lines.rs::a_line_that_is_not_utf8_is_an_io_error_at_its_key` | |
| `len(m.stdin)` | | Left out: at layer L1 `len` takes `(String) -> int` only (DESIGN words table); the length of a family is a later layer. |
| `m.stdin.map(...)` | | Left out: `map` is a layer L3 word (DESIGN words table), although the text of step L1.19 uses `m.stdin.map(l -> l.upper)` as its example of a rejected push. The words table assigns the layer; the example is noted as an inconsistency in the row's report. |
| A program that never reads stdin runs with stdin closed | `blocking.rs::reading_standard_input_blocks_and_args_and_env_do_not` covers the reads | Closing stdin is a property of the built executable (l01_36 groups), not of the interpreter these tests run. |
| Reading stdin blocks; reads pass up through helpers and cycles | `blocking.rs` (all ten tests) | |

## Writing to `m.stdout` and `m.stderr`

| Case | Covering test | Or reason none is needed |
|---|---|---|
| A string holding a line end, the empty string, a non-ASCII string | `combinations.rs::a_pushed_value_is_written_as_lines_at_any_depth` | |
| A family of strings written one line per entry | `lines.rs::a_family_of_lines_is_written_one_line_per_entry` | |
| An empty level, flat or nested, writes no line | `writes.rs::an_empty_level_pushed_writes_no_line` | Checked through `join_lines`; a program cannot build such a family at L1, since map displays are a later form. |
| Pushed values given as map displays (`{}`, `{0 -> "a"}`, nested) | | Left out: zedc refuses map displays at L1 ("a map display is part of the Zed language, and this version of zedc does not compile it yet"). |
| Only strings are written; a number pushed is rejected with a repair | `writes.rs::only_strings_are_written_as_lines` | |
| A push whose value may hold a failure is rejected: a stdin line, to stderr, an argument, a variable, a file, a bare atom | `combinations.rs::a_push_whose_value_may_hold_a_failure_is_rejected_at_the_push` | |
| Two push sites on two branches; only the one that runs writes | `combinations.rs::of_two_push_sites_only_the_one_that_runs_writes`; `writes.rs::an_error_stops_the_wave_before_anything_is_written` | |
| One port pushed twice in a wave | `writes.rs::a_port_pushed_twice_in_one_wave_is_an_error` | |
| An error stops the wave before anything is written; the first failed write stops the rest | `writes.rs::an_error_stops_the_wave_before_anything_is_written`, `writes.rs::the_first_failed_write_aborts_the_rest` | |
| A port given to a helper, through a chain, by any path | `ports.rs` (all seven tests) | |
| A read of an output port, `len(m.stdout)` | `ports.rs::a_read_of_an_output_port_is_still_rejected` | |
| Numbers too large to build | `writes.rs::a_number_too_large_to_build_stops_the_run`, `writes.rs::printing_a_number_too_large_to_build_stops_the_run`, `writes.rs::a_number_computed_from_literals_is_rejected_before_the_run` | |

## `main::files`

| Case | Covering test | Or reason none is needed |
|---|---|---|
| A file read whole: empty file, last line without a line end | `combinations.rs::a_file_is_read_whole_in_each_position` | |
| A missing file, a directory | same test (missing_file, directory) | |
| A path read from stdin; the empty path | same test (path_from_standard_input, empty_path_from_standard_input) | |
| Read inside a helper | same test (read_in_a_helper); `outside.rs::a_function_other_than_main_reads_main_files` | |
| A config file read and a missing one falling back | `files.rs::a_config_file_is_read_and_a_missing_one_falls_back` | |
| A file that is not UTF-8 is `#ioError` with its fields | `files.rs::a_file_that_is_not_utf8_is_an_io_error`, `files.rs::a_failed_read_says_what_failed_where_and_why` | |
| Each path read once per wave | `files.rs::each_path_is_read_once_so_the_wave_sees_one_value` | |
| A byte order mark and each `\r\n` kept by a whole-file read | `line_ends.rs::a_files_read_keeps_the_byte_order_mark_and_each_crlf` | |
| `main::files` used outside `main`, in parentheses, in a unit without `main`, keyed writes | `outside.rs` (all nine tests) | |

## `main`'s header and result, records, annotations

| Case | Covering test | Or reason none is needed |
|---|---|---|
| The result is the exit status; a body that exports nothing exits 0; a bubbled failure exits 1 | `main_args.rs` (first three tests) | |
| A status not proved to be a byte is rejected with the menu | `main_args.rs::a_status_not_proved_to_be_a_byte_is_rejected_with_the_menu` | |
| Headers `main` may not have; one `MainArgs`; each field used only in its direction | `main_args.rs::a_header_main_may_not_have_is_rejected`, `files.rs::main_takes_one_main_args`, `main_args.rs::a_field_is_used_only_in_its_direction` | |
| Record and replay, round trip of any bytes, damaged or short records | `replay.rs` (all five tests), `sharing.rs` (all six tests) | |
| `@nonblocking`, the old word `blocking`, `signals` | `nonblocking.rs`, `blocking_word.rs`, `signals.rs` | Checked by those files; not ports of L1.19 proper. |
| Usage errors exit 2; a file zedc cannot use is named | `writes.rs::usage_errors_exit_2`, `writes.rs::a_file_zedc_cannot_use_is_named_with_the_reason`, `writes.rs::a_unit_whose_path_is_not_utf8_is_named_with_its_root` | |
| Large inputs, many lines, deep chains | `bench.rs`, `scaling.rs` | Benchmarks (P178). |

## Coverage before and after

Measured with `-C instrument-coverage` and `llvm-cov report` over the test targets of the eight
groups of the row (l01_19, l01_19a, l01_19b, l01_19c, s_01, l02_08, l02_08d, l07_03), benchmarks
not run. Missed lines, of the lines in each file:

| File | Lines | Missed before | Missed after |
|---|--:|--:|--:|
| crates/zedc/src/run.rs | 1045 | 164 | 164 |
| crates/zedc/src/build.rs | 273 | 6 | 6 |
| crates/zedc/src/pin.rs | 260 | 19 | 18 |
| crates/zedc/src/unit.rs | 885 | 306 | 300 |
| crates/zed-tools/src/catalog.rs | 622 | 48 | 42 |
| crates/zed-rt/src/ports.rs | 51 | 8 | 8 |
| crates/zedc-resolve/src/resolve.rs | 2177 | 1122 | 1122 |
| All files the targets link | 464565 | 396577 (14.63% covered) | 395116 (14.95% covered) |

Most of the lines still missed in run.rs and resolve.rs belong to forms of other steps; the
cases of these groups that reach them are listed above. The missing-file branches of pin.rs
were reached before only when the build directory held no file from an earlier run; the test
`l02_08_import_pinning/combinations.rs::the_pin_file_is_made_when_missing_and_never_written_over_a_change`
now reaches them on every run.
