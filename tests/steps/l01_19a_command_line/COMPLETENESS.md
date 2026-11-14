# Completeness: l01_19a_command_line

Step L1.19a (DESIGN.md): the `CommandLine` port `m.args`, the words after the first `--` keyed
from 0, a read outside `0..<n` giving `#outOfBounds`, an argument that is not UTF-8 a usage
error naming its key, the arguments recorded and replayed. Plan row TEST-complete-ports
(author P189). Coverage before and after is in l01_19_whole_file_ports/COMPLETENESS.md.

| Case | Covering test | Or reason none is needed |
|---|---|---|
| Arguments keyed from 0; the keys of n arguments are `0..<n` | `arguments.rs::arguments_are_keyed_from_zero`, `arguments.rs::the_keys_of_n_arguments_are_0_to_n_minus_1` | |
| No `--`, or nothing after it: no key present | `arguments.rs::with_no_arguments_the_family_is_empty`, `arguments.rs::without_dashes_or_with_nothing_after_them_no_key_is_present` | |
| Every word after the first `--`, a later `--` or `--record` among them | `arguments.rs::every_word_after_the_first_dashes_is_an_argument`; `combinations.rs::an_argument_of_each_kind_is_written_as_given` | |
| An empty word, empty between words, a leading dash, spaces and a tab kept, non-ASCII | `combinations.rs::an_argument_of_each_kind_is_written_as_given` | |
| A key past the last or below 0 | `arguments.rs::a_key_past_the_last_argument_or_below_0_is_out_of_bounds` | |
| A key of 2^63 or more | `/home/luke/Work/wt/failing-tests/FAIL-ports-key-past-i64.rs` | Fails: gives `#notFound`, DESIGN gives `#outOfBounds`. Plan row FAIL-ports-key-past-i64; not merged (P188). |
| An argument read in interpolation, in a condition, at a computed key, through a helper, cast to `int`, used as a path | `combinations.rs::an_argument_is_read_in_each_position` | |
| An argument that is not UTF-8 is a usage error naming its key | `arguments.rs::an_argument_that_is_not_utf8_is_a_usage_error_naming_its_key`, `binary.rs::zedc_names_the_argument_that_is_not_utf8` | |
| A read left undisposed is rejected | `arguments.rs::a_read_may_be_out_of_bounds_so_the_checker_asks_for_its_disposal` | |
| The port is an input; push targets and views | `arguments.rs::the_arguments_are_an_input`, `arguments.rs::a_push_target_may_end_in_one_view`, `arguments.rs::a_push_target_has_at_most_one_view_and_it_comes_last` | |
| stdin and the arguments read together; a program without the port ignores its arguments | `arguments.rs::standard_input_and_the_arguments_are_read_together`, `arguments.rs::a_program_without_the_port_ignores_its_arguments` | |
| Record and replay of the arguments, with none, round trip, test-table `main` rows | `replay.rs` (all six tests) | |
| zedc passes the words; words that are no command; `zedc fmt` | `binary.rs` (all six tests) | |
| `len(m.args)` and keys computed from it | | Left out: at layer L1 `len` takes `(String) -> int` only (DESIGN words table). |
| `m.args.map(...)` | | Left out: `map` is a layer L3 word (DESIGN words table). |
| Many arguments | `bench.rs::a_run_with_many_arguments_scales` | Benchmark (P178). |
