# l01_36a_executables: completeness (step L1.36a)

The code under test is `zedc build <file> -o <out>` (`crates/zed-native/src/link.rs`:
`command`, `build`, the runtime library's check, the working directory and its sweep), the
data an executable carries and its start (`crates/zed-native/src/exe.rs`), and the run-time
limits (`crates/zed-rt/src/limits.rs`, `stack.rs`). The tests of this directory are the target
`l01_36a_executables` and, named in `crates/zed-native/Cargo.toml`, `build_binary`
(`binary.rs`) and `limits_binary` (`limits_binary.rs`). Each row is a case; the second column
names the test that covers it, or says why no test is needed.

| Case | Covering test, or reason none is needed |
|---|---|
| **Programs built and run against the interpreter** | |
| each step program, built twice to the same bytes, on all 31 corpus inputs | `agreement::{config,fahrenheit,greeting,username}_agrees`, `agreement::the_step_programs_are_exactly_these` |
| each enabled corpus program and fence program | `agreement::every_enabled_corpus_program_agrees` (none enabled at L1), `agreement::every_enabled_fence_program_agrees` |
| a program run by its user, from `zedc build` as a command | `binary::a_built_executable_runs` |
| a stripped `zedc` | `binary::a_stripped_zedc_builds` |
| **Inputs of a built program** | |
| standard input | `agreement::a_tuple_indexed_by_a_computed_key_agrees`, `agreement::config_agrees` and the other step programs |
| arguments after `--`: present, missing, not UTF-8 | `agreement::files_named_by_arguments_agree` |
| files by path: present, missing, a directory, not UTF-8 | `agreement::files_named_by_arguments_agree` |
| the environment | `agreement::every_enabled_fence_program_agrees` |
| `--record <out>`, replayed by `zedc run` | `agreement::a_record_of_the_executable_replays_under_the_interpreter` |
| a word before `--` the executable does not know; a port bound on the command line | `agreement::files_named_by_arguments_agree` |
| other forms of the executable's own command line (`--record` with no path, and so on) | none here: the executable reads its words with `zedc::run::executable`, the reader `zedc run` uses, whose cases step L1.19 tests |
| **Values computed only at run time** | |
| `>` and `>=`, rewritten by legalization | `agreement::a_built_comparison_by_greater_than_agrees` |
| a tuple indexed by a computed key, in range, past the end, negative | `agreement::a_tuple_indexed_by_a_computed_key_agrees` |
| `min`, `max`, `clamp` on floats at the corner values, both orders | `minmax::min_max_and_clamp_on_floats_agree_with_the_interpreter` |
| integer products at the word edges | `mul_edges::products_at_the_word_edges_are_exact_in_the_executable` |
| an atom with an empty payload apart from the bare atom | `atoms::an_empty_payload_is_built_apart_from_the_bare_atom` |
| constants too large to write out, folded or literal, as powers | `one_engine::*` |
| **Stops and their sites** | |
| a stop, status 1, placed at the expression that raised it, under both engines | `sites::*` |
| a number, power, rational power or string too large for memory, status 3 | `sites::a_number_too_large_is_placed_at_its_operation`, `sites::a_power_too_large_is_named_as_written_with_its_size`, `sites::a_rational_power_too_large_is_named_as_written_with_its_size`, `sites::a_string_too_large_is_named_as_written_with_its_size`, `limits_binary::a_number_too_large_for_memory_stops_the_run_with_status_3` |
| a site in the prelude, in a function of the program, shared by two expressions | `sites::a_prelude_word_is_placed_at_the_call_in_the_program`, `sites::a_function_of_the_program_is_placed_in_its_body`, `sites::a_node_two_expressions_share_takes_the_first_site` |
| sites change neither the address nor the ZIR text | `sites::the_sites_change_neither_the_address_nor_the_zir_text` |
| **Limits `main` sets** | |
| memory, processor time, deadline: within and past, status 3 | `limits_binary::*` |
| **`zedc build`'s command line** | |
| no words, a file alone, `-o` with nothing after, words out of order, extra words, two files, only flags | `command::a_command_line_not_of_the_form_file_o_out_is_a_usage_error`, `binary::a_wrong_command_line_is_a_usage_error` |
| `--suppress` with no address or a word that is not one; `--option` with no name | `command::a_command_line_not_of_the_form_file_o_out_is_a_usage_error` (the messages are step L1.29's and L2.8d's) |
| a rejected program | `binary::a_rejected_program_builds_nothing` |
| **Tools** | |
| a missing runtime library; a missing linker | `binary::a_missing_tool_is_a_usage_error_naming_it` |
| a runtime library of another build, by its build or its compiler flags | `runtime::a_build_refuses_a_library_of_another_build`, `binary::a_runtime_library_of_another_build_is_a_usage_error` |
| a runtime library that is not an archive | `command::a_runtime_library_that_is_not_an_archive_is_named` |
| a linker that cannot be run (not executable) | `command::a_linker_that_cannot_be_run_is_named` |
| a linker that runs and fails, what it printed shown | `command::a_link_that_fails_is_named_with_what_the_linker_printed` |
| a linker run for its versions that then cannot be run for the link | none: only a change to the file between two runs a few milliseconds apart reaches it; the message is the one of the row above, from the same function `not_run` |
| `zedc` that cannot find its own file (`current_exe` fails) | none: on Linux it reads `/proc/self/exe`, which fails only without `/proc` |
| picking the runtime library built with this executable among several | `runtime::*` |
| **Output paths** | |
| `-o` naming no file (`dir/..`) | `command::an_output_that_names_no_file_is_refused` |
| `-o` in a directory that does not exist | `command::an_output_that_names_no_file_is_refused` |
| `-o` naming an existing directory: refused, the directory left as it is | `command::an_output_that_is_a_directory_is_left_as_it_is` |
| a build killed while linking; the next build sweeps what it left | `binary::a_build_killed_while_linking_blocks_no_later_build` |
| a working directory name taken, or swept by another build between its creation and its lock | none: a race of two processes at one name of one process id; step L1.36b's `leftover::builds_to_one_output_at_once_all_succeed` runs builds at once |
| the cache of links, the identity of the toolchain, the files a link read | step L1.36b (`tests/steps/l01_36b_link_identity`) |
| **The executable's own start** | |
| the data the build writes read back, and an executable whose data does not read back | `exe::tests::the_data_reads_back` in `crates/zed-native` (out of this row's scope). The data is written by the same build that reads it, and is no input of the user's; every build test above reads it back |
| **Scaling** | in `bench.rs` (`--bench`); not correctness tests (P178) |

## Coverage

Line coverage is measured with `-C instrument-coverage` over the test binaries in this
process. `exe.rs`'s `zed_main`, `start` and `Program::decode`, and most of `zed-rt`'s
`limits.rs` and `stack.rs`, run inside the built executables and in the child processes of
`build_binary` and `limits_binary`, which are linked with the runtime library, not with the
instrumented test binary: they run in every build test above but are not counted. `limits.rs`
and `stack.rs` also have their own unit tests in `crates/zed-rt`.
