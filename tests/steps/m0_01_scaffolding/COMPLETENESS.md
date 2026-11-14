# M0.1 completeness: step folders and their test targets

Code under test: `zed_tests::is_step_name` (tests/src/lib.rs) and `zed_tools::step_targets`
(`folders`, `block`, `splice`, `targets`, `drift`, `run`). Lines of step_targets.rs reached:
73% before this pass, 98% after (by llvm-cov); the lines left are the `read_dir` entry and `file_type` errors
and a failed `fs::write`, which need a failing file system. Every line of `is_step_name` is reached.

| Case | Covering test, or the reason none is needed |
|---|---|
| Stage `m0`, `s`, `l01`, `l29` | `cases::step_names_by_stage_step_letter_and_description` |
| Stage `l30` to `l40` (DESIGN.md has layers L30 to L40) | Fails: row FAIL-steps-name-layers, `wt/failing-tests/FAIL-steps-name-layers.rs` |
| Stage `l41` (no such layer) refused | FAIL-steps-name-layers (passes now, kept beside the failing case) |
| Stage `l+1` (a sign) refused | Fails: row FAIL-steps-name-plus-sign, `wt/failing-tests/FAIL-steps-name-plus-sign.rs` |
| Stage upper case, unknown, `m1`, `l00`, `l1`, `l001`, a letter beyond ASCII after `l` | `cases::step_names_by_stage_step_letter_and_description` |
| Step `01`, `99`, `00`, one digit, three digits, `+1`, letter `a` on each stage, two letters, upper-case letter, a letter only | `cases::step_names_by_stage_step_letter_and_description` |
| Description: one letter, digits, inner `_`, inner `__`, empty, leading `_`, trailing `_`, upper case, hyphen, a letter beyond ASCII | `cases::step_names_by_stage_step_letter_and_description` |
| No description, empty name | `cases::step_names_by_stage_step_letter_and_description` |
| Every folder in the repository well named | `every_step_folder_is_well_named` |
| `folders`: empty directory | `cases::folders_lists_subdirectories_only_in_byte_order` |
| `folders`: subdirectories in byte order, upper case before lower | `cases::folders_lists_subdirectories_only_in_byte_order` |
| `folders`: a file among the folders is skipped | `cases::folders_lists_subdirectories_only_in_byte_order` |
| `folders`: missing directory, a file given as the directory | `cases::folders_lists_subdirectories_only_in_byte_order` |
| `folders`: a folder name that is not UTF-8 refused with its name | `cases::folders_lists_subdirectories_only_in_byte_order` |
| `folders`: an entry or its type that cannot be read | None: needs a failing file system; the error path is one `map_err` like the tested ones |
| `block`: no folder, one, two in set order | `cases::block_writes_one_target_per_folder_in_set_order` |
| `splice`: empty block, new block, second pair of markers untouched | `cases::splice_replaces_only_the_lines_between_the_markers` |
| `splice`: END before BEGIN, END without a line break, BEGIN without a line break | `cases::splice_replaces_only_the_lines_between_the_markers` |
| `splice` twice changes nothing; written targets read back | `the_written_targets_read_back_and_splicing_twice_changes_nothing` |
| `targets`: empty block; spaces around `=` absent or many; comments, blank lines, other keys | `cases::targets_reads_names_and_paths_and_skips_every_other_line` |
| `targets`: keys `names`, `paths` are other keys; text outside the markers ignored | `cases::targets_reads_names_and_paths_and_skips_every_other_line` |
| `targets`: a path with no name, a name with no path, two names before a path | `cases::targets_reads_names_and_paths_and_skips_every_other_line` |
| `targets`: unquoted, single-quoted and unterminated values are not read | `cases::targets_reads_names_and_paths_and_skips_every_other_line` |
| `drift`: nothing; matching sets in another order; no folders; no targets | `cases::drift_of_matching_and_empty_lists_is_empty` |
| `drift`: a target listed twice and three times, with another path, with no folder and a wrong path at once | `cases::drift_reports_each_problem_of_one_target_together`, `drift_names_a_target_listed_twice_or_with_another_path` |
| `drift`: folder without a target, target without a folder | `drift_names_each_folder_without_a_target_and_each_target_without_a_folder` |
| The repository's folders and targets agree | `every_step_folder_has_a_target_and_every_target_has_a_folder` |
| The list of step folders | `step_index` (expected-output snapshot) |
| `run --check` before writing (fails, one line a folder), after writing (passes, silent), after a folder is removed | `cases::the_tool_checks_writes_and_refuses_bad_arguments` |
| `run` writes, then reports unchanged | `cases::the_tool_checks_writes_and_refuses_bad_arguments` |
| `run --check` with no root reads this repository | `cases::the_tool_checks_writes_and_refuses_bad_arguments` |
| `run` with no root writing this repository | None: it would write the real manifest; its pieces are the cases above |
| `run` with two roots, `--check` and two roots: usage error | `cases::the_tool_checks_writes_and_refuses_bad_arguments` |
| `run` with an unknown flag: read as a root | `cases::the_tool_checks_writes_and_refuses_bad_arguments` |
| `run` on a root with no manifest, a manifest and no `tests/steps`, or a manifest with no markers (write and check), writes nothing | `cases::the_tool_checks_writes_and_refuses_bad_arguments` |
| `run` when writing the manifest fails | None: needs a read-only file system; one `map_err` |
| Many folders written and read back | `scaling::the_targets_of_some_folders_are_written_and_read_back_without_drift`; sizes in `bench` |
