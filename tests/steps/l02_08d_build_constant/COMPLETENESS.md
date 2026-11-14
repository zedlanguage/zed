# Completeness: l02_08d_build_constant

Step L2.8d (DESIGN.md): `build.target` and `build.options.<name>` are literals of the build,
fixed by `--target` and `--option`; a read of an option the manifest does not declare is an
error naming the declared ones; staging keeps the branch the build takes and drops the others,
and test tables of dropped branches are listed as not run. Plan row TEST-complete-ports
(author P189). Coverage before and after is in l01_19_whole_file_ports/COMPLETENESS.md.

| Case | Covering test | Or reason none is needed |
|---|---|---|
| A read is a literal of the build | `reads.rs::a_read_is_a_literal_of_the_build` | |
| A read in an `if` condition, negated, in a conjunction and a disjunction, with `!=`, the literal on the left, in a helper body, as a helper argument, bound to a name, in a nested `if` | `combinations.rs::a_read_in_each_position_is_replaced_by_its_literal` | |
| Each of the seven target literals on either side of `==` and `!=` | `combinations.rs::every_target_is_a_target_literal_on_either_side` | |
| A target literal that names no target, on either side | `reads.rs::a_target_literal_that_names_no_target_is_rejected_on_either_side` | |
| Two options: none, either, both, both in the other order | `combinations.rs::each_build_of_two_options_takes_its_own_branch` | |
| An undeclared option, with the declared options in manifest order; a package that declares none | `reads.rs::an_undeclared_option_is_rejected_with_the_declared_options_in_manifest_order`, `reads.rs::an_option_read_where_the_package_declares_none_says_so` | |
| Every use other than the two reads is rejected | `reads.rs::every_use_other_than_the_two_reads_is_rejected_naming_them` | |
| A program's own `build` shadows the word | `reads.rs::a_programs_own_build_shadows_the_word` | |
| `--option` turned on, with no name, not declared; the pins unchanged by it; the manifest lists each option once | `command.rs` (all five tests) | |
| `--target` naming no target | `test_staged.rs::target_is_a_usage_error_when_it_names_no_target` | |
| Each target lowers its own branch; without staging every branch is lowered | `branches.rs` (both tests) | |
| An executable holds the strings of the taken branch only, by target and by option | `staged.rs::an_executable_holds_the_string_of_the_taken_branch_only`, `staged.rs::an_executable_holds_the_string_of_the_options_branch_only` | |
| `run` and replay stage the program; a run writes what its build takes | `staged.rs::run_and_replay_stage_the_program`, `staged.rs::run_of_a_few_option_branches_writes_the_letters_its_build_takes` | |
| Test rows of a dropped branch: listed as not run, not failing, turned over by an option; rows of evaluated or unreached functions run; a unit with no `main` runs every row | `test_staged.rs` (first five tests) | |
| `test`, `run` and `mutate` stage the same program | `test_staged.rs::test_and_run_stage_the_same_program`, `test_staged.rs::test_of_a_few_taken_and_dropped_functions_runs_the_taken_rows_only`, `test_staged.rs::mutate_runs_no_row_that_test_does_not_run` | |
| Many reads | `scaling.rs::a_few_reads_pass_the_front_end` | Small scaling run (P178). |
