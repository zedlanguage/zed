# Completeness of the L25.8 tests (`zedc test --mutate`)

Author P189, 2026-11-14, row TEST-complete-misc. Code under test: `crates/zedc/src/mutate.rs`
(all of it), `crates/zedc-elab/src/elab/mark.rs` (the marks of mutable operators and constants)
and the `--mutate` part of `crates/zedc/src/testing.rs` (`command` and `mutants`). Expected
results come from DESIGN.md L25.8 and L2.8d. A test named `file::name` is in this directory.

Coverage by llvm-cov over the correctness tests of this group (benchmarks left out), before and
after this pass: `mutate.rs` lines 83.40% → 86.87%, regions 89.67% → 91.97%; `mark.rs` lines
84.62% → 92.31%. Each line still not reached is listed below with its reason.

| Case | Test that covers it | Or the reason none is needed |
|---|---|---|
| `<` → `<=`, `<=` → `<`, `>` → `>=`, `>=` → `>`, `==` → `!=`, `!=` → `==`, each at the operator's column | `cases::each_comparison_is_replaced_by_its_boundary_neighbor` | |
| `+` → `-` and `-` → `+` | `cases::addition_and_subtraction_are_replaced_by_each_other` | |
| `*` → `/` and `/` → `*` on `rat` and on `f64`; no mutant of `*` on `int` | `cases::multiplication_and_division_are_replaced_on_rat_and_f64`, `examples::a_multiplication_becomes_a_division_only_where_division_is_defined` | |
| Other operators (`div`, `mod`, `^`, `++`, `&&`, `\|\|`, `!`, unary `-`) | | DESIGN L25.8 names examples ("`<=` with `<`, `+` with `-`, a constant with its neighbor"), not the set. QUESTIONS A103 asks which operators are replaced; row TEST-mutate-set adds the tests after the answer. |
| Integer constant in decimal, `0`, hex, with `_`, at the top of `i64`, past `i64`: `n - 1` then `n + 1`, printed in decimal | `cases::each_form_of_an_integer_constant_gives_its_two_neighbors` | |
| `-3`: a literal has no sign (sec:grammar `Integer`), so the constant is 3 and the mutants give -2 and -4 | `cases::each_form_of_an_integer_constant_gives_its_two_neighbors` | |
| Whole-number constant whose use fixes `rat` / `f64`: neighbors at that carrier | `examples::a_whole_number_on_rat_has_its_mutants_at_rat`, `cases::a_whole_number_on_f64_has_its_neighbors_at_f64` | |
| Constants that are not integers (`2.5`, `0.5r`, strings, `true`) | | Same question, A103: DESIGN does not say what the neighbor of a non-integer constant is. |
| Neighbor too large for memory (`mutate.rs` `beside`, the `TooLarge` error) and a neighbor whose digits the system will not print (`reported`, "an integer of …") | | Reached only when the system refuses memory for a number about the size of a literal already read from the source; no small, fast test can make that happen (an unusual size, P178). |
| Operator after parentheses, line breaks and a `//` comment: the column is the operator's | `cases::the_operator_is_found_after_parentheses_and_a_comment` | |
| `operator_at` finds no operator in the gap (falls back to the gap's start) | | Not reachable from source: a binary operator always has its token between its operands. |
| Mutant in a local binding, a tuple, a call's argument, a string interpolation, an `if` condition and both branches | `cases::a_mutant_in_each_place_of_a_body_is_detected_by_a_row_that_reaches_it` | |
| Mutant in a default constant, one per call that uses it | `examples::a_default_constant_has_a_mutant_at_each_call_that_uses_it` | |
| Mutant in a function with no table, reached through its caller's table | `cases::a_callee_s_mutants_are_detected_by_its_caller_s_table` | |
| Mutant in a definition no table reaches | `examples::a_definition_no_table_reaches_has_its_mutants_undetected` | |
| Mutant reached only by rows of untaken branches (L2.8d) | `l02_08d_build_constant::test_staged::mutate_runs_no_row_that_test_does_not_run` | Covered in the L2.8d group; it needs a build constant. |
| Mutant detected by the second row after the first passes; undetected when every row passes | `cases::a_mutant_is_detected_by_any_row_and_undetected_only_when_every_row_passes`, `examples::a_table_that_omits_the_boundary_leaves_its_mutants_undetected` | |
| Mutant the build stage proves equal: skipped | `examples::a_mutant_the_build_stage_proves_equal_is_skipped`, `examples::the_fares_report` | Which equal mutants are skipped is the optimizer's strength: `a + 0` → `a - 0` with `a` a parameter is reported undetected today, and the law catalog has no `x + 0 = x`, so no test pins either verdict. |
| Mutant whose row may not end: not run | `examples::a_mutant_whose_row_may_not_end_is_not_run` | |
| Row of `main`: the mutant runs the program's wave | `examples::a_row_of_main_runs_the_mutant_wave` | |
| Row of `main` with no program built (`run`, `("main", _, _) => continue`) | | Not reachable through `zedc test`: the tables passed on the original before mutation runs, which needs the program. |
| Definition with nothing to replace: 0 mutants | `cases::a_definition_with_nothing_to_replace_has_no_mutant` | |
| Report order: definitions by name, nodes in preorder, `n - 1` before `n + 1`; independent of declaration order | `order::reordering_declarations_keeps_the_report_order`, `order::moving_a_definition_down_changes_only_its_line` | |
| Marked elaboration differs from the unit (the internal errors of `mutants`) and the `unreachable!` arms of `neighbors` and `apply` | | Internal consistency checks of the compiler; no source reaches them. |
| `mark_of` on an operator with no mark | | Every source operator of the kinds `mutable` admits is marked by `elaborate_marked`; no source reaches it. |
| Command: undetected mutants leave status 0 | `command::undetected_mutants_do_not_change_the_exit_status` | |
| Command: the original's tables fail, or the unit does not compile: status 1, no mutant runs | `command::a_program_whose_own_tests_fail_exits_non_zero_and_runs_no_mutant`, `command::a_program_that_does_not_compile_exits_non_zero_and_runs_no_mutant` | |
| Command: a file with no row and no ✗ mark | `cases::a_file_with_no_test_runs_no_mutant` | |
| Command: a rejection unit with a unit that has tables | `cases::a_rejection_unit_adds_no_mutant` | |
| Command: `--target`, `--option` after `--mutate`; an unknown option is a usage error | `cases::the_flags_of_zedc_test_follow_mutate` | |
| Command: `--mutate` and no file | `command::a_usage_error_names_the_flag` | |
| Command: several files report as each alone | `command::several_files_report_as_each_file_alone` | |
| Command: `--mutate` after another flag | | DESIGN gives no order of the flags of `zedc test`; the usage line puts `--mutate` first. |
| A corpus function whose table checks a boundary (the L25.8 test) | `examples::the_fares_report`, `examples::a_boundary_the_table_checks_detects_its_mutants` | |
| Scaling of finding and running mutants | `scaling::the_mutants_of_each_benchmark_unit_at_small_sizes`; the benchmarks in `bench.rs` | |
