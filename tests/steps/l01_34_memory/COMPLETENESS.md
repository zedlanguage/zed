# l01_34_memory: completeness (step L1.34, DESIGN.md sec:memory)

The code under test is `crates/zedc-zir/src/zir/memory.rs`: the planner (`plan`: borrow
inference, last-use drops, dups, entry drops, result dups, fusion) and the counting machine
(`run`: runs a planned graph and checks every count after every node). Each row is a case; the
second column names the test that covers it, or says why no test is needed.

| Case | Covering test, or reason none is needed |
|---|---|
| **Kinds of value** | |
| int, float, bool, `()`, a bare atom: no cell | `cells::strings_tuples_and_big_integers_are_cells_and_scalars_are_not` |
| string, tuple, big integer: one cell each | `cells::strings_tuples_and_big_integers_are_cells_and_scalars_are_not` |
| a closure: a cell holding its captures | `borrow::a_closure_holds_its_captures` |
| a struct value matched by field name | `fusion::a_struct_binder_is_found_by_field_name` |
| a value nested a cell a level | `scaling::a_nested_value_is_allocated_and_freed_a_cell_a_level` |
| a port's value: a fresh cell, read once and used twice | `decisions::the_machine_gives_the_kernels_outcome_on_failures_and_ports` |
| a failure atom as a decision's value | `decisions::the_machine_gives_the_kernels_outcome_on_failures_and_ports` |
| **Uses of a value** | |
| used once: never counted | `cells::a_value_used_once_is_never_counted` |
| read (borrowed), then dropped at its last use | `cells::a_borrowed_value_is_dropped_at_its_last_use` |
| consumed twice: a dup before each owned use but the last | `cells::each_owned_use_but_the_last_gets_a_dup` |
| returned while borrowed: a result dup | `cells::a_borrowed_value_returned_gets_a_dup` |
| passed to an arm that ignores it: an entry drop | `cells::an_arm_that_ignores_an_owned_capture_drops_it_on_entry` |
| **Positions** | |
| `let` body, tuple component, primitive argument | `cells::*`, `checks::*` |
| lambda parameter only read: borrowed | `borrow::a_parameter_only_read_is_borrowed` |
| lambda parameter consumed: owned | `borrow::a_parameter_consumed_is_owned` |
| callee seen through a capture | `borrow::a_call_through_a_capture_sees_the_callee` |
| callee the plan cannot see: arguments passed owned | `borrow::an_unknown_callee_takes_its_arguments_owned` |
| capture of a capture, called and dropped | `scaling::closures_capturing_closures_are_called_and_dropped` |
| two lambdas sharing one body | `places::a_body_shared_by_two_lambdas_runs_as_two_occurrences`, `chains::wrappers_sharing_one_body_take_their_argument_as_their_callee_does` |
| `if` arms nested in `if` arms | `chains::nested_ifs_hand_each_name_owned_down_to_the_tuple`, `scaling::a_nest_of_ifs_is_planned_and_run_to_the_kernels_value` |
| a push under nested `if`s | `scaling::a_push_under_nested_ifs_is_planned_and_run_once` |
| chains of calls, borrowing or consuming at the leaf | `chains::a_call_chain_borrows_down_to_a_borrowing_leaf_and_owns_down_to_a_consuming_one`, `chains::capture_chains_borrow_the_captured_string_for_every_call` |
| a binder at every level of a deep pattern, every set of kept binders | `binders::every_set_of_kept_lines_of_a_deep_match_is_released_exactly` |
| **Fusion** | |
| a unique scrutinee, fused and unfused | `fusion::a_fresh_pair_destructured_costs_one_write_fused_and_four_unfused` |
| a shared scrutinee | `fusion::a_shared_scrutinee_dups_what_it_keeps` |
| kept parts move out with no count write | `binders::a_held_once_invoice_moves_its_kept_lines_out_with_no_count_write` |
| every failure and port case, fused and unfused | `decisions::the_machine_gives_the_kernels_outcome_on_failures_and_ports` |
| **Decisions that fail, and ports** | |
| `if` on an atom, the arms borrowing or owning a cell: the atom, inputs dropped | `decisions::the_machine_gives_the_kernels_outcome_on_failures_and_ports` |
| `match` no arm of which matches (int, string, atom): the kernel's stop | `decisions::the_machine_gives_the_kernels_outcome_on_failures_and_ports` |
| a port the run was not given: the kernel's error | `decisions::the_machine_gives_the_kernels_outcome_on_failures_and_ports` |
| **Whole programs** | |
| every table row of every corpus unit, waves included, fused and unfused | `corpus::every_row_passes_through_the_machine` |
| a pushing function called twice | `corpus::a_function_that_pushes_and_is_called_twice_passes_through_the_machine` |
| the same program built in different allocation orders | `places::the_machine_keeps_nodes_by_place_not_address` |
| a program whose result is a function | `checks::a_result_that_is_a_function_is_refused` |
| **The machine's checks on a wrong plan** | |
| a missed drop: a leak | `checks::a_missed_drop_is_a_leak` |
| an extra dup: a count above the references | `checks::an_extra_dup_is_a_count_above_its_references`, `checks::each_check_of_the_machine_reports_its_wrong_plan` (a dup at a last use, a dup of a passed closure) |
| a missing dup: an edge consumed twice | `checks::a_missing_dup_consumes_an_edge_twice` |
| a borrowed argument to a consuming parameter | `checks::a_borrowed_argument_to_a_consuming_parameter_is_refused` |
| no plan at all; an arm with no plan | `checks::each_check_of_the_machine_reports_its_wrong_plan` |
| a lambda body with no plan, called | not merged: filed as FAIL-memory-callee-no-plan (the message names the same region twice) |
| the plan resolves a call to another region | `checks::each_check_of_the_machine_reports_its_wrong_plan` |
| an argument arriving borrowed that the plan owns (a capture), and owned that the plan borrows (an arm argument) | `checks::each_check_of_the_machine_reports_its_wrong_plan` |
| a region (the root, a body) that ends owning an edge | `checks::each_check_of_the_machine_reports_its_wrong_plan` |
| a body that keeps an owned argument past its last use | `checks::each_check_of_the_machine_reports_its_wrong_plan` |
| a use, a result, a drop consuming a borrowed or already consumed edge | `checks::each_check_of_the_machine_reports_its_wrong_plan` |
| a read after the edge's last use | `checks::each_check_of_the_machine_reports_its_wrong_plan` |
| a borrowed scrutinee whose arm owns a binder | `checks::each_check_of_the_machine_reports_its_wrong_plan` |
| a read of a freed cell; a drop of a freed cell; a frame holding a freed cell; cells live after the result is dropped | none: each needs a reference the per-node count check already reports as a count below or above its references, so no plan reaches them first (inferred from `check`, which runs after every node and at each entry); they stay as defensive checks |
| a kept path reading past a cell's parts | none: the paths come from the pattern the kernel matched against the same value, so a part index is always in range |
| `match` whose kernel run gives a failure value instead of an arm index | none reached: the kernel stops when no arm matches (the `match` rows above); a failure scrutinee is turned into arms by elaboration, before L1.34 |
| `if` whose condition is a non-boolean the kernel turns into an arm index | none: the checker gives `if` a `bool` or a failure; the failure case is covered |
| **Scaling** | in `bench` (planning and running are linear in depth); not correctness tests (P178) |
