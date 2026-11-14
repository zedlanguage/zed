# Completeness: literals that take the carrier of their use (L1.26a, L1.26b)

Row TEST-complete-literals (author P189). The code under test is the literal code of the
checker: `crates/zedc-check/src/check/mod.rs` (`read_literal`, `lit_value`, `lit_holds`,
`menu`, `decimal_at_int`, `literal_message`, `rat_forms`, `is_cast_of_literal`, the
`unfixed_*` menus) and `crates/zedc-check/src/check/walk.rs` (`lit_fit`, `fit_lambda`,
`fit_step`, `literals_refused`, `apart`), with the reading of literals in
`crates/zedc-elab/src/elab/walk.rs` and `crates/zed-kernel/src/num/`. Expected results are
from DESIGN.md L1.26a, L1.26b, sec:domains, sec:type_resolution rules 3 and 4, the operator
table, and sec:diagnostics rows "Numeric literal at a carrier that cannot take it" and "Two
numeric values with no common carrier". llvm-cov, as a floor, over both groups' tests
(regions): `check/mod.rs` 86.20% before, 86.47% after; `check/walk.rs` 82.99% before, 83.59%
after; `elab/walk.rs` 86.49% before, 86.82% after. The counts move by up to 0.3% from run to
run with the order of the test threads (type-variable renaming in `check/mod.rs` is reached or
not). In the literal functions, uncovered lines: `is_cast_of_literal` 9 → 1, `fit_step`
23 → 1, `fit_lambda` 17 → 0, `literals_refused` 8 → 7, `apart` 29 → 17. The lines still
uncovered are listed at the end with their reasons.

The carriers are `int`, `f32`, `f64` and `rat`; `bf16` and `f16` arrive with step L1.18a.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| **Kinds of literal** | | |
| An integer literal: generic, `int` where nothing fixes it | `mod.rs` `an_integer_literal_leaves_the_parameter_generic`, `literals_that_nothing_else_fixes` | |
| A decimal literal: every carrier but `int`; rejected where nothing fixes it | `mod.rs` `a_decimal_literal_takes_a_float_format_or_rat_and_never_int`, `literals_that_nothing_fixes_and_that_no_int_holds_are_rejected_with_a_menu` | |
| Suffixed literals `r`, `f64`, `f32`; no suffix on an integer | `features.rs` `literals_of_two_carriers_meet_only_where_one_takes_the_other`; `mod.rs` `the_lexer_reads_no_suffix_on_an_integer` | |
| Forms of one number: exponent, underscores, hex, a leading point | `features.rs` `the_forms_of_a_number_are_one_literal_each`; `written.rs` | |
| Zero, `-0`, `-0.0`, each sign, the bounds of `i64` and one past | `features.rs` `signs_zero_and_the_bounds_of_i64_keep_their_exact_values` | |
| An integer no float holds exactly (2^24 + 1 at `f32`, 2^53 + 1 at `f64`) | `features.rs` `an_integer_literal_with_no_exact_float_is_rejected_at_that_float`; `mod.rs` `an_integer_literal_removes_the_carriers_that_do_not_hold_it` | |
| A decimal no float holds exactly (`0.1` at `f32`) is the nearest value | `features.rs` `an_integer_literal_with_no_exact_float_is_rejected_at_that_float` | |
| A decimal past the range of `f64` (`1e400`, `1e-400`) | `features.rs` `a_literal_out_of_the_range_of_a_float_is_rejected_with_the_rounding_it_would_take` | |
| A decimal past the range of `f32` leaves `f32` out of a class; the largest `f32` keeps it | `features.rs` `a_decimal_past_the_range_of_f32_leaves_f32_out_of_a_class` | |
| A decimal past the range of `f32` at a declared `f32` | | Pending LIT-formats (f32 range messages and menus, after L1.18a); test source saved in /home/luke/Work/wt/failing-tests/LIT-formats-decimal-past-f32-param.rs |
| A decimal past the range of `f64` beside `rat` | | Already FAIL-check-decimal-past-f64-at-rat |
| Many digits, deep nests, long lines | `scaling.rs` | Larger sizes are benchmarks (P178), `bench.rs` |
| **Syntactic positions** | | |
| Operand of an operator, either side | `mod.rs` `an_operation_on_literals_alone_takes_the_carrier_it_meets`; `param_follows.rs` | |
| Argument at a declared, generic or untyped parameter; by position and by name | `features.rs` `a_literal_argument_of_a_declared_parameter_is_read_at_its_carrier`; `call_arguments.rs`; `mod.rs` `a_literal_argument_leaves_the_caller_generic` | |
| Argument at a declared union (`f64 \| String`, `f64 \| rat`) | `features.rs` `a_literal_argument_of_a_declared_union_takes_its_one_numeric_carrier` | |
| Several refused literal arguments: one error that counts them | `features.rs` `several_literal_arguments_a_call_refuses_are_one_error_that_counts_them` | |
| Lambda body: called through a higher-order function, bound to a name, called where written | `positions.rs` `a_literal_in_a_lambda_body_takes_the_carrier_of_the_lambdas_argument`, `a_lambda_bound_to_a_name_is_generic_over_the_carriers_its_literal_takes`, `a_lambda_body_of_literals_alone_keeps_its_literals` | |
| Lambda in a slot of a declared function type: the slot's carrier; a missing or extra parameter; a narrower parameter | `positions.rs` `a_lambda_in_a_slot_of_a_declared_function_type_gives_its_literal_that_slots_carrier`; `features.rs` `a_lambda_needs_a_parameter_for_each_argument_passed_by_position` | |
| Local function and block | `positions.rs` `a_literal_in_a_local_function_or_a_block_takes_the_carrier_of_the_parameter` | |
| Bound to a local name alone: `int` | `positions.rs` `an_integer_literal_bound_to_a_local_name_alone_is_an_int`; `name_fixed.rs` | |
| Tuple component, returned or compared | `positions.rs` `a_literal_returned_in_a_tuple_beside_a_parameter_keeps_its_value`; `tuples.rs`; `tuple_arg_pair.rs`; `tuple_rest.rs` | |
| `if` branch: both literals, nested, beside a parameter, beside another type, at a declared parameter | `positions.rs` `a_nest_of_ifs_of_literals_is_the_union_of_their_values`; `features.rs` `a_literal_branch_beside_a_branch_of_another_type_keeps_both`, `a_literal_branch_at_a_declared_parameter_is_read_at_its_carrier`; `lit_branches.rs`; `lit_branch_ops.rs` | |
| `if` branch beside a `rat` name bound to a literal, or a `rat` literal, at a `rat` use | | FAIL-check-if-carrier-branch-literal-at-rat (DESIGN's `h(if b { r } else { 0.1 })` sentence) |
| `else` default: `int` beside `div`, a literal of the union beside `rat` | `positions.rs` `a_literal_default_of_else_takes_the_carrier_of_the_other_side` | |
| String hole | `positions.rs` `a_literal_in_a_string_hole_takes_a_carrier_as_it_would_alone`; `tuples.rs` `a_decimal_in_a_block_a_hole_or_a_default_is_rejected` | |
| Nested in itself: operations, calls, `inc(x: inc(...))` | `positions.rs` `literals_nested_in_operations_and_calls_take_the_carrier_of_the_outermost_use` | |
| Comparison with a parameter; `==` with a class | `positions.rs` `a_literal_compared_with_a_parameter_takes_its_carrier`; `mod.rs` `a_literal_compared_with_a_class_leaves_its_carriers` | |
| Negation | `positions.rs` `a_negated_literal_takes_the_carrier_of_its_use`; `lit_branches.rs` `a_negated_rat_literal_is_a_literal` | |
| Top level and body agree | `top_body_agree.rs`; `mod.rs` `batch_and_single_file_checking_agree` | |
| Receiver of a method; struct field; `match` arm; `initial`; loops | | Not reachable at this layer: name resolution rejects struct, type, method, local, `initial`, `while` and `until` statements (`crates/zedc-elab/src/elab/walk.rs`, the statement match); `match` is built at L2.4 |
| Declared binding `x: rat = 1;` | | Pending LIT-decl-binding and L1.26b; the tests use a declared parameter instead |
| **Other features** | | |
| Atoms: `/ 0` gives `#divByZero`, `div`, `#none` beside a literal | `features.rs` `a_literal_beside_an_operation_that_may_give_an_atom_keeps_the_atom`; `lit_branches.rs` `a_zero_branch_keeps_div_by_zero` | |
| Float `÷ 0.0` gives `#divByZero` | | Pending POW-domains |
| Casts of literals and of operations on literals | `features.rs` `a_literal_cast_takes_the_carrier_the_cast_names`; `cast_int_f64.rs`; `cast_rat_int.rs`; `cast_of_union.rs` | |
| A cast of a literal compared with a value of another type | `features.rs` `a_literal_cast_compared_with_a_value_of_another_type_is_always_false` | |
| Comparison with a string, `bool` or tuple: the values it may mean | `features.rs` `a_literal_compared_with_a_value_that_holds_no_number_is_offered_the_values_it_may_mean`; `fixes.rs` `a_comparison_no_number_can_equal_lists_what_fits` | |
| An operator that takes no number (`and`, `++`) | `features.rs` `an_operator_that_takes_no_number_rejects_a_literal` | |
| Powers: integer power, float power, negative exponent at `rat` | `features.rs` `a_power_takes_the_integer_or_the_float_power_by_its_operands`; `top_body_agree.rs`; `lazy_carrier.rs` | |
| A `rat` literal folded with integer and decimal literals | `features.rs` `a_rat_literal_folds_with_integer_and_decimal_literals_at_a_rat_parameter`, `a_rat_literal_in_an_operation_on_literals_at_a_rat_parameter_keeps_its_exact_value` | |
| Unions of literal values and carriers | `two_union_operands.rs`; `call_union_at_f64.rs`; `parts_type.rs` | |
| A generic function passed to a slot of two arrows | `mod.rs` `a_generic_function_fits_a_slot_of_two_arrows` | |
| Ports: a program run | `features.rs` `a_literal_in_a_program_run_through_its_ports_takes_its_carrier`; `mod.rs` `a_program_runs_literal_arguments_branches_and_components` | |
| Units and facets | | Units exist only in the parser at this layer |
| Imports | | Name resolution rejects import statements at this layer |
| Staging | | The literal is settled before staging; staging of literals is l01_27's group |
| **Errors and repairs** | | |
| Menus: unfixed decimal, decimal at `int`, no one carrier, no exact value, powers | `fixes.rs`; `design_menus.rs`; `lazy_carrier.rs` | |
| A forced literal beside another carrier offered without its suffix (`1r` beside `f64`) | `features.rs` `literals_of_two_carriers_meet_only_where_one_takes_the_other` | The implementation offers `1.0` where DESIGN writes `1`; both are the same `f64` |
| A forced literal beside `f32` (`1r`, `0.5r`) | | Pending LIT-formats (f32 menus); test source saved in /home/luke/Work/wt/failing-tests/LIT-formats-rat-suffix-beside-f32.rs |
| Each fix checks where it is offered (a lambda's fix `rat(x) * 0.5` in an `int` slot) | | Pending L1.26b ("every fix a rejected literal's message offers is applied in turn and checks") |
| Spelling: the literal quoted as written | `written.rs`; `spelling.rs` | |
| **Uncovered lines that remain** | | |
| `lit_holds`, the `f32` arm and the "nearest" `f64` arm | | The `f32` arm is the `f32` menu, pending LIT-formats; the nearest `f64` is offered only for an inexact decimal beside `f64`, which DESIGN gives no fix (`0.1r` beside an `f64`) |
| `literal_message` and `rat_forms`, the `quoting` fallback | | Taken only when `shown()` gives TooLarge, which needs memory to run out; not reachable in a test |
| `lit_value` `f64` → `f32` | | `f32` menus, pending LIT-formats |
| `carrier_mask` on a bound naming a type that is no carrier; `adopted` where `adopt` gives no value or an error inside a repair's check | | Not reached by any literal these groups can write; not shown unreachable. A test needs a `for T in` bound written in source or a repair whose own literal fails, neither of which this layer's syntax produces as far as this pass found |
| `fit_needs`, `main_limit_fix`, `fixed_at`, `built_text` | | Not literal code: functions with needs, and values past the address space (A100); their groups test them |
