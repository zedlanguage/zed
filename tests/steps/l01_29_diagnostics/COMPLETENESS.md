# Completeness: diagnostics (L1.29)

Row TEST-complete-diagnostics (author P189). The code under test is the rendering of
diagnostics in `crates/zedc/src/front.rs` (`Diagnostic`, the steps, the source lines and their
underlines, `Quoted`, `Unloaded::report`) and the derivations, rows and menus the checker and
the elaborator give it. Expected results are from DESIGN.md step L1.29 and rows L1.29a, L1.29b
and L1.29d, and from sec:diagnostics. This folder held 504 tests (benchmarks aside) before the pass; the
cases below name the file that covers each, and `completeness.rs` adds the ones no file had.
The repair and printing files moved to `../l01_29_repairs_and_printing`, a test target of its
own (TESTS-split, 2026-11-14); the table names them there.

Coverage of `crates/zedc/src/front.rs` by this group (llvm-cov, benchmarks skipped): regions
93.55% before the pass, 94.08% after; lines 94.04% to 94.39%. What stays uncovered is named in the
last rows of the table: `front::syntax`, read only by `zedc fmt` and run here through the
executable, which llvm-cov of the test executable does not count; and the refusal of a question
outside linear arithmetic, tested in `l01_38_presburger`.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| The layout: the message line, numbered steps padded to one width, each source line shown once with its underlines, numbers after underlines, overlapping underlines on further rows | `layout.rs` (thirteen tests) | |
| Nested texts drawn by their ends; a chain sharing its first or last character; an overlap with no nesting given by its range | `layout.rs` `sums_nested_on_one_line_…`, `calls_nested_on_one_line_…`, `powers_nested_on_one_line_…`, `a_step_whose_text_overlaps_another_without_nesting_is_given_its_range`, `a_balanced_nesting_is_underlined_in_full` | |
| Columns: a tab four, a wide character two, a combining mark none, a multibyte span by characters | `layout.rs` `wide_characters_tabs_and_combining_marks_are_underlined_…`, `the_underline_covers_a_multibyte_span_by_characters` | |
| A character printed escaped takes the columns of its escape; the place in the headline counts source characters | `completeness.rs` `a_hidden_character_on_a_shown_line_is_escaped_and_underlines_count_its_escape` | |
| Several diagnostics of one file: each line shown once, later steps by range under "line N is shown above" | `quoted.rs` (eight tests) | |
| Two diagnostics on two lines each show their own line, escapes and all | `completeness.rs` `two_diagnostics_each_show_their_own_line_with_its_escapes` | |
| A step that repeats an earlier one is shown only the first time: two calls of one function, two uses of one name | `completeness.rs` `a_step_that_repeats_an_earlier_one_is_shown_only_the_first_time`; a place shown once, `layout.rs` `steps_are_numbered_to_one_width_and_places_shown_once_when_repeated` | |
| The derivation: a name to its binder's origin, a call to its declaration and signature, operator parts, a narrowing `is`, a rebinding, a literal at the end | `derivations.rs` (fourteen tests); `declared.rs`; `literal_steps.rs` | |
| A rejected application lists each argument and each arrow of the callee | `derivations.rs`; `../l01_29_repairs_and_printing/casts.rs`; `sum_plus.rs` | |
| Rows of the table: binder naming a type, display in body position, operation that always fails, prefix `-` on a literal's chain, a name used above its definition, recursion, a type with no value (`Never`) | `binder_type.rs`, `body_display.rs`, `always_fails.rs`, `neglit.rs`, `negative_literals.rs`, `above.rs`, `recursion.rs`, `emptied.rs` | |
| Messages no other test produced | `../l01_29_repairs_and_printing/rare.rs` (eleven tests) | |
| Repairs: each offered repair checks; widening casts only; menu order; domain and power repairs | `../l01_29_repairs_and_printing/repairs.rs`, `../l01_29_repairs_and_printing/offered_repairs.rs`, `../l01_29_repairs_and_printing/casts.rs`, `../l01_29_repairs_and_printing/menu_order.rs`, `../l01_29_repairs_and_printing/domain_repairs.rs`, `../l01_29_repairs_and_printing/power_repairs.rs` | |
| Printed types are syntax: every printed type parses back; fresh type-variable names; binders as written; bounded type variables; kind-wide types; shared parts named | `../l01_29_repairs_and_printing/printed.rs`, `fresh_names.rs`, `../l01_29_repairs_and_printing/kernel_names.rs`, `tyvars.rs`, `kinds.rs`, `markers.rs`, `untracked.rs`, `../l01_29_repairs_and_printing/type_size.rs` | |
| L1.29a: printed types do not move; warnings only beside no rejection | `../l01_29_repairs_and_printing/stable.rs`; `../l01_29_repairs_and_printing/widen_test.rs` `a_rejected_unit_prints_no_warning`, `widen.rs` | |
| L1.29b: item order changes no verdict, diagnostic or outcome | `../l01_29_repairs_and_printing/order.rs` (eighteen tests) | |
| L1.29d: a syntax error, the tokens expected, the constructs open, recovery at the next declaration, in a unit and across a package | `syntax_recovery.rs` (fourteen tests), `package_recovery.rs` (ten tests) | |
| Addresses: printed only under `--addresses`, stable; `--suppress` | `../l01_29_repairs_and_printing/rejection_addresses.rs`, `../l01_29_repairs_and_printing/suppress.rs`, `suppress_binary.rs` | |
| Warnings: widening, a refused question in an accepted unit and in a rejection | `widen.rs`, `../l01_29_repairs_and_printing/widen_test.rs`, `../l01_29_repairs_and_printing/refused_warning.rs`, `../l01_29_repairs_and_printing/refused_in_rejection.rs` | |
| A refused check over a recursive type group; an overload set's waits | `group_site.rs`, `overload_cycles.rs` | |
| Constants folded the same on every machine; a power larger than the address space; `main`'s limits, the memory limit up to the address space, 2^64 bytes, and the rejection past it naming `2^64`, which compiles | `fold_machine.rs`, `../l01_29_repairs_and_printing/too_large.rs`, `main_limits.rs` | |
| A panic in zedc reported as a bug in zedc | `bug.rs` | |
| Every command of the executable prints a rejection in full | `commands_binary.rs` | |
| Batch and single-file checking agree | `batch.rs`; `syntax_recovery.rs`, `package_recovery.rs` | |
| A file that is not UTF-8: the loader's refusal passes through the same report, placed at its first bad byte | `completeness.rs` `a_file_that_is_not_utf8_is_placed_at_its_first_bad_byte` | |
| A definition whose type comes from an error already reported (`t() = 1.e;` used in `main`) gives no second error, before or after its cause | follow_on.rs (either order; arithmetic, comparison, `if`, negation, tuple index; a field read) | Row FAIL-diagnostics-follow-on, fixed |
| The headline of a member call of a name in no scope (`1.e`) is as short as `` `e` is not defined. `` | member_headline.rs (each kind of literal; a parameter keeps the field-read clause; a function in scope is accepted) | Row FAIL-diagnostics-member-headline, fixed |
| The ✗ fence variants of the spec | `variants.rs` | |
| L1.29c: the four argument rows and their menus | none | Row L1.29c is open; its tests come with it. |
| L1.29e: the spelling index; L1.14a | none | Rows L1.29e and L1.14a are open. |
| The refusal of a question outside linear arithmetic (`Row::NonLinearQuestion`, `conjuncts` in `front.rs`) | none in this group | Covered by `l01_38_presburger` (step L1.38). |
| `front::syntax`, read only by `zedc fmt` | `commands_binary.rs`; `l01_19a_command_line/binary.rs` | Run through the `zedc` executable, which llvm-cov of the test executable does not count. |
| Many errors, long lines, deep nesting | `../l01_29_repairs_and_printing/scaling.rs`, `bench.rs`, `bench/` | Sizes beyond the small cases are benchmarks (P178). |
