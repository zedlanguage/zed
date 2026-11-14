# M0.9 kernel evaluator: cases and the tests that cover them

Code under test: `crates/zed-kernel/src/eval.rs` (the evaluator), `value.rs` and `prov.rs`.
Measured with `-C instrument-coverage` and `llvm-cov` over this group alone, regions% / lines%,
before the last test of `complete.rs` was added: `eval.rs` 74.11 / 74.07 before and 80.88 /
78.81 after; `value.rs` 56.38 / 63.76 and 56.13 / 63.62 (the count of generic instances changes
the total); `prov.rs` 74.74 / 77.17 unchanged.

| Case | Test that covers it | Or reason none is needed |
|---|---|---|
| Integer arithmetic past a word and back | complete.rs `integer_arithmetic_widens_past_a_word_and_comes_back` | |
| Integer division by zero; Euclidean remainder | complete.rs `integer_division_by_zero_is_an_atom_and_the_remainder_is_never_negative` | |
| Rationals: reduced, `+ - * /`, negative power, divide by zero | complete.rs `rationals_stay_reduced_and_exact`, `the_remaining_operand_kinds_of_arithmetic_order_and_reads` | |
| Floats at `f64` and `f32`: arithmetic, NaN, signed zero, `pow`, `min`/`max`, comparisons | complete.rs `floats_follow_ieee_754_at_f64_and_round_once_at_f32`, `the_remaining_operand_kinds_of_arithmetic_order_and_reads` | |
| `sqrt` at each width, of `-0.0` and of a negative | complete.rs `the_remaining_operand_kinds_of_arithmetic_order_and_reads`; l01_18_scalar_interpreter sqrt_fma.rs | |
| `f32 ^ int`, exponent past 2^53 of each parity and sign | complete.rs `the_remaining_operand_kinds_of_arithmetic_order_and_reads` | |
| NaN in, NaN out through `pow` | complete.rs `the_remaining_operand_kinds_of_arithmetic_order_and_reads` | |
| `fma` | l01_18_scalar_interpreter sqrt_fma.rs | |
| `min`, `max`, `not`, `and`, `or`; ordering strings and tuples | complete.rs `min_max_not_and_or_and_the_comparisons_of_non_numbers` | |
| `min`/`max` of two tuples; tuples they cannot order | complete.rs `the_remaining_operand_kinds_of_arithmetic_order_and_reads`; l01_18_scalar_interpreter tuple_min_max.rs | |
| Strings and the text words | complete.rs `strings_concatenate_and_the_text_words_work_on_code_points` | |
| Tuples and atoms built and read; `tupleGet`/`at` past the end, at -1, a big integer, a string; `at` on an interval family | complete.rs `tuples_and_atoms_are_built_and_read`, `the_remaining_operand_kinds_of_arithmetic_order_and_reads` | |
| `sum` of a tuple; failures merged | complete.rs `sum_of_a_tuple_is_its_total_and_merges_its_failures` | |
| Numeric casts exact or an atom | complete.rs `numeric_casts_are_exact_or_give_an_atom` | |
| `show` | complete.rs `show_writes_data_and_passes_an_atom_through` | |
| A failure atom through every primitive but tuple, atom, `==`, `!=` | complete.rs `a_failure_atom_passes_through_every_primitive_but_tuple_atom_eq_and_ne` | |
| Applying a family | complete.rs `applying_a_family_reads_its_entry` | |
| `match`, first matching arm | complete.rs `match_takes_the_first_arm_whose_pattern_matches` | |
| Ill-typed application reported as a compiler bug | complete.rs `an_ill_typed_application_is_reported_as_a_compiler_bug_naming_it` | |
| Families: reads, union, order, families as leaves, scopes | scaling.rs (6 tests) | |
| Shared values: records, lists, tuples, NaN, families, relations | shared.rs (14 tests) | |
| Empty inner levels: fold, discard, remap, move, rank | empty_levels.rs (11 tests) | |
| Provenance of failures | provenance.rs (23 tests) | |
| Deep values and terms; a failed run leaves the evaluator usable | deep.rs, deep_values.rs; benchmarks in bench, binary.rs, deep_scaling.rs | |
| Bit words | l01_39a_bit_words | |
| Code points | l01_39c_code_points | |
| Globals (`push`, `global`, `run_under`) | l01_28_staging | Called by zedc-stage only |
| Sites (`set_sites`) and a run-time error placed in the text | l01_19_whole_file_ports | Set by `zedc::run` (run.rs `wave`) when a program runs |
| Ports (`ask_port`, `call_port`) | l01_19_whole_file_ports, l01_19c_environment | |
| Definedness fixes (`entry_ended`, `demand`, a partial family) | m0_04_corpus_references | Fixes enter at later layers' terms |
| An equality or order test whose work exceeds memory (`test_too_large`, `order_too_large`) | none | Needs an input of unusual size, so it is a benchmark, not a regular test (author P178) |
