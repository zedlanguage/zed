# Completeness: the scalar interpreter (L1.18)

Row TEST-complete-values (author P189). The code under test is the scalar words of
`crates/zed-kernel/src/words.rs` (casts, `abs`, `len`, `lower`, `upper`, `trim`, `sum`), the
float text readers of `num/float_text.rs`, the arithmetic arrows and failure merging of
`eval.rs`, and the float and value printing of `print.rs` and `value.rs`. Expected results are
from DESIGN.md step L1.18 and the sections it cites (sec:corner_cases, "Casts are domain
proofs"; sec:failure). Tests named without a file are in `completeness.rs`.

llvm-cov, as a floor, over both groups' tests (l01_17 and l01_18 together, benchmarks left
out), lines covered before the completeness tests and after:

| File | Before | After |
|---|---|---|
| `words.rs` | 79.66% | 85.78% |
| `num/float_text.rs` | 96.56% | 96.79% |
| `text.rs` | 64.40% | 92.04% |
| `value.rs` | 56.91% | 56.98% |
| `num.rs` | 83.66% | 83.51% |
| `num/fast.rs` | 81.63% | 81.55% |
| `eval.rs` | 51.14% | 51.19% |
| `print.rs` | 46.32% | 46.32% |
| all eight | 68.70% | 70.31% |

`num.rs`, `value.rs` and `num/fast.rs` differ by a few lines between two runs of the same tests (by
0.1 point at most), so a change that small is not a change of the tests. What stays uncovered, and why:

- `words.rs`: `codePoint`, `scalar`, `utf8`, `fromUtf8` and their helpers are words of step
  L1.39c, tested there. The refusal while testing whether a number lies beyond the float range
  (lines 118-121) needs a number agreeing with the largest finite float's rounding boundary
  in every leading bit; the rounding refusal it shares its error with is tested at `f64`
  (`l01_17` `memory_check.rs` `rounding_near_a_boundary_is_refused_when_memory_is_short`) and
  at `f32` (`rounding_near_an_f32_boundary_is_refused_when_memory_is_short`). `len` past
  `i64::MAX` characters cannot be built in a test. `room_to_print` of a float or an atom inside
  a composite runs only under a lowered memory limit, tested in `l01_17` `memory_check.rs`.
- `eval.rs`: generators, folds, fixpoints, families, ports and definedness belong to steps
  L1.19 to L1.24 and are tested there.
- `print.rs`: the printer of kernel terms (`lay_out`, `render`, `pattern_out`) prints terms in
  messages, steps L1.15 and L1.29.
- `num.rs`, `num/fast.rs`: modular inverses, the Bezout coefficients and the crossovers between
  multiplication and division methods are reached at widths only the benchmarks build
  (`bench` modules, run with `--bench`), and `literal_text` and `integer_text` print types in
  messages (L1.26a, L1.29).
- `value.rs`: family operations (L1.22), `Debug` output, and ZIR's power text (L1.32).

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| An arrow for each kind: `+ - * /` on `int`, `rat`, `f32`, `f64` | `failures.rs`, `f32.rs` `arithmetic_rounds_once_to_f32`, `l01_17` `numbers.rs` | |
| Two kinds select no arrow | `failures.rs` `mixed_kinds_select_no_arrow`, `l01_17` `comparisons_and_sums_across_kinds_are_type_errors` | |
| Euclidean `div` and `mod`: the remainder is never negative, for each sign pair | `failures.rs` `euclidean_division_keeps_the_remainder_non_negative` | |
| `div` and `mod` at the edges: past a word, by a negative divisor, the smallest word, by 0 | `euclidean_div_and_mod_at_the_edges`, `l01_17` `edges.rs` | |
| An atom operand passes through arithmetic | `failures.rs` `one_failure_flows_through_the_arithmetic` | |
| A loose atom passes through a cast, `String`, interpolation, `sum`, `abs`, `len`, `-` | `a_loose_atom_passes_through_casts_and_words` | DESIGN L1.18 says a cast of a value that is neither a number nor a string is a type error; read with "An operation that always fails is rejected", limit (2) ("an atom an operand carries in passes through ... and is not a new failure") and "A cast of an atom gives the atom", the rule is about data (tuples, `bool`), not loose atoms. Decided by those past decisions |
| `min` and `max` pass a failure on | `words.rs` `min_and_max_pass_a_failure_on` | |
| Two failures merge into `#errs({…})`; merges flatten; `else` replaces a merge | `failures.rs` `two_failures_merge_into_a_set`, `a_merge_flattens_and_else_replaces_it` | |
| Merging in each number kind and in `sum` | `failures_merge_in_every_kind_and_in_sum`, `scaling.rs` `a_chain_of_failures_merges_them_all` | |
| `==` on an atom compares data and does not pass it through | `failures.rs` `an_atom_compared_with_equals_is_data`, `l01_17` `equality_of_atoms_and_f32_inside_values` | |
| Origin sets on a merged failure | | Step L1.20 brings provenance; DESIGN says no origin set until then |
| `sum` of the empty tuple is `0` | `l01_17` `edges.rs` `the_sum_of_the_empty_tuple_is_zero` | |
| `sum` of one component, and of each kind | `sum_of_one_component_and_of_each_kind`, `words.rs` `summing_an_order` | |
| `sum` of mixed kinds is a type error | `sum_of_mixed_kinds_is_a_type_error` | |
| A cast of a tuple, `bool` or comparison result is a type error | `a_cast_of_a_tuple_atom_or_bool_is_a_type_error`, `casts.rs` `a_cast_of_a_kind_it_does_not_take_is_a_type_error` | |
| The evaluator's own check refuses a word on a kind it does not take | `the_evaluator_refuses_a_word_on_a_kind_it_does_not_take` | |
| `#NaN` and `#inf` at a float cast | | Step L1.18a adds them |
| `int(s)`: optional `-`, ASCII digits, leading zeros, `"-0"` is `0` | `casts.rs` `an_int_read_from_text_takes_leading_zeros_and_a_minus_zero`, `an_int_text_is_a_minus_and_digits_alone` | |
| `int(s)` refuses `+`, space, a point, an exponent, the empty text | `an_int_text_is_a_minus_and_digits_alone` | |
| Digits of other scripts, fullwidth digits, mixed scripts are `#invalid` | `casts.rs` `digits_of_other_scripts_are_not_read` | |
| `rat(s)` reads what `String` writes, the same without `r`s, a decimal | `rat_text.rs` `text_that_string_writes_or_a_decimal_is_read`, `every_printed_rat_reads_back_to_itself`, `a_rat_text_takes_the_written_forms_and_no_others` | |
| `rat(s)` refuses every other text, a zero denominator included | `rat_text.rs` `text_that_string_never_writes_is_invalid` | |
| A decimal read by `rat` keeps or cancels its powers of 2 and 5 | `rat_text.rs` `a_decimal_keeps_the_powers_of_2_and_5_it_does_not_cancel`, `a_decimal_is_reduced_as_by_the_gcd_whatever_its_powers_of_2_and_5` | |
| `f64(s)`: `inf`, `-inf`, `nan`, `-nan`, signed forms, fractions, exponents | `an_f64_text_reads_inf_nan_and_signed_forms` | |
| `f64(s)` correctly rounded; beyond the range `#overflow` | `casts.rs` `a_float_reads_correctly_rounded_and_overflow_is_overflow` | |
| `f64("-0")` is `-0.0`; a text below half the least subnormal is a signed zero | `casts.rs` `a_float_read_from_text_keeps_the_sign_of_zero`, `a_float_text_below_the_least_subnormal_reads_as_a_signed_zero` | |
| `+5`, `.5`, `infinity`, `Infinity`, `NaN`, `1E5`, `1e+5`, `5.`, hex floats, spaces are `#invalid` | `an_f64_text_reads_inf_nan_and_signed_forms` | |
| `#underflow` on a parse | | An atom of `@fpwarn` alone, step L10.3b |
| `f32(s)` reads what `f64(s)` reads, rounded once from the digits | `an_f32_text_reads_what_an_f64_text_reads`, `f32.rs` `casts_to_f32_are_exact_or_fail` | |
| A number received in pieces reads as one | `casts.rs` `a_number_received_in_pieces_reads_as_one`, `a_number_joined_from_a_thousand_pieces_reads_as_one` | |
| `int` and `rat` of an infinity or the NaN, at `f64` and `f32`, are `#invalid`; of `-0.0` are `0` and `0r` | `int_and_rat_of_a_float_that_is_no_number_are_invalid` | |
| `int` of a float that is not whole; `rat` of a float is its exact rational | `casts.rs` `a_float_to_int_must_be_whole`, `a_float_is_an_exact_rational` | |
| `f64` of an `int` or `rat`: equal, `#overflow`, `#inexact` | `casts.rs` `a_number_to_f64_must_be_exactly_representable`, `a_number_beyond_the_largest_float_is_overflow`, `f64_of_an_int_or_rat_is_equal_or_fails_by_the_reason` | |
| `f32` of an `int`, `rat` or `f64`: equal, `#overflow` at either sign, `#inexact`, infinities and the NaN kept, an underflow `#inexact` | `f32_of_an_int_rat_or_f64_is_equal_or_fails_by_the_reason`, `f32.rs` `casts_to_f32_are_exact_or_fail` | |
| `f32` of an `f32` is itself | `f32_of_an_int_rat_or_f64_is_equal_or_fails_by_the_reason` | |
| `f32` and `f64` of an `f64` `-0.0` keep the sign | `cast_negzero.rs` | Fixed by row FAIL-values-cast-negzero; neighbors (`0.0`, tiny floats of each sign, the least subnormal, `f64` of `-inf` and `nan`) in the same file |
| `f64` of an `f32` is exact, `-0.0`, infinities, the NaN and subnormals included | `f64_of_an_f32_is_exact`, `f32.rs` `casts_from_f32` | |
| `f32(n)` exact for an `n` the checker shows within ±2^24; one past keeps `#inexact` | `f32_of_an_int_shown_within_two_to_the_24_is_exact` | |
| A cast that always fails is rejected | `f32.rs` `a_cast_that_always_fails_is_rejected` | |
| Rounding near a boundary under a memory limit | `l01_17` `memory_check.rs` `rounding_near_a_boundary_is_refused_when_memory_is_short`, `rounding_near_an_f32_boundary_is_refused_when_memory_is_short` | |
| `f32` arithmetic rounds once; NaN in gives NaN out; signed zero; subnormals; overflow to infinity | `f32.rs` | |
| `f32` `-x`, `abs`, `min`, `max` are exact, with `-0.0` and the NaN | `f32_abs_negation_min_and_max_are_exact` | |
| `f32` comparisons are IEEE 754 | `f32.rs` `f32_values_are_ordered_as_ieee_754` | |
| `f32 ^ f32` is the IEEE power rounded to `f32` | `an_f32_to_an_f32_power_is_the_ieee_power` | |
| `f32 ^ int` taken in `f64` and rounded | `f32.rs` `an_f32_to_an_int_power_is_an_f32` | |
| `f32 ^ n` with `n` beyond ±2^53 keeps the sign of the exact power | `an_f32_to_a_huge_int_power_keeps_the_sign_of_the_exact_power` | |
| Division by `0.0` or `-0.0`, and `0.0 ^ n` with `n < 0`, give an infinity at `f32` and `f64` | `division_by_a_float_zero_and_zero_to_a_negative_power_are_infinite` | |
| `sqrt` and `fma` at `f64` and `f32`: rounding, signed zero, infinities, the NaN | `sqrt_fma.rs` | |
| No back end contracts `a * b + c` into an `fma` | `sqrt_fma.rs` `fma_at_f64_rounds_once_and_a_multiply_and_an_add_round_twice`, `random_operands_give_the_same_bits_in_the_kernel_and_in_native_code` | |
| A literal operand of `sqrt` takes `f64`; `int`, `rat` or two formats are rejected | `sqrt_fma.rs` `a_literal_operand_takes_f64_since_sqrt_and_fma_take_float_formats_alone`, `an_int_or_rat_operand_or_two_formats_are_rejected` | |
| `String` of an `f32` is the shortest text that reads back in `f32` | `f32.rs` `an_f32_prints_the_shortest_text_that_reads_back_in_f32` | |
| ZIR's text writes an `f32` constant with its suffix | | Step L1.32 (canonical ZIR) tests the ZIR text |
| A decimal literal a use fixes at `f32` is read from its digits | `f32.rs` `a_use_fixes_a_decimal_literal_at_f32`, `literals.rs` `an_f32_literal_rounds_by_the_same_rule` | |
| Float printing: shortest form, fixed notation range, ties, names of infinities and NaN, round trip | `floats.rs` | |
| Float literals: rounding, out of range, subnormal, zero at any exponent, long digit strings | `literals.rs` | |
| `String` of each kind of data: atom inside a tuple, named payload in code-point order, nested tuple, `bool`, `rat`, string | `string_writes_each_kind_of_data`, `words.rs` `string_writes_any_value_and_leaves_a_string_alone` | |
| A one-component tuple prints with its comma | `a_one_component_tuple_keeps_its_comma` | |
| A printed string escapes `\\`, `\"`, `\n`, `\r`, `\t`, `\0`, `\$` before `{`, and characters with no visible form, as `\u{X}`; inside a tuple, and printed twice through `String` | `a_printed_string_escapes_what_a_terminal_does_not_show` | |
| Showing a function is a type error | `showing_a_function_is_a_type_error` | |
| `len` counts code points | `string_words_on_empty_and_unicode_text` | |
| `len` counts units at `U8String` | | `U8String` is a word of row STR-types, not yet in the language (`l02_03` `later_words.rs`) |
| `lower` and `upper` are full case mappings (`ß`, `İ`); `trim` takes Unicode white space; each on the empty string | `words.rs` `string_words_are_unicode`, `cleaning_a_user_name`, `string_words_on_empty_and_unicode_text` | |
| `abs`, `min` and `max` of each number kind | `words.rs` `abs_of_each_number_kind`, `min_and_max_of_each_number_kind`, `min_and_max_take_two_numbers_of_one_kind` | |
| `min` and `max` of tuples | `tuple_min_max.rs` | |
| Too many or too few arguments to a word | `word_args.rs` | |
| Messages name each primitive as the program writes it | `prim_names.rs` | |
