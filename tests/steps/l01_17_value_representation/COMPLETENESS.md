# Completeness: value representation (L1.17, L1.17a)

Row TEST-complete-values (author P189). The code under test is the value representation of
`crates/zed-kernel`: `value.rs` (values, their natural order, equality and hashing), `num.rs`
and `num/fast.rs` (integers past a word kept as powers of primes, `rat`, the memory asks of
their builds), `text.rs` (strings, joined as a rope) and the parts of `eval.rs` and `print.rs`
that build, compare and print values; and the checker's rejections that L1.17 names. Expected
results are from DESIGN.md steps L1.17 and L1.17a, sec:domains, sec:order and the reference
semantics (step M0.9). Tests named without a file are in `completeness.rs`.

llvm-cov, as a floor, over both groups' tests (l01_17 and l01_18 together, benchmarks left
out), lines covered before the completeness tests and after:

| File | Before | After |
|---|---|---|
| `value.rs` | 56.91% | 56.98% |
| `num.rs` | 83.66% | 83.51% |
| `num/fast.rs` | 81.63% | 81.55% |
| `text.rs` | 64.40% | 92.04% |
| `words.rs` | 79.66% | 85.78% |
| `num/float_text.rs` | 96.56% | 96.79% |
| `eval.rs` | 51.14% | 51.19% |
| `print.rs` | 46.32% | 46.32% |
| all eight | 68.70% | 70.31% |

`num.rs`, `value.rs` and `num/fast.rs` differ by a few lines between two runs of the same tests (by
0.1 point at most), so a change that small is not a change of the tests. What stays uncovered, and why:

- `value.rs`: the family operations (union, insert, remove, family equality) are step L1.22;
  `Debug` output is for the implementation's own messages; the reader of ZIR's power text is
  step L1.32.
- `num.rs`, `num/fast.rs`: the modular inverse, the Bezout coefficients and the crossovers
  between multiplication and division methods are reached only at the widths the benchmarks
  build (`bench` modules, run with `--bench`; `subquadratic.rs` checks the results at the
  crossovers); `literal_text` and `integer_text` print types in messages (L1.26a, L1.29).
- `text.rs`: a join past `usize::MAX` bytes cannot be built. `flat`, which zedc's ports and
  `zedc run` call (`run.rs`, `rows.rs`), is tested with them; the kernel's words call
  `try_flat`, which is covered. `is_flat` is called only by the rope's unit tests
  (`text::tests`), which with l01_36 test its balance and scaling. The `From<&String>`,
  `From<Text>`, `PartialOrd` and `Debug` impls have no use in these steps; the arms for a
  tree that is a node at the top, which a text never is, and for joining onto an empty text,
  which `join` returns early from, are not reached; the second memory ask of `try_shared`,
  for its copy, is refused only when the first, for the text, was just given.
- `eval.rs`, `print.rs`: generators, folds, fixpoints, families and ports are steps L1.19 to
  L1.24; the printer of kernel terms prints terms in messages, steps L1.15 and L1.29.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| An integer is a word while it fits and widens past it, and narrows back | `numbers.rs` `integers_widen_past_64_bits_and_narrow_back`, `edges.rs` `the_smallest_word_widens_under_negation_and_narrows_back` | |
| Big literals in any base | `numbers.rs` `big_literals_in_any_base_and_euclidean_division` | |
| A number far past a word is exact: `3 ^ 10000000`, `1e999999r` | `numbers.rs` `a_number_far_past_a_machine_word_is_exact` | |
| `2^2^100` is a value: order, equality and remainders without its digits | `two_to_two_to_the_hundred_is_a_value` | |
| Kept powers agree with the built value; their corner cases; close products | `powers.rs` | |
| A sum factors out the shared powers and builds nothing above them | `powers.rs` `kept_powers_agree_with_the_built_value`, `corner_cases_of_kept_powers` | |
| A power of a wide base is built; past a 64-bit exponent it is refused | `powers.rs` `a_power_of_a_wide_base_is_built`, `a_power_of_a_wide_base_to_an_exponent_beyond_64_bits_is_refused` | |
| An exact division by a huge power builds nothing | `powers.rs` `an_exact_division_by_a_huge_power_builds_nothing` | |
| Products and quotients agree with `num_bigint` across the method crossovers | `subquadratic.rs`, `products.rs` `a_product_or_quotient_by_a_word_is_exact` | |
| Sums, differences, quotients and remainders agree with `num_bigint` | `in_place.rs` `sums_differences_quotients_and_remainders_agree_with_num_bigint`, `wide_differences_quotients_and_remainders_are_exact` | |
| `x^n` on an `int` needs `n : int[0..]`; rejected otherwise, with the test and `rat` repairs | `l01_26` `soundness.rs` `an_int_power_needs_an_exponent_of_at_least_zero`, `an_int_power_whose_exponent_may_be_below_zero_offers_a_test_of_it`; `l01_29` `power_repairs.rs` | |
| `x^n` on a `rat` takes either sign of `n`; `#divByZero` only for `0r` to a negative power | `a_rat_power_in_a_program_takes_either_sign`, `powers.rs` `a_rat_takes_an_int_exponent_of_either_sign` | |
| The checker drops `#divByZero` where `x` holds no `0r` or `n : int[0..]` | `l01_26` `soundness.rs` `zedc_run_offers_and_runs_the_exact_rat_power`, `a_port_takes_an_operation_on_literals_whose_divisor_is_no_zero` | |
| `0`, `1`, `-1`, `0r`, `1r`, `-1r` to any power stay small | `numbers.rs` `powers_of_zero_one_and_minus_one_stay_small`, `powers.rs` `a_unit_or_zero_base_builds_no_exponent`, `powers_of_zero_one_and_minus_one_as_rats_stay_small` | |
| `rat(n)` of an `n` whose interval holds no `0` has no `0r`, so `1r / rat(n)` and `rat(n)^-1` are total | `l01_26` `soundness.rs` `zedc_run_offers_and_runs_the_exact_rat_power` | |
| A decimal literal base meets an `int` exponent at `rat` | `a_decimal_literal_to_an_int_power_is_a_rat` | |
| A `rat` is reduced with a positive denominator and prints `1r/3r` | `a_rat_is_reduced_with_a_positive_denominator`, `numbers.rs` `rationals_are_exact` | |
| `/` by `0r` is `#divByZero` | `numbers.rs` `rational_division_by_zero_is_an_atom` | |
| Euclidean `div` and `mod`; the smallest word by small negative divisors and by 0 | `numbers.rs` `big_literals_in_any_base_and_euclidean_division`, `edges.rs` | |
| The natural order ranks kinds atom, `bool`, number, string, tuple | `order.rs` `kinds_order_atoms_bools_numbers_strings_tuples` | |
| Character, record, morphism, keypath and family in the natural order | | Characters are row STR-types, records later steps, families L1.22 |
| Numbers order by exact value across kinds; a family keyed by mixed numbers | `order.rs` `numbers_order_by_value_across_kinds`, `a_family_keyed_by_mixed_numbers_visits_them_by_value` | |
| Equal values order `int`, `rat`, `f32`, `f64`; a float by its dyadic rational; infinities at the ends | `equal_numbers_order_by_kind_and_floats_by_their_exact_value` | |
| Zeros, subnormals and the NaN in the natural order | `edges.rs` `the_natural_order_places_zeros_subnormals_and_nan` | |
| `f16` and `bf16` in the order | | Step L1.18a |
| `==` and `!=` are structural, IEEE 754 at every float inside, `f64` and `f32` | `equality.rs` `float_equality_and_comparison_follow_ieee`, `ieee_equality_reaches_inside_tuples_and_atoms`, `equality_of_atoms_and_f32_inside_values` | |
| `==` compares atoms as data, payloads by position and by name | `atoms.rs` `a_named_payload_is_a_struct_whatever_the_written_order`, `equality_of_atoms_and_f32_inside_values` | |
| Keys tell signed zeros apart and read one NaN | `equality.rs` `keys_still_tell_signed_zeros_apart_and_read_one_nan` | |
| `<` `<=` `>` `>=` IEEE 754 on floats: zeros equal, NaN unordered, `min`/`max` of zeros and NaN | `edges.rs` `the_two_zeros_compare_equal_under_ieee`, `nan_is_unordered_and_its_negation_is_the_canonical_nan`, `subnormals_order_between_zero_and_the_normals`, `min_and_max_put_the_negative_zero_below_and_nan_absorbs` | |
| Comparisons within one kind: strings, `bool`, tuples component by component, `rat`, wide ints | `comparisons_within_one_kind` | |
| Comparing two kinds, numbers of two kinds included, is a type error; so is `r + n` | `comparisons_and_sums_across_kinds_are_type_errors`, `numbers.rs` `numbers_of_different_kinds_do_not_mix`, `edges.rs` `zeros_of_two_kinds_do_not_compare` | |
| Showing a value that holds a function is a type error | `l01_18` `completeness.rs` `showing_a_function_is_a_type_error`, `l01_26` `soundness.rs` `a_function_is_not_shown_and_not_put_in_a_tuple` | |
| An atom's payload may hold a function; building one is no error | `building_an_atom_that_holds_a_function_is_no_error` | |
| A tuple may hold a function, `(f, 1)`; building one is no error | **FAIL-values-function-in-tuple** | Rejected today; filed, test in `wt/failing-tests/FAIL-values-function-in-tuple.rs` |
| A struct or an array that holds a function, `Pair(fst: f, snd: 1)` | | zedc does not compile struct declarations or arrays yet; the step that adds them tests this |
| `==` on functions is a type error until their domain is enumerable; a function deep in a tuple or a payload, or reaching one through a generic call | `equality.rs` `functions_compare_only_over_an_enumerable_domain`, `a_function_deep_in_a_tuple_is_reported_once_where_it_is_written`, `a_function_in_an_atom_s_payload_is_refused_by_equality`, `a_function_nested_in_payloads_and_tuples_is_refused`, `a_function_reaching_a_payload_through_a_generic_call_is_refused_by_equality` | |
| A payload is all by position or all by name; by name a struct in code-point order | `atoms.rs` `a_named_payload_is_a_struct_whatever_the_written_order`, `payload_errors` | |
| A positional payload holds any value, atoms as data | `atoms.rs` `a_positional_payload_holds_any_value_atoms_included` | |
| Patterns by name match with extra fields and bind `f:`; by position only by position | `atoms.rs` `else_matches_a_payload_by_name_and_binds_its_fields`, `nested_atom_patterns_by_position_and_by_name`, `fields.rs` | |
| A string joined from many blocks is equal, ordered and hashed as its text, as a left fold, a right fold or a balanced tree of joins | `a_joined_string_is_compared_ordered_and_hashed_by_its_text_alone` | |
| A joined string orders before a longer one it begins; a short string joined before a long one | `a_joined_string_is_compared_ordered_and_hashed_by_its_text_alone` | |
| A join past `usize::MAX` bytes (`TooLong`) | | Cannot be built in a test |
| String words, atom names, padding and cuts of a joined string are those of its text | `string_copies.rs` | |
| The syntax tree shares a literal's digits and a string literal's text | `asks.rs` `the_syntax_tree_shares_a_literals_digits`, `string_copies.rs` `the_syntax_tree_shares_a_string_literals_text` | |
| A sum, power, `div`, `mod` or `String` of a number asks for its memory and is refused by name and width | `asks.rs`, `in_place.rs`, `products.rs` | |
| L1.17a: an order of numbers that agree in many bits is refused when memory is short; equality of them still answers | `memory_check.rs` `ordering_numbers_that_agree_in_many_bits_is_refused_when_memory_is_short` | |
| L1.17a: an equality that must copy a number to move a prime out | `memory_check.rs` `equality_that_must_copy_a_wide_number_is_refused_when_memory_is_short` | |
| L1.17a: rounding near a boundary of `f64` and of `f32` | `memory_check.rs` `rounding_near_a_boundary_is_refused_when_memory_is_short`, `rounding_near_an_f32_boundary_is_refused_when_memory_is_short` | |
| L1.17a: printing a tuple asks for its whole text first | `memory_check.rs` `printing_a_composite_holding_a_number_too_large_to_build_is_an_error`, `printing_many_copies_of_a_number_asks_for_the_whole_text` | |
| L1.17a: a family's key order refused | `memory_check.rs` `a_family_key_order_refused_is_an_error` | |
| L1.17a: each check answers exactly when the memory is given | `memory_check.rs` `equality_and_order_of_wide_numbers_are_exact_when_memory_is_given`, `close_numbers_order_and_round_exactly_when_memory_is_given` | |
| The L1.17a examples at 2^40 bits under 1 GiB | | Tested at 2^24-bit widths under a matching lowered limit (`margin`); a size of 2^40 bits is a benchmark |
| Order of power towers sharing a prime, and by Baker's bound | `powers.rs` `close_products_compare_exactly`; `l01_29` `power_repairs.rs` `the_least_power_of_a_tower_under_a_test_is_exact` | The Baker class is row POW-tower |
