# Completeness: integer machine operations (L1.39f)

Row TEST-complete-reduced (author P189). The code under test is the seven machine words
`mulHi`, `bitReverse`, `byteSwap`, `pdep`, `pext`, `funnelShl` and `funnelShr`: their kernel
evaluation (`zed_kernel::bits::word`, its machine path `small`/`machine_op` and its exact path
`big`), their checking (`bits`, `bits_step` and `bit_domains` in `zedc-check`), and their forward
transfer (`zedc::store::interval::bit_word`). Expected results are from DESIGN.md step L1.39f,
the operand domains of step L1.39a, and the currying rule of sec:values_morphisms. llvm-cov of
this group's tests, as a floor, regions (lines): `crates/zed-kernel/src/bits.rs` 71.05%
(78.79%) before, 71.97% (79.61%) after; `crates/zedc-check/src/check/walk.rs` 15.18% (16.33%)
before, 33.44% (35.84%) after; `crates/zedc-lattice/src/interval.rs` 27.76% (30.89%) before,
33.33% (38.12%) after. The lines of `bits.rs` still not reached are the words of step L1.39a,
`f64Bits`, and `NumberTooLarge` (below); `l01_39a_bit_words` covers the L1.39a words.

Tests in `completeness.rs` unless a file is named.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| The named values of DESIGN (`mulHi(2^63, 4, width: 64)` is 2, and the rest) | `values.rs` `the_named_cases` | |
| Each word on every operand of up to 8 digits, and on random 64-digit operands | `reference.rs` `every_operand_of_up_to_eight_digits`, `random_64_digit_operands` | |
| Each word at every width from 8 to 128, and at its corners (0, 1, all ones, the top digit) | `reference.rs` `random_operands_at_every_width_from_8_to_128`, `the_corners_at_every_width`; `values.rs` `zero_all_ones_and_the_top_digit_through_the_surface` | |
| Width 0 and width 1; `pdep`/`pext` with an empty and a full mask | `a_word_at_width_zero_and_one` | |
| A width past `u128` (the exact path): 0, 1, the top digit, `mulHi` and the funnel shifts | `a_width_past_the_machine_words_takes_the_exact_path` | |
| The machine and the exact paths agree; both fail outside the domain | `native.rs` both tests; `reference.rs` `pdep_and_pext_agree_on_wide_and_kept_operands` | |
| Algebraic laws: `bitReverse` an involution, `pext` undoes `pdep`, `funnelShl(x, x, k)` is `rotl`, `byteSwap` reverses bytes | `values.rs` `bit_reverse_is_an_involution_and_pext_undoes_pdep`, `funnel_shl_of_one_word_twice_is_rotl`, `byte_swap_reverses_the_bytes_of_a_word` | |
| `pdep`/`pext` read only the digits the mask reaches | `reference.rs` `pdep_and_pext_read_only_the_digits_the_mask_reaches` | |
| `byteSwap` at a width not a multiple of 8 names the width; a funnel shift by `k = width` names `k` | `errors.rs` first two tests | |
| A negative operand; an operand at least `2^width`; the derivation follows a name | `errors.rs` `a_negative_operand_is_rejected`, `each_operand_read_as_width_digits_is_checked`, `the_derivation_follows_a_name_to_its_definition` | |
| A negative operand beside one past `i64`, at the kernel | `a_width_past_the_machine_words_takes_the_exact_path` | |
| An operand that is no integer, at the kernel | `the_kernel_refuses_an_operand_that_is_no_integer` | |
| The kernel rejects the values the checker rejects | `errors.rs` `the_kernel_rejects_the_same_values_at_run_time` | |
| Each word in a function body, its operands bounded by `if` tests, through test tables | `each_word_in_a_function_body_under_tests_of_its_operands` | |
| An operand not bounded: no test, a one-sided test, a test one too wide, a shift count one too large | `an_operand_not_bounded_by_its_tests_is_rejected_at_each_word` | |
| Refinement types on a parameter (`x: int[0..<2^16]`) | | step L10.1: this zedc does not compile refinements yet; the `if` tests above stand in |
| A word as a receiver (`x.bitReverse(width: 8)`) | `values.rs` `a_receiver_is_the_first_operand` | |
| A word in a tuple, an interpolation, nested in another word and in itself, on an expression operand, with a named width, in a lambda | `each_word_in_other_positions` | |
| A lambda passes the need of its word to its caller | `each_word_in_other_positions` | |
| `width` missing, positional, unknown, twice; an operand named; a width given to `pdep`/`pext`; too many or too few operands | `the_width_is_the_only_named_parameter` | the message names the word and carries the repairs: `a_malformed_call_of_a_word_names_the_word_and_its_repairs`, `each_misfit_of_a_word_names_the_word_and_offers_no_declaration_edit` (FAIL-bitword-arity-message) |
| An operand of another kind: a rat, a suffixed float, a string, a bool, a tuple | `an_operand_of_another_kind_is_rejected` | |
| An array display as an operand | | this zedc does not compile array displays yet |
| Currying by `width` alone, values | `a_word_curries_by_its_width_alone` | |
| Currying that leaves out an operand, leaves out nothing, or on `pdep`/`pext` (no named parameter) | `a_word_curries_by_its_width_alone` | |
| The domain of a word curried with `...`: each word, both sides of the width and of a funnel shift's `k`, through renaming, returning and passing | `a_word_curried_with_dots_checks_its_domain_at_compile_time`, `the_width_boundary_and_the_funnel_shift_k_are_checked_through_the_curried_function`, `the_curried_function_is_checked_when_it_is_renamed_returned_or_passed` | |
| A failure atom as an operand passes through each word; `else` gives the default | `a_failure_passes_through_each_word` | |
| Forward transfer: `mulHi`, `bitReverse`, `byteSwap` below `2^w`, `pdep` at most `mask`, read back by a second word's domain at the width that fits and one narrower | `the_bounds_of_forward_transfer_are_read_by_a_second_word`; `transfer.rs` `the_bounds_design_states` | |
| Forward transfer of `pext` below `2^m`, `m` the most one digits of a mask in its hull: a single mask, a range, an all-ones end, a one-digit mask, an unbounded mask, a kept end; the count checked against every member on machine and wide words | `pext_popcount.rs` all four; `transfer.rs` `the_bounds_design_states` | FAIL-pext-transfer-popcount, fixed |
| A funnel shift gives a word of its width | `a_funnel_shift_gives_a_word_of_its_width` | |
| `bit_word` sound on random intervals; a single value gives the value | `transfer.rs` `the_transfer_is_sound_on_random_intervals`, `single_values_give_the_value` | |
| Scaling: n and 8n `u64` values; `pdep`/`pext` O(w); the width words O(w); the `pext` transfer O(n) in the digits of the mask hull | `bench.rs` all four | |
| Lowering to machine instructions | | step L24.2a |
| `NumberTooLarge` from the exact path | | no width or operand the checker accepts makes a result too large to hold: the result is below `2^width`, and `2^width` is computed by the checker first |
| Units and facets on an operand | | this zedc does not compile a declared type with `units` yet (`n: int with units("B") = 3;` is refused as not compiled) |
