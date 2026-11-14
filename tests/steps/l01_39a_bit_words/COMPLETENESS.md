# Completeness: the bit words (L1.39a)

Row TEST-complete-reduced (author P189). The code under test is the bit words `bitAnd`,
`bitOr`, `bitXor`, `shl`, `shr`, `popCount`, `bitNot`, `leadingZeros`, `trailingZeros`, `rotl`,
`rotr` and `f64Bits`: their kernel evaluation (`zed_kernel::bits::word`, its machine path
`small` and exact path `big`, the domain checks `domain` and `below_two_pow`), their checking
(`bits`, `bits_step` and `bit_domains` in `zedc-check`, with narrowing by tests), and their
forward transfer (`zedc::store::interval::bit_word`, which the lattices note of the test
audit found without a unit test: it is tested here through its public path
`zedc::store::interval::bit_word`, in `transfer.rs` and below). Expected results are from
DESIGN.md step L1.39a, sec:domains and the currying rule of sec:values_morphisms.

llvm-cov of this group's tests, as a floor, regions (lines) before → after:
`crates/zed-kernel/src/bits.rs` 48.03% (50.69%) → 51.84% (56.20%);
`crates/zedc-check/src/check/walk.rs` 49.94% (52.32%) → 50.74% (53.23%);
`crates/zedc-lattice/src/interval.rs` 68.02% (71.73%) → 68.02% (71.73%). Every line of
`bit_word` that serves an L1.39a word was reached before. The lines of `bits.rs` still not
reached here are those of the L1.39f words (`byteSwap`'s width, the funnel shifts' `k`,
`mulHi`'s parameters), covered by `l01_39f_int_machine_ops`, and the kernel's answer to a call
with the wrong number of arguments, which the checker rejects before any call is run.

Tests in `completeness.rs` unless a file is named.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| The named values of DESIGN (`bitNot(5, width: 3)` is 2, `rotl(8, 1, width: 4)` is 1, `trailingZeros(0, width: 8)` is 8, masking a byte) | `values.rs` `the_named_cases`, `masking_a_byte_and_packing_two` | |
| Each word at 0, 1, `2^63` and `2^64 + 1` where its domain allows | `values.rs` `each_word_at_zero_and_one`, `each_word_at_two_to_the_63`, `each_word_at_two_to_the_64_plus_one` | |
| Each word against a reference at every width; zero, all ones, width one, width zero, the machine edge | `reference.rs` `every_word_against_the_reference_at_every_width`; `corners.rs` all | |
| Operands of several limbs; kept ends (a power of 2 kept by its exponent) | `shapes.rs` `the_bit_words_on_operands_of_several_limbs_agree_with_the_written_out_value`; `kept_ends.rs` all | |
| A shift count is never masked; `shl`/`shr` of a negative `x` | `values.rs` `a_shift_count_is_never_masked`; `each_word_in_a_function_body_under_tests_of_its_operands` | |
| `rotl`/`rotr` by `k` at least the width rotate by `k` places | `each_word_in_a_function_body_under_tests_of_its_operands` (`rotl(1, 5, width: 4)` is 2) | |
| `f64Bits` the IEEE 754 encoding; NaN gives the canonical NaN in the interpreter and the executable | `reference.rs` `f64_bits_is_the_ieee_754_encoding`; `nan.rs` all | |
| `f32Bits`, `f16Bits`, `bf16Bits` | | plan row L1.18a (the formats `f16` and `bf16`; the three words are held in `PENDING` of `l02_03_name_resolution`) |
| A negative operand is rejected and the derivation names it; through a name; each operand; an `x` wider than its width | `errors.rs` first five tests | |
| A call that does not fit; nested words checked with the inner values; a name carries what its text shows | `errors.rs` `a_call_that_does_not_fit_is_rejected`, `bit_words_nested_in_each_other_are_each_checked_with_the_inner_values`, `a_name_carries_what_its_text_shows` | |
| The kernel rejects values outside the domain: machine path, exact path, no integer, `f64Bits` of no f64 | `errors.rs` `the_kernel_rejects_values_outside_the_domain`; `the_kernel_refuses_a_negative_operand_on_the_machine_path`, `the_kernel_refuses_each_operand_outside_its_domain_on_the_exact_path` | |
| The domain `0 ..< 2^w` at its ends, for a negative `x` or `w`, a non-int, and past `i64` | `the_domain_of_an_x_with_a_width_is_below_two_to_the_width` | |
| Each word in a function body, its operands bounded by `if` tests, through test tables | `each_word_in_a_function_body_under_tests_of_its_operands`; `narrowing.rs` all | |
| An operand not bounded at each word: no test, a one-sided test, one digit too wide | `an_operand_not_bounded_by_its_tests_is_rejected_at_each_word`; `narrowing.rs` rejection tests | |
| Refinement types on a parameter | | step L10.1: not compiled by this zedc yet; the `if` tests stand in |
| Generic wrappers pass the need on; lambdas and curried calls take it; type variables | `generic.rs` all | |
| A receiver; a receiver chain; a tuple, an interpolation, nested words, an expression operand, a comparison, a lambda | `values.rs` `a_receiver_is_the_first_operand`; `each_word_in_other_positions` | |
| `width` positional, missing, twice; an operand named; a width given to a word with none; too many or too few | `the_width_is_the_only_named_parameter` | the message names the signature and has no repairs: FAIL-bitword-arity-message (filed from L1.39f, with `bitAnd(1)` among its cases) |
| An operand of another kind: rat, suffixed float, bool, string, tuple; `f64Bits` of a string or a bool | `an_operand_of_another_kind_is_rejected`; `generic.rs` `an_argument_of_a_declared_int_type_is_rejected` | |
| Currying by `width` | `a_word_curries_by_its_width_alone` | |
| The domain of a word curried with `...` (`bitNot`, `rotl`) | | fails: FAIL-bitword-curry-domain (filed from L1.39f, with `bitNot` and `rotl` among its cases) |
| A failure passes through | `values.rs` `a_failure_passes_through` | |
| Forward transfer: sound on random pairs; single values; `shl(1, 30)` inside `i32` and `shl(1, 31)` outside; `x.bitAnd(255)` in `int[0..=255]` | `transfer.rs` all | |
| Forward transfer on ranges at the bounds DESIGN states: `bitAnd` at the smaller upper bound, `bitOr`/`bitXor` at an upper bound of `2^k - 1` and of `2^k`, `leadingZeros` up to `w`, `shl`/`shr` as product and quotient, a width past `i64` | `transfer.rs` `the_rules_on_ranges`; `the_bounds_design_states_on_ranges` | |
| Each word's transfer bound read back by a second word's domain, at the width that fits and one narrower | `the_bounds_of_forward_transfer_are_read_by_a_second_word` | |
| `bitAnd` in the linear-relation rung (`x <= a`, `x <= b`) | `rung2.rs` all | |
| A chain of 20,000 bindings | `deep.rs` | |
| Scaling | `bench/` | |
| Negative operands | | step L1.39d |
| Units and facets on an operand | | this zedc does not compile a declared type with `units` yet |
