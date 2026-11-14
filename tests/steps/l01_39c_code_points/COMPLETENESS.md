# Completeness: code points and UTF-8 bytes (L1.39c)

Row TEST-complete-reduced (author P189). The code under test is the four prelude words this
zedc builds for step L1.39c, `codePoint`, `scalar`, `utf8` and `fromUtf8`: their kernel
evaluation (`crates/zed-kernel/src/words.rs`, the arms for the four words and the functions
`first_char`, `utf8` and `from_utf8`), their signatures and the atoms the checker lists for them,
and their native lowering. Expected results are from DESIGN.md step L1.39c, sec:failure (an
operation that always fails) and sec:values_morphisms (calls). llvm-cov of this group's tests,
as a floor: every line of the four arms and of `first_char`, `utf8` and `from_utf8` was reached
before and after; `crates/zed-kernel/src/words.rs` as a whole (it holds other words) 25.25%
of regions (30.64% of lines) before, 41.86% (46.08%) after.

DESIGN.md now names this step's words `char8`, `char16`, `char32`, `int(c)` and the casts
giving `#invalid` and `#overflow`, with `utf8` keyed in `B`. Plan row STR-types replaces
`codePoint`, `scalar` and `#notScalar` with them; the cases of the new names are that row's,
listed below so that none is lost.

Tests in `completeness.rs` unless a file is named.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| `codePoint("a")` 97, `codePoint("é")` 233, two scalars and the empty string `#notScalar` | `values.rs` `the_named_code_points` | |
| A surrogate is no scalar; `scalar(128512)` round trips | `values.rs` `a_surrogate_is_not_a_scalar_and_an_emoji_round_trips` | |
| `scalar` of every int that is no scalar value: -1, each end of the surrogates, past the last, `2^64`, `-(2^70)`; the ends that are | `values.rs` `scalar_refuses_every_int_that_is_not_a_scalar_value` | |
| Escapes and controls as one scalar: `\u{0}`, `\n`, `\t`, `\\`, `\"`, DEL, BOM, the noncharacters, `\u{10FFFF}` | `escapes_controls_and_noncharacters_are_scalars` | |
| A combining sequence (`e` + U+0301) is two scalars; its bytes differ from `é` | `a_combining_sequence_is_two_scalars` | |
| `utf8` of 1-, 2-, 3- and 4-byte scalars, of `""`, of controls and of `\u{10FFFF}` | `values.rs` `utf8_gives_the_bytes_keyed_from_zero`; `utf8_of_controls_and_the_last_scalar` | |
| The keys are the byte offsets from 0, first at 0 and last at `n - 1` | `bytes.rs` `the_keys_are_the_byte_offsets_from_zero` | |
| Reading one byte by its key (`utf8("aé")[0]`) | | lookup on a family is step L3.2, not built; this zedc rejects it with "`[0]` takes a tuple, not int ->? int" |
| `fromUtf8(utf8(s)) == s` for every string of up to 4 scalars over 1- to 4-byte scalars, at every boundary, at a stride over all scalars | `bytes.rs` `every_string_of_up_to_four_scalars_round_trips`, `every_boundary_round_trips_with_its_bytes`, `every_scalar_at_a_stride_round_trips`; `values.rs` `from_utf8_of_utf8_is_the_string` | |
| The UTF-8 length changes at each boundary | `bytes.rs` `the_lengths_change_at_the_boundaries` | |
| `fromUtf8([192, 128])` and every overlong form, surrogate, scalar past the last, truncated or stray continuation | `bytes.rs` `the_named_overlong_pair_is_bad`, `overlong_forms_are_bad`, `surrogates_and_scalars_past_the_last_are_bad`, `truncated_and_stray_continuation_bytes_are_bad` | |
| An int that is not a byte; a value that is not an int; the empty family | `bytes.rs` `an_int_that_is_not_a_byte_is_bad`, `a_value_of_another_kind_is_a_type_error`, `the_empty_family_is_the_empty_string` | |
| Bytes read in key order whatever the keys | `bytes.rs` `bytes_are_read_in_key_order` | |
| An atom passed to each word passes through | `bytes.rs` `an_atom_passes_through`; `a_failure_atom_as_the_argument_passes_through` | |
| `else` takes over each failure | `values.rs` `the_failures_pass_through_else` | |
| An interpolated `scalar`, and its failure failing the text | `values.rs` `an_interpolated_scalar_is_its_text_or_its_failure` | |
| A receiver, with and without parentheses; chained receivers | `values.rs` `a_receiver_is_the_string` | |
| A rope (`++`) read as its text | `values.rs` `a_rope_is_read_as_its_text` | |
| A tuple component, nested words, a comparison, arithmetic on the result, `==` on bytes, `++` of results | `each_word_in_other_positions` | |
| A lambda body; the lambda's failure | `each_word_in_other_positions` | |
| A function body under test tables; an `if` branch | `each_word_in_a_function_body_under_test_tables` | |
| A `match` arm | | `match` is not compiled by this zedc yet |
| An argument of another kind: bool, tuple, rat, suffixed float, string for int, int for string, string for bytes | `checks.rs` `an_argument_of_another_kind_is_rejected`; `an_argument_of_another_kind_is_rejected` | |
| No argument, or two | `the_words_take_one_positional_argument` | |
| The bytes are not a number | `checks.rs` `the_bytes_are_not_a_number` | |
| A failure unhandled before a string is written; a literal that always fails | `checks.rs` `a_failure_must_be_handled_before_a_string_is_written`, `a_literal_that_is_never_a_scalar_is_rejected` | |
| A code point in the domain of the bit words, 21 digits wide and not 20 | `checks.rs` `a_code_point_is_in_the_domain_of_the_bit_words`, `a_code_point_is_not_wider_than_21_digits_but_may_be_wider_than_20` | |
| A user function named `codePoint` shadows the word | `checks.rs` `a_local_function_named_code_point_is_not_the_word` | |
| A code point through a function's result is any int | `checks.rs` `a_code_point_returned_by_a_function_is_read_as_any_int` | |
| The interpreter and native code agree | `native.rs` all four | |
| Scaling of `utf8` and `fromUtf8` at n and 8n bytes | `bench.rs` both | |
| `char8`, `char16`, `char32`, `int(c)`, the casts with `#invalid` and `#overflow`, `char32(s)`, `c + 1` a type error, `utf8` keyed in `B` | | plan row STR-types, which replaces `codePoint` and `scalar` |
| `#badUtf8` renamed `#badEncoding(...)` | | step L7.3i |
