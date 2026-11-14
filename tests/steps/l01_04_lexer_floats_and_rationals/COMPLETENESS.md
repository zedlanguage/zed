# Completeness: float and rational literals (L1.4)

Row TEST-complete-lex (author P189). The code under test is the float and rational part of
`crates/zedc-syntax/src/lex/number.rs` and its messages in `lex/token.rs`. Expected results are
from DESIGN.md sec:lexical (the float and rational rows, the `f32`/`f64` suffixes, `f16` and
`bf16` before L1.18a). llvm-cov over `number.rs`, as a floor: see `l01_03`.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Floats as programs write them | `floats_as_programs_write_them` | |
| A digit must follow the dot, so `1.x` and `1..2` start with the integer | `a_digit_must_follow_the_dot_so_member_access_and_ranges_start_with_the_integer` | |
| `f32` and `f64` on each form: dot, exponent, both, groups, `E+` | `edges.rs` `the_suffixes_f32_and_f64_force_the_format_of_each_form_of_a_decimal` | |
| A suffix in capitals, with more letters after, too short, unknown width, followed by `_` | `a_suffix_is_written_in_small_letters_and_alone` | |
| `f16` and `bf16` on a float and an integer | `the_suffixes_f16_and_bf16_are_rejected_until_their_formats_come` | |
| `r` after each form of a real: integer, dot, exponent with sign, groups | `each_form_of_a_real_takes_r`, `rationals_are_decimal_and_keep_their_text` | |
| An exponent of zero, with `_`, with a sign; `_` after `e` or its sign | `an_exponent_and_its_groups` | |
| A second dot or exponent; a dot after hex | `a_second_dot_or_exponent_starts_a_new_token` | |
| Each token that may stand next to a float; `'` after it | `what_may_stand_next_to_a_float` | |
| A float or rational in a hole, and an error there placed in the file | `a_float_in_a_hole_is_lexed_as_in_code` | |
| Each malformed form's message, as written | `expected_malformed_floats_and_rationals` | |
| A literal too long for memory to copy | | Unusual size (P178); see `l01_03` |
| Long literals and long exponents | | Benchmarks (P178) |
