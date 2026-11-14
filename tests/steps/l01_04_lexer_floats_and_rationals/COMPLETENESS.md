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
| Probe (coordinator, 2026-11-14): `t() = 1.e;`. DESIGN: `Real` needs a digit after the dot, so this is `1` `.` `e`, rule `MemberSuffix`: `get(1, #e)` if the type of `1` has a field `e`, else the call `e(1)`; neither exists, so the program is rejected. Compiler: lexes as DESIGN says; `zedc run` rejects it ("`e` is not a function in scope"). The checker's type `() -> _` is an intermediate result, never shown alone. Agrees | `edges.rs` `a_dot_with_no_digit_after_it_ends_the_integer_before_a_letter` | The rejection itself is the resolver's and elaborator's, outside this group |
| Probe: `1e999999999999`, and any decimal past the range of every float format (`1e400`, `1e-400`). DESIGN L1.26b: one Float token; at `rat` it is exact, and in a class each format it does not fit is removed, leaving `rat`. Compiler: the lexer agrees; the checker gives it type `Never` with no error, and `zedc run` rejects `1e400 + 1r` as an `f64` that rounds to infinity, while `0.1 + 1r` prints `11r/10r` | `edges.rs` `a_decimal_beyond_the_range_of_every_float_format_is_one_float_token`; **FAIL-check-decimal-past-f64-at-rat** | Checker disagrees; filed, test in `wt/failing-tests/FAIL-check-decimal-past-f64-at-rat.rs` |
