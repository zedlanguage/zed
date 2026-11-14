# Completeness: integer literals (L1.3)

Row TEST-complete-lex (author P189). The code under test is the integer part of
`crates/zedc-syntax/src/lex/number.rs` and its messages in `lex/token.rs`. Expected results are
from DESIGN.md sec:lexical (the integer row, `_` between digits, `0x`/`0o`/`0b`). llvm-cov over
`number.rs` (shared with L1.4), as a floor: 88.48% of regions before, 94.42% after.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Each base at one digit, at its largest digit, with groups, with leading zeros | `edges.rs` `each_base_at_one_digit_and_with_groups`, `leading_zeros_are_decimal_digits_and_hex_digits_keep_their_case` | |
| Hex digits keep their case; `e` in hex is a digit | same | |
| Any number of digits is kept | `a_literal_keeps_every_digit_whatever_its_size` | |
| `_` at the end, doubled, after the base mark, before the number | `every_misplaced_underscore_is_named` | |
| A base mark with no digit, or a digit outside its base | `a_base_mark_with_no_digit_of_its_base_is_named` | |
| A capital base mark (`0X`, `0O`, `0B`) | `every_capital_base_mark_is_named` | |
| A number running into a name; a hex digit too large for its base | `an_integer_takes_no_suffix_but_r`, `a_number_ends_where_a_name_character_does_not_follow` | |
| A format suffix on an integer (`1f64`, `42f32`) | `an_integer_takes_no_suffix_but_r` | |
| `r` after an integer of another base | same | |
| Each token that may follow: operator, bracket, separator, `::`, comments, `.`, string, atom | `what_may_stand_right_after_an_integer` | |
| `'` after a number | same | |
| A letter beyond ASCII after a number | `a_letter_beyond_ascii_right_after_a_number_is_an_error` | |
| An integer in a hole, and an error there placed in the file | `an_integer_in_a_hole_is_lexed_as_in_code` | |
| Each malformed form's message, as written | `expected_malformed_numbers` | |
| A literal too long for memory to copy (`number.rs:72-79`, `:99-101`; `token.rs` `unread_literal`) | | Needs a literal larger than the memory the allocator gives, an unusual size (P178); a benchmark at most |
| Long literals | | Benchmarks (P178) |
