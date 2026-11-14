# Completeness: characters a terminal does not show (DIAG-control, in L2.12's folder)

Row TEST-complete-diagnostics (author P189). This folder holds the tests of DIAG-control; the
rows of step L2.12 itself are not built yet. The code under test is `crates/zedc-base/src/terminal.rs`
(`hidden`, `escape`, `escape_width`, `Escaped`), the source lines and underlines of
`crates/zedc/src/front.rs` (`shown`), the string writer `Text::literal` of
`crates/zed-kernel/src/text.rs` as printed types and `String(x)` use it. Expected results are
from DESIGN.md sec:diagnostics, "Characters a terminal does not show".

Coverage of `crates/zedc-base/src/terminal.rs` by this group (llvm-cov, benchmarks skipped):
regions 95.65% before the pass and after, lines 100% both. The two regions left are the `?` of
`Escaped`'s writes, taken only when the formatter it writes to fails; nothing in zedc fails
that way here: a failing formatter is the caller's path, not a case of the escape.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| A clear-screen in a string of the unit prints escaped in the line, the headline and the type | `mod.rs` `a_clear_screen_in_a_string_of_the_unit_prints_escaped` | |
| Every class of hidden character (a C0 control, NUL, DEL, C1 controls, a space other than U+0020, line and paragraph separators, zero-width space and joiner, the byte order mark, each bidirectional control, a format character above U+FFFF) prints escaped in the line and the type | `completeness.rs` `every_kind_of_hidden_character_prints_escaped_in_the_line_and_the_type`; `mod.rs` `a_nul_a_delete_a_c1_control_and_a_bidi_override_print_escaped` | |
| Private-use, unassigned and noncharacter code points print escaped in a type | `completeness.rs` `private_unassigned_and_noncharacter_code_points_print_escaped_in_a_type` | |
| A character that shows (`'`, `é`, a wide character) is left alone | `mod.rs` `a_character_that_shows_is_left_alone`; `completeness.rs` `a_string_type_with_no_special_character_prints_as_written` | |
| A literal written with an escape prints as written | `mod.rs` `a_literal_written_with_an_escape_prints_as_written` | |
| A combining mark shows on a line; in a printed literal it is escaped, also at its start | `completeness.rs` `a_combining_mark_shows_and_a_format_character_does_not`, `a_combining_mark_in_a_printed_type_is_written_escaped_even_at_the_start` | |
| A printed string type reads back as itself | `mod.rs` `a_printed_string_type_reads_back_as_itself` | |
| Underlines placed by the escape's columns, for every digit count of the escape, a five-digit one, after an escape | `completeness.rs` `the_width_of_an_escape_is_counted_for_every_digit_count`, `the_marks_stand_under_a_literal_holding_a_five_digit_escape`; `mod.rs` `a_mark_after_an_escape_stands_under_its_character` | |
| A tab on a line shows as four spaces and `\t` in a type; a tab in a message is kept, a line feed lays it out | `mod.rs` `a_character_that_shows_is_left_alone`; `completeness.rs` `a_line_feed_lays_out_a_message_and_a_tab_in_a_message_is_kept` | |
| An escape in a comment on a quoted line; hidden characters on two lines | `completeness.rs` `an_escape_in_a_comment_on_a_quoted_line_prints_escaped`, `hidden_characters_on_two_lines_print_escaped_on_each` | |
| A step on another line than the headline quotes its own line | `completeness.rs` `a_step_on_another_line_than_the_headline_quotes_its_own_line` | |
| Every text of a diagnostic prints escaped; the diagnostic keeps its own text | `mod.rs` `every_text_of_a_diagnostic_prints_escaped_and_the_diagnostic_keeps_its_text` | |
| A refused file; a parse error keeps the raw line and prints it escaped | `mod.rs` `a_refused_file_prints_escaped`, `a_parse_error_keeps_the_raw_line_and_prints_it_escaped` | |
| A hidden character in a dependency's text | `mod.rs` `a_clear_screen_in_a_dependency_prints_escaped` | |
| `String(x)` of a value writes the strings inside it with the same writer | `completeness.rs` `a_string_inside_a_value_prints_with_the_same_writer` | |
| The lexer naming the characters it rejects | none in this group | Belongs to the lexical tests, `l01_02` (TEST-complete-lex). |
| Long lines of many escapes | `bench.rs` | Sizes beyond the small cases are benchmarks (P178). |
