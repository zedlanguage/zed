# Completeness: string literals (L1.5)

Row TEST-complete-lex (author P189). The code under test is `crates/zedc-syntax/src/lex/string.rs`
and the `Part` printing and equality in `lex/token.rs`. Expected results are from DESIGN.md
sec:lexical (the string row, `Escape`, holes) and the message rule for characters that may not
show. llvm-cov over `string.rs`, as a floor: 98.79% of regions before, 99.19% after.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Plain strings and each escape `\n \t \r \0 \\ \" \$` | `strings.rs` `plain_strings_and_escapes` | |
| `\u{…}` at its bounds: 0, leading zeros, the edges of the surrogates, U+10FFFF, two in a row | `edges.rs` `each_code_point_escape_at_its_bounds` | |
| `\u{…}` naming a surrogate or a value past U+10FFFF, or too wide for 32 bits | `each_code_point_that_names_no_character_is_an_error_over_the_escape` | |
| `\u` unclosed, with a non-hex digit, with a space, with nothing, capital `\U` | `each_malformed_code_point_escape_is_an_error_at_its_backslash_u` | |
| An unknown escape lists the escapes | `an_unknown_escape_is_a_lexical_error_that_lists_the_escapes` | |
| A backslash before a line break or a tab names it by code point, never printing it | **FAIL-lex-escape-invisible** | The message prints the raw character; filed, test in `wt/failing-tests/FAIL-lex-escape-invisible.rs` |
| Escapes in a `"""` string, an escaped `"` before the closing `"""` | `an_escape_in_a_triple_quoted_string_is_decoded_as_in_a_one_line_string` | DESIGN's string row says the text "cannot end in `"`"; the grammar's `Escape` allows `\"` there, and the test follows the grammar. The prose should say "an unescaped `"`" |
| A `$` that opens no hole: before a digit, at the end, alone, doubled, before a space; `{` and `}` alone | `a_dollar_that_opens_no_hole_is_text` | |
| An empty and a one-line `"""` string; one with only a line break | `the_empty_and_one_line_triple_quoted_strings` | |
| Stripping: closing indentation removed; delimiters on their own lines | `a_triple_quoted_string_strips_its_closing_indentation`, `stripping_needs_both_delimiters_on_their_own_lines`, `stripping_reads_only_the_lines_of_the_delimiters` | |
| A line indented less than the closing line; tabs and spaces mixed | `stripping_reads_only_the_lines_of_the_delimiters`, `expected_malformed_strings` | |
| Blank lines inside a stripped string | `blank_lines_and_deeper_lines_inside_a_stripped_string` | |
| A line of only spaces or tabs deeper than the indentation becomes empty | **FAIL-lex-deep-blank-line** | Kept as spaces; filed, test in `wt/failing-tests/FAIL-lex-deep-blank-line.rs` |
| A `\r\n` file: strips as the `\n` file | `l01_01` `line_endings_in_a_loaded_string_are_one_break_each` | |
| A hole holding nothing, a space, braces, a keyword, an atom, an annotation, the wildcard, a rational, a string with `{` or `}`, a comment with `}` | `a_hole_may_hold_any_token_and_nothing` | |
| Nested holes; holes over lines; a hole's spans index the file | `holes.rs` | |
| A lexical error in a hole is placed in the file | `a_lexical_error_in_a_hole_is_placed_in_the_file` | |
| An unclosed hole of a `"""` string | `an_unclosed_hole_of_a_triple_quoted_string_is_an_error`, `expected_malformed_holes` | |
| A string beside another string, a name, an operator; four quotes | `a_string_is_one_token_beside_others` | |
| `Part` `Debug` as derived, through a hole of two tokens and a string of two parts | `nested_parts_print_and_compare_as_derived` | |
| `Part` equality: text against a hole, two texts, hole spans, token counts, token spans, nested | `nested_parts_print_and_compare_as_derived`, `tokens_a_few_holes_deep_compare_print_and_drop` | |
| Deep nesting and long strings | | Benchmarks (P178) |
| `string.rs:344`, `unreachable!` | | Cannot be reached by construction |
| A `"""` string whose text starts with a hole is not stripped (`string.rs:422`) | `stripping_reads_only_the_lines_of_the_delimiters` | |
| `string.rs:293`, a nested hole whose end an earlier scan recorded | | No input found reaches it: the scan does not look at a hole a second time in the order it reads them. Inferred from the code, not proved |
