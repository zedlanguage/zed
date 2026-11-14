# Completeness: names (L1.2)

Row TEST-complete-lex (author P189). The code under test is `crates/zedc-syntax/src/lex/name.rs`
and the parts of `lex/mod.rs` and `lex/token.rs` that read and report names. Expected results are
from DESIGN.md sec:lexical (`Name`, `NameChar`, `Wildcard`, `Keyword`, `Space`, author decision
of 2026-11-12 on ASCII names) and the message rule for characters that may not show. llvm-cov
over `name.rs`, as a floor: 99.64% of regions after.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Each ASCII name character at the start and inside a name | `ascii.rs` `a_name_takes_exactly_the_ascii_name_characters` | |
| A name as programs write it | `names_as_programs_write_them` | |
| `_` alone is the wildcard; `_` before a name character is a name | `a_bare_underscore_is_the_wildcard_and_an_underscore_before_a_name_character_is_a_name` | |
| One trailing `'`; a second one | `a_trailing_prime_is_part_of_the_name_and_only_one_is_read`, `ascii_names_with_a_prime_lex` | |
| `'` after the wildcard or a keyword | `edges.rs` `a_prime_after_the_wildcard_or_a_keyword_is_an_error` | |
| A digit or a combining mark at the start | `a_name_cannot_start_with_a_digit_or_a_combining_mark` | |
| Each character `Space` takes between two names (` `, `\t`, `\n`, `\r`, `\r\n`, a mix) | `each_character_space_takes_separates_two_names` | |
| Control characters `Space` does not take (FF, VT, DEL, U+0085): error named by code point | `a_control_character_space_does_not_take_is_an_error_named_by_its_code_point` | |
| Other space and format characters between tokens | `a_space_or_format_character_other_than_a_plain_space_between_two_tokens_is_an_error` | |
| Each blank character in code, in a comment, in string text; the grammar engine agrees | `ignorable.rs` (four tests) | |
| A byte order mark, NUL, zero-width joiner and non-joiner, bidi controls | `invisible.rs` | |
| A name, atom or annotation beyond ASCII: rejected, transliteration offered | `non_ascii.rs` | |
| An offer that is a keyword, a taken name or a prelude name | `the_offer_is_a_new_name_with_the_least_suffix`, `the_offer_is_no_prelude_name`, `an_offer_that_would_be_no_name_is_not_made` | |
| A Cyrillic letter that looks like a keyword | `a_cyrillic_letter_that_looks_like_a_keyword_is_no_name` | |
| Spans are byte ranges; a loaded file gives line and column | `spans_are_byte_ranges_of_the_text`, `a_loaded_file_gives_the_line_and_column_of_the_character` | |
| Every keyword and prelude word is an ASCII name; the prelude lexes | `every_keyword_is_an_ascii_name`, `every_word_type_and_annotation_the_resolver_gives_the_prelude_is_an_ascii_name`, `every_file_of_the_prelude_source_lexes` | |
| The Unicode tables match the lexer's Unicode version | `the_data_files_are_of_the_unicode_version_of_the_lexer_tables` and two more | |
| Long names and long runs | | Benchmarks (P178) |
| `name.rs:116`, `Word::Name` in the second reading of `word` | | Cannot be reached: a word gets there only when it holds a character beyond ASCII, so `is_ascii` is false |
