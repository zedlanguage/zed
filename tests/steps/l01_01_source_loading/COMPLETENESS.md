# Completeness: source loading (L1.1)

Row TEST-complete-lex (author P189). The code under test is `zedc::source` (`load`, `Reject`,
`io_reason`, `unreadable`) and `zedc::run::load`. Expected results are from DESIGN.md
sec:lexical (UTF-8, no byte order mark, NFC, line endings) and sec:diagnostics. llvm-cov over
`crates/zedc-base/src/source.rs`, as a floor: 89.05% of regions before, 99.50% after.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Empty file | `edges.rs` `each_line_ending_and_each_mix_of_them_is_one_break` | |
| NFC text in many scripts | `nfc_text_in_many_scripts_loads_unchanged` | |
| Each line ending alone: `\n`, `\r\n`, lone `\r` | `edges.rs` `each_line_ending_and_each_mix_of_them_is_one_break` | |
| Each mix of line endings, at the start and the end | `each_line_ending_and_each_mix_of_them_is_one_break`, `windows_and_classic_mac_line_endings_load_as_the_unix_file` | |
| A continuation byte alone; a byte UTF-8 never uses (`FF`, `FE`) | `each_kind_of_bytes_that_are_not_utf8_is_rejected_at_its_first_bad_sequence` | |
| A lead byte cut off by text or by the end; a code point above U+10FFFF; an overlong form (`C0 AF`) | same | |
| A byte order mark cut off at the end (`EF BB`) | same | |
| The first of two bad sequences is the one named | same | |
| A rejection's line and column count the bytes as read, before line endings change, and columns count characters | `a_rejection_is_placed_in_the_file_as_read_before_its_line_endings_normalize`, `places.rs` | |
| A byte order mark alone, before a line break, twice, before a comment | `a_byte_order_mark_is_rejected_alone_and_before_any_other_text` | |
| A byte order mark after the start | `a_byte_order_mark_after_the_start_is_left_to_the_lexer` | |
| Text that is not NFC: the span is the first text NFC changes, with the NFC spelling | `the_span_is_the_first_text_nfc_changes`, `the_first_of_two_places_nfc_changes_is_the_one_named` | |
| A run of combining marks of mixed classes | `one_base_with_a_run_of_marks_of_mixed_classes_is_rejected_whole` | |
| A Hangul syllable of three jamo (L V T) is named whole | **FAIL-source-lvt-jamo** | The repair named leaves the file not NFC; filed, test in `wt/failing-tests/FAIL-source-lvt-jamo.rs` |
| A combining mark at the start of the file | `a_mark_at_the_start_of_the_file_is_nfc_and_left_to_the_lexer` | |
| NUL and bidi controls | `nul_and_bidi_controls_are_left_to_the_lexer` | |
| A file with two problems is rejected once | `a_file_with_two_problems_is_rejected_once_with_a_span_in_the_file` | DESIGN names no order among the rejections, so the test asks only for one span inside the file |
| Messages without the file (`Display`) and with it (`message`, `render`) | `the_messages_without_a_place_are_the_rejections_in_words`, `expected_rejections` | |
| A file that cannot be read: numbered and unnumbered system errors | `a_file_that_cannot_be_read_is_named_with_the_reason_in_words` | |
| The command-line path `zedc::run::load` | `the_compilers_whole_file_path_reports_a_rejection_with_its_place` | |
| Loaded text given to the lexer: a `"""` string with `\r\n`, a lone `\r` in a `"` string | `line_endings_in_a_loaded_string_are_one_break_each` | |
| Large files and long runs | | Benchmarks in `bench.rs` and `scaling.rs` (P178) |
| `source.rs:192`, `unreachable!` after the NFC search | | Cannot run while the search is right; FAIL-source-lvt-jamo shows the search's claim is wrong for another reason |
