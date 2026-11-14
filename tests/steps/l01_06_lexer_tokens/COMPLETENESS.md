# Completeness: atoms, annotations, operators, keywords and comments (L1.6)

Row TEST-complete-lex (author P189). The code under test is `lex/mod.rs`, `lex/punct.rs`,
`lex/comment.rs` and the token messages in `lex/token.rs`. Expected results are from DESIGN.md
sec:lexical (the comment, atom, annotation and operator rows, `KeywordWord`). llvm-cov, as a
floor: `mod.rs` 88.24% of regions before, 100% after; `comment.rs` and `punct.rs` 100%;
`token.rs` 89.57% before and after (see the last rows).

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Every keyword; a longer word; a keyword in another case | `words.rs` `every_keyword_is_a_keyword_and_a_longer_word_is_a_name`, `edges.rs` `a_keyword_differs_from_a_name_only_in_case` | |
| `where` and `sep` reserved by position; `without` a keyword | `where_and_sep_are_names_reserved_only_by_position`, `without_is_a_keyword` | |
| `'` after a keyword | `a_prime_does_not_continue_a_keyword` | |
| An atom or annotation of each kind of name, a keyword, two in a row, followed by `.` or `(` | `an_atom_or_annotation_holds_any_name`, `atoms_and_annotations` | |
| `#_` as an operator | same | |
| `#` or `@` with no name, before a digit, before `_` or `'` | `a_mark_with_no_name_after_it_is_an_error_at_the_mark` | |
| Every operator alone; the longest wins | `every_operator_lexes_alone_and_the_longest_wins` | |
| Runs of operator characters that could be read two ways | `each_run_of_operator_characters_is_read_longest_first` | |
| An arrow, ellipsis or sign beyond ASCII; `…` as an elision in a fence | `an_arrow_or_ellipsis_beyond_ascii_is_no_operator` | |
| A line comment at the end of the file, after a token, holding `/*` | `a_comment_at_the_edges_of_the_file_and_of_tokens` | |
| Empty and nested block comments; a quote in a comment; `*/` outside one | same, `block_comments_nest` | |
| An unclosed block comment | `an_unclosed_block_comment_runs_to_the_end_of_the_file` | |
| A comment delimiter in a string | `a_comment_delimiter_in_a_string_is_text` | |
| Each form of a doc comment: empty, no space, two spaces, tab, trailing space, four `/`, `/**`, after code | `each_form_of_a_doc_comment`, `doc_comments_are_collected_and_other_comments_dropped` | |
| A doc comment in a hole is listed, so that a later step can report it as attached to no declaration | **FAIL-lex-doc-in-hole** | Dropped; filed, test in `wt/failing-tests/FAIL-lex-doc-in-hole.rs` |
| `comments`: empty file, order, nested, adjacent, none from strings or holes | `the_comments_of_a_file_are_listed_in_order_without_those_in_strings` | |
| A whole program | `expected_example_program` | |
| Each lexical error's message | `expected_lexical_errors` | |
| Long runs and deep nesting | | Benchmarks (P178) |
| Probe (coordinator, 2026-11-14): `(1, )`. DESIGN: `Space` only separates tokens, and `TupleExpr` takes a trailing `,`, so `(1, )` is the one-tuple `(1,)`. Compiler: same tokens and parse, and `zedc run` prints `(1,)`. Agrees | `edges.rs` `space_before_a_closing_bracket_changes_no_token_and_no_parse` | |
| Probe: `x'` alone and `{ 1 }` alone. DESIGN: every `Decl` of a `Unit` ends in `;`, so each is a syntax error at the top level; with the `;` each is an `ExprStmt`, a form of layer L6. Compiler: without `;`, a syntax error with the repair `x';` (no "not yet"); with `;`, "an expression statement ... does not compile it yet", the honest layer message. Agrees | `edges.rs` `an_expression_at_the_top_level_needs_its_semicolon` | The "not yet" message is the front end's layer check, outside this group |
| `token.rs:198`, the message for an unexpected `\` | | Cannot be reached: `\` is an operator |
| `token.rs` `Unread` and `unread_literal` | | Unusual size (P178); see `l01_03` |
