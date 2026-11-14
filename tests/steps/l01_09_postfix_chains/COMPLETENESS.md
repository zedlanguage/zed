# L1.9 completeness: postfix chains

Code under test: the building of postfix chains into syntax trees (`crates/zedc-syntax/src/ast/
mod.rs`, `builder.rs` argument lists) and their grammar rules `Postfix`, `Suffix`,
`CallSuffix`, `MemberSuffix`, `SafeSuffix`, `IndexSuffix`, `Args`, `PosArg`, `NamedArg`,
`PlainArg` (DESIGN.md sec:grammar, step L1.9).

Coverage (llvm-cov, regions, the eleven groups of TEST-complete-parse, before and after this
pass): `ast/mod.rs` 94.4% to 94.5%, `ast/builder.rs` 86.0% to 86.2%. What is left in `mod.rs`
is `unreachable!` arms that name the grammar's only forms, and `shown`, whose refusal of a text
too large for memory is a benchmark-sized input. What is left in `builder.rs` is the ports of
`main` (`m.stdout`, `m.signals`, `MainArgs` fields, pushes to inputs), tested with the steps that
give them: l01_19_whole_file_ports, l01_19a_command_line and l01_21_test_runner.

| Case | Covering test, or the reason none is needed |
|---|---|
| Each alternative of each suffix and argument rule parses to its node | `l01_08_parser::alternatives::*` (one case per alternative, `grammar_cases.rs`) |
| Positional, then named, then curried arguments; a shorthand argument is the name in its place | `calls::positional_then_named_then_curry`, `calls::a_shorthand_argument_is_the_name_at_its_own_place` |
| A curry mark out of place does not parse | `calls::misplaced_curry_marks_do_not_parse` |
| A positional argument after a named one parses and is refused with its row | `calls::a_positional_argument_after_a_named_one_parses_and_is_rejected_with_its_row` |
| An argument named twice is refused at the second | `calls::an_argument_named_twice_is_an_error_at_the_second` |
| A form of a later layer is refused as not compiled yet | `calls::a_form_of_a_later_layer_is_refused_as_not_compiled_yet` |
| A sort key is a positional argument; a direction word alone prints back and needs a following `,` or `)` | `calls::a_sort_key_is_a_positional_argument`, `calls::a_direction_word_alone_prints_back_and_needs_a_following_comma_or_paren` |
| `5.double`: a digit then a letter is member access (the lexer rule) | `chains::a_digit_then_a_letter_is_member_access` |
| Suffixes apply left to right; a chain is an operand of the operators around it | `chains::suffixes_apply_left_to_right`, `chains::a_chain_is_an_operand_of_the_operators_around_it` |
| Each chain in DESIGN.md's fences builds, or names its step | `fences::every_chain_in_the_fences_builds_or_names_its_step` |
| A chain in the head of `if`, `match`, `for` | `l01_08_parser::heads::each_construct_in_a_head_gives_the_tree_of_the_head_flag` |
| Long chains, deep nesting, nested string holes | Benchmarks `bench::*`; `scaling::each_benchmark_text_builds_its_tree_at_small_sizes` checks their texts at small sizes |
| A prefix `-` on a literal's chain (`-1.abs`) | Tested with its row in l01_21, l01_29 and l01_37a (`ast/neglit.rs`) |
