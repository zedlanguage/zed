# L1.8 completeness: the parser

Code under test: the PEG engine and grammar reader (`crates/zedc-syntax/src/parse/`:
`grammar.rs`, `engine.rs`, `tree.rs`, `case.rs`, `mod.rs`, `recover.rs`) over the grammar of
DESIGN.md sec:grammar (`zed/grammar/syntax.peg`, `notation.peg`). Expected trees are taken
from the grammar text: its ordered choice, its `~` marks and its layer tags.

Coverage (llvm-cov, regions, the eleven groups of TEST-complete-parse with benchmarks
skipped, before and after this pass): `parse/grammar.rs` 94.4% to 98.0%, `engine.rs` 94.2% to
95.7%, `case.rs` 96.4% to 97.3%, `recover.rs` 96.9% to 97.7%, `tree.rs` 98.7%, `mod.rs` 99.0%.

| Case | Covering test, or the reason none is needed |
|---|---|
| Every alternative of every rule of `syntax.peg` and `notation.peg` builds its node | `alternatives::each_case_builds_its_alternative_at_its_layer_and_not_one_ring_below` over the 502 cases of `grammar_cases.rs` |
| Each alternative parses at the ring of its layer and not one ring below | `alternatives::each_case_builds_its_alternative_at_its_layer_and_not_one_ring_below` |
| A rule or alternative added to the grammar without a case | `alternatives::every_alternative_of_every_rule_has_a_case` fails until one is added |
| Each item of each alternative (literal, token kind, rule outside a lookahead, so each branch of a choice) is matched by some case | `alternatives::every_item_of_every_alternative_is_matched_by_some_case` (this table or `zed/grammar/cases.txt`) |
| The head flag (sec:grammar "The head flag"): an `else` tail, a brace-led display, a `with` update, a nested `if`/`match`/`for`, `break` in the head of `if`, `match` and `for`; brackets clear the flag; an `else` tail outside a head takes a block | `heads::each_construct_in_a_head_gives_the_tree_of_the_head_flag` (26 cases of `head_cases.rs`) |
| Bracketing of the operator ladder, later-layer operators only at their ring, a string hole parsed as an expression | `cases::*` (3 tests) |
| Left recursion: seeds, growth, brackets restarting a match, one node per operator, a rule that only calls itself | `left_recursion::*` (8 tests) |
| Associativity table rows (LR-4 audit): `else` chains, joins, subtraction and division from the left, power from the right, a flat comparison chain | `lr4_assoc::*`, `grammar_shape::*` |
| Separated lists (`sep`), lists of lists, nested separators | `grammar_read::*` |
| Each malformed grammar line: trailing text, unclosed literal, class, `head(`, `nest(`, `(`; a `;`; `--` in a class; a stray `*`; a missing expression; no layer; an undefined rule; an alternative before any rule; a mark beside another item | `grammar_errors::each_malformed_grammar_line_is_refused` |
| Edge forms of a grammar line: a layer followed by a `--` comment, a `~` mark on an undefined name in an open grammar, each of the nine token kinds the grammar names | `grammar_errors::the_edge_forms_of_a_grammar_line_are_read` |
| The engine over characters: what each item matches (classes, `ANY`, an undefined name under `read_open`, a token kind, an empty sequence, a lookahead asked from outside) and what a failure expected; the size of a character input and of a token input, and that tokens have no characters | `grammar_errors::the_engine_reads_a_grammar_over_characters`, `an_input_of_characters_or_tokens_reports_its_size` |
| Parse errors: where they are reported, what is expected, named in the program's words, never as a grammar token kind | `errors::expected_errors`, `plain_names::*` |
| A reserved word in each position a name may stand (binding, parameter, function, field, struct field, record field, named argument, type, loop variable), with its repair | `reserved::*` (14 tests) |
| Every fence of DESIGN.md parses first at its recorded ring; every variant fixture as its fence | `rings::*` |
| Deep nesting: blocks of lines, a comment at the bottom of a nest | `deep::*` |
| Large inputs | Benchmarks (`scaling::*`, `grammar_scaling::*` at small sizes; the large sizes run under `--bench`) |
| Recovery: the note on a bracket still open names the token where the parse stopped, or says "where the parse stops" when that token's text holds a line break or backticks | `recovery_edges::an_open_bracket_names_where_the_parse_stops` |
| Recovery under a grammar whose `Unit` has no `END` (`parse_with`): a declaration that parses only in part is refused at its stop, with its repairs | `recovery_edges::a_unit_rule_with_no_end_is_recovered_too` |
| `Kind::name` of `KW` and `OP` | None: the grammar writes keywords and operators as quoted literals, never by kind, so no grammar line names these two kinds and no message prints them |
| `case.rs` line 148 (the clause deleted, and the unit still not parsing to its end) | None reachable through `parse`: the clause repair runs only for the real `Unit`, which ends in `END`, so a parse of the repaired unit either reaches the end or fails |
| `recover.rs` lines 364 and 413: a repair that does not lex, and a word inserted at the end directly after a word | No input found: a repair inserts only a literal of the grammar, which lexes, and the closing and separating tokens inserted at the end of a declaration begin with no letter. This is read from the code, not proved; an input that reaches either line should get a test |
| `tree.rs` line 312, `Expected::Class` on tokens | None: `unreachable!`; a grammar over tokens holds no character class (the character engine is tested in `grammar_errors`) |
