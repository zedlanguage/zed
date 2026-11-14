# Completeness: zed-tools unit tests

Row TEST-complete-crates (author P189). The crate's one unit test, in `src/layer.rs`, calls
`WordTable::read_row`, the reading of one row of the table "Defined words by layer" (DESIGN.md
sec:layers), and through it `spans`, `is_word` and `prose_words`. These, `WordTable::layer_of`
and `label_at`, the `// layer Lk` label, are the pieces covered here; expected results come from
the module comment of `layer.rs` and the table in DESIGN.md. New tests are in
`src/layer/completeness.rs`; `tests::` names the older test in `src/layer.rs`.

Tested elsewhere, not by unit tests:

- The `layer` tool as a whole (reading the table from a file, the positions where each word
  counts, string holes, program directories, labels, failures):
  `tests/steps/m0_03_grammar_tools/layer_roles.rs`.
- The other tools, through whole runs: `tests/steps/m0_03_grammar_tools` (audit, cases, check,
  cite, conflicts, fences, fence_layers, fuzz, llp, plan, progress, ring, spec, spec_checks,
  split, sync, syntax, text), `tests/steps/s_01_port_catalog` (catalog),
  `tests/steps/s_01f_import_graph` (imports), `tests/steps/m0_01_scaffolding` (step_targets),
  and `l01_02_lexer_names`, `l01_07_fences`, `l01_21_test_runner`, `l07_03_unit_log_off`
  (spec, spec_checks, sync, syntax).

llvm-cov lines (unit tests of the crate):

| File | Before | After |
|---|---|---|
| `layer.rs` | 68/430 (15.81%) | 106/430 (24.65%) |

Every line of `spans`, `is_word`, `prose_words`, `layer_of`, `read_row` and `label_at` is now
reached. The lines of `layer.rs` left unreached are `WordTable::read` (reads a file), the scope
pass, `analyze`, `program_units`, `check`, `report` and `run`, all tested by `layer_roles.rs`.

| Case | Test, or reason none is needed |
|---|---|
| Backtick spans of a cell: several in order, adjacent, empty (skipped), none, unclosed | `a_cell_holds_its_non_empty_backtick_spans_in_order` |
| A word by prefix and column: annotation `@`, atom `#` (any column), `::` read (the word after the first `::`), plain word a facet in the facet column and a form elsewhere; columns after the third not read | `each_column_and_prefix_puts_a_word_in_its_own_kind` |
| Spans skipped: `.fold` and `abs` (need types), `with …`, `zedc …`, a named argument `n:`, a call `f(…)` | `spans_that_name_no_word_of_source_are_skipped`, `tests::argument_names_are_not_counted` |
| Spans refused as no word: with a space, before `:` or `(…)` not a word, `f()`, leading digit, a dash, a non-ASCII letter | `spans_that_name_no_word_of_source_are_skipped`, `tests::argument_names_are_not_counted` |
| A row with too few columns; with no layer (`2x`, `L`, `—`); a layer without `L` | `a_row_with_too_few_columns_or_no_layer_is_refused` |
| A word named twice keeps its first layer; a word of two kinds has the lowest layer; a word not listed has none | `a_word_keeps_the_first_layer_that_names_it_and_its_lowest_kind` |
| Words named in prose (L13 `sanitize`, L20 `serialize`, `Json`, `Csv`); a layer with none | `the_words_a_row_names_in_prose_are_forms_of_their_layer` |
| Label: at the start, followed by text, `L0`, ending in punctuation; refused when the number runs into a letter or `_`, has no digits, is indented, misspelled, not on the first line, empty, or past `u32` | `a_label_is_the_layer_comment_at_the_start_whose_number_ends_its_word` |
| The target value `#mcu` (DESIGN.md lists five target values; the tool knows four) | Fails: `#mcu` in a type counts as an L31 atom read. Row FAIL-layer-mcu-target-value, test in `wt/failing-tests/FAIL-layer-mcu-target-value.rs` (not merged), for `tests/steps/m0_03_grammar_tools` |
