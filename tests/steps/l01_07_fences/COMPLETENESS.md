# Completeness: fences (L1.7)

Row TEST-complete-lex (author P189). The code under test is `crates/zedc-base/src/fence.rs`
(`extract`, `marks`, `label`) and the fence reading of `crates/zed-tools/src/spec.rs`
(`zed_fences_in`, `Spec::open`, `all_fences`). Expected results are from DESIGN.md (every fence
tagged `zed`, the ✗ variant rule, the `// layer Lk` label). llvm-cov, as a floor: `fence.rs`
100%; `spec.rs` 89.34% of regions before, 94.67% after, every line covered.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| Only `zed` fences, with their lines | `extractor.rs` `only_zed_fences_are_extracted_with_their_lines` | |
| An opening line with space after or a tab before | `edges.rs` `an_opening_line_is_three_backticks_and_zed_with_space_around_only` | |
| Lines that only look like an opening: `zedx`, `Zed`, four backticks, a title, a space before `zed`, no tag, `peg` | same | |
| A closing line with space around; four backticks or a tag inside a fence | `a_closing_line_is_three_backticks_with_space_around_only` | |
| An empty document; a fence at its last line; two fences back to back | `fences_at_the_edges_of_the_document_and_of_each_other` | |
| An unclosed fence: the extractor runs to the end, the spec tool rejects it with its line | `an_unclosed_fence_runs_to_the_end`, `the_spec_tool_rejects_an_unclosed_fence_with_its_line` | |
| The extractor and the spec tool agree on every fence | `the_fences_are_those_the_extractor_finds` and the helper in `edges.rs` | |
| A ✗ on a comment line is a variant; elsewhere it marks the line (block comment, string, bare) | `a_mark_on_a_comment_line_is_a_variant`, `a_mark_on_a_line_that_is_not_wholly_a_line_comment_marks_the_line` | |
| A label: whole comment line, no digits, leading zeros, text after, indented, no space after `//` | `a_label_is_a_whole_comment_line`, `a_label_names_a_layer_in_digits_after_the_l` | |
| A label too large for `u32` | | Layers are below 100; such a label gives `None`, as no label |
| A `\r` in the document | | `extract` receives text that `load` or `read_text` has already given `\n` line endings |
| DESIGN fences then EXAMPLES fences | `the_spec_reads_the_fences_of_design_then_of_examples` | |
| A spec with fewer than three grammars | `a_spec_needs_its_three_grammars` | |
| Sections and keys of fences | `keys.rs` | |
| Variants and fixtures | `variants.rs` | |
| Every fence of DESIGN, EXAMPLES, README and the mathlib study | `copies.rs`, `mathlib.rs` | |
| Many and long fences | | Benchmarks (P178) |
