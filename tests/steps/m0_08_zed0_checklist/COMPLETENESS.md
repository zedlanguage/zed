# M0.8 completeness: the bootstrap-subset checklist

Code under test: the recorded checklist `zed/compiler/ZED0.md` and corpus program 31, read by
this folder's own readers (`table_layers`, `layer`, `layer_after`, `part_b_layers`). The audit
itself (the `audit` tool, which reads the spec repository) runs by hand and is not in these
tests; its negative controls are recorded in ZED0.md. Every line of the readers is reached
(llvm-cov, before and after this pass). Each claim of DESIGN.md step M0.8 that the file records
is one case below.

| Case | Covering test, or the reason none is needed |
|---|---|
| The audit found that L6 completes what program 31 needs; Part A's layers are L1 to L6 | `the_completing_layer_is_the_highest_item_and_program_31_is_labeled_there` |
| Program 31 is labeled at that layer | `the_completing_layer_is_the_highest_item_and_program_31_is_labeled_there` |
| Grammar alternatives at L1, L2, L3 and L6 only | `cases::part_a_has_grammar_at_l1_l2_l3_l6_and_words_up_to_l5` |
| `loop`, `until`, boundary `with` (Loop#0, Until#0, Boundary#0) in row L6 | `cases::part_a_has_grammar_at_l1_l2_l3_l6_and_words_up_to_l5` |
| Defined words up to L5 | `cases::part_a_has_grammar_at_l1_l2_l3_l6_and_words_up_to_l5` |
| Each Part A entry has the form `Rule#i` and is listed once | `cases::part_a_has_grammar_at_l1_l2_l3_l6_and_words_up_to_l5` |
| Each Part A entry is needed by program 31, and each need is listed | None here: the `audit` tool decides it against the spec's grammar, run by hand (ZED0.md "The audit") |
| Part A is the only table read by its first cell `L<k>` (the header row `Layer` is not a layer) | `cases::part_a_has_grammar_at_l1_l2_l3_l6_and_words_up_to_l5` |
| The subset is L1–L18 in full, language parts up to L24, back end of L28 | `every_part_b_need_lies_within_the_core_that_zed0_is` |
| Every Part B need lies within the subset; 20 rows; the highest is L24 | `every_part_b_need_lies_within_the_core_that_zed0_is` |
| `Files` port and `String` functions at L1, bit words at L1, `rekey` at L4, indexed definitions, `fix`, `.fold` at L6, the back-end port step S.1a | `cases::part_b_places_each_need_design_names_at_its_layer` |
| Every Part B row has four nonempty cells | `cases::part_b_places_each_need_design_names_at_its_layer` |
| Steps the audits added (L1.19a, L1.36a, L1.39c, L3.15a, L5.8a, L6.13–L6.13c, S.1a–S.1f, S.3a) are recorded | `cases::every_step_design_names_for_the_subset_is_recorded` |
| The step reader: a step name followed by a full stop, a prefix of a longer step, words that are not steps | `cases::every_step_design_names_for_the_subset_is_recorded` |
| `layer` on a range, a bare number, a cell with text after the layer, a step number | `cases::the_readers_of_layers_take_the_first_number` |
| `table_layers` on an empty text, on rows with letters after the number, on a row with no number | `cases::the_readers_of_layers_take_the_first_number` |
| `part_b_layers` takes the last layer of a range and skips the header and rule rows | `cases::the_readers_of_layers_take_the_first_number` |
| DESIGN.md's wording "the language parts of L19–L22" plus L23 and L24 steps, ZED0.md's "L19–L24" | None: both put the subset's language parts at most at L24, which the test checks; the wording differs only in grouping |
