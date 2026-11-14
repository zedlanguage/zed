# M0.12 completeness: the refusal census

Code under test: the census of plan item REFUSAL-census-now (this folder: `refusals`, `line`,
`totals`, `report` and `census` in `mod.rs`, the kinds and their phrases in `kinds.rs`, the
reader of `programs.txt` in `programs.rs`) and, through it, the refusals `zedc::run::load` and
the front end report on the corpus. DESIGN.md has no step M0.12 of its own; the kinds are those
the checker's code names (the header of `kinds.rs`), and the census lists them as the plan row
says. Lines of the three files reached (llvm-cov, without the `bench` module): 99.0% before and
after (2 of 242 missed, both with their reasons at the end of the table); the new tests pin
behavior on inputs the census itself does not hold.

| Case | Covering test, or the reason none is needed |
|---|---|
| The refusals of every enabled fence of the spec and the README | `enabled_fences` (snapshot) |
| The refusals of every step unit `tests/steps/**/*.zed` | `step_units` (snapshot) |
| The refusals of the 120 units of `programs.txt`, in 12 pieces, piece 4 split in four | `programs_0` to `programs_11`, `programs_4_unit_7` to `programs_4_unit_9` (snapshots) |
| A refusal whose phrase lies in a step or the menu, not the message: the reason takes that step or menu | reached by the census snapshots (the ` \| ` parts of their reasons) |
| A rejection of the front: `run::load` reports each of its messages | reached by every rejected unit of the census |
| Each kind found by its phrase; an undecided text of kind `Other`; a text that is no refusal | `kinds_are_found_by_their_phrases` |
| Several kinds in one text, in the list's order; a phrase twice is one kind | `cases::a_text_with_several_kinds_has_each_in_the_order_of_the_list` |
| Each undecided phrase alone is `Other`; a kind's phrase beside one is that kind alone; no text, a cut phrase, another letter case are no refusal | `cases::each_undecided_phrase_alone_is_of_kind_other_and_a_named_kind_wins` |
| The kinds have distinct names, none `Other`, and no phrase holds another, so each phrase marks one kind | `cases::every_kind_has_a_distinct_name_and_a_phrase_no_other_kind_holds` |
| A census line: tab-separated, kinds joined by commas, the reason trimmed and its line breaks written ` / ` | `cases::a_census_line_is_tab_separated_on_one_line` |
| Totals: each kind of a line with several counted, list order then `Other`, zeros left out, only the kinds field read, whole names only; the empty census | `cases::totals_count_each_kind_of_each_line_in_the_list_order_and_leave_out_zeros` |
| `programs.txt` reads back to its bytes: 120 units, each origin ending in `#` and 8 hex digits, lengths in bytes | `cases::the_programs_file_reads_back_to_its_bytes` |
| The pieces cover every unit once, in order, sizes within one of each other, at 1, 7, 12, 120 and 121 pieces | `cases::the_pieces_of_the_programs_cover_every_unit_once_in_order` |
| A malformed `programs.txt` (no header, no length, short text) | None: the file is a fixture written once by the census hook; a malformed file panics at its `expect`, naming what is missing, and `the_programs_file_reads_back_to_its_bytes` checks the file as it is |
| Classifying and counting scale linearly | `bench::classifying_and_counting_scale_linearly` (the `bench` module) |
| mod.rs line 82: `run::load` loads a unit the front rejects | None: a check that the two agree; `run::load` runs the same front first (`run::loaded` calls `compile` before `program`), so no unit reaches it |
| mod.rs line 86: a refusal only `run::load` reports | None today: the only errors `run::load` adds after the front are those of `run::program` (no `main`, several `main`s), whose messages hold no kind's phrase; the line lists such a refusal if the program checks ever give one |
