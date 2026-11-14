# M0.3 completeness: the grammar tools

Code under test: the `zed-tools` crate (`crates/zed-tools/src/`): `check`, `ring`, `cases`,
`fences`, `layer`, `audit`, `fuzz`, `fence_layers`, `progress`, `sync`, `cite`, `conflicts`,
`plan`, `llp`, `split`, `spec`, `spec_checks`, `syntax`, `text`, `random`, over small specs
built from the real grammars (DESIGN.md sec:grammar, step M0.3, and the plan rows each tool
names).

Coverage (llvm-cov, regions, before and after this pass): `cases.rs` 67.3% to 94.1%, `check.rs`
84.7% to 99.0%, `layer.rs` 71.6% to 95.5%, `progress.rs` 80.3% to 84.4%, `ring.rs` 88.5% to
93.4%, `spec_checks.rs` 57.7% to 61.3%, `sync.rs` 78.5% to 79.4%, `syntax.rs` 85.3% to 95.6%,
`text.rs` 82.9% to 100%, `fence_layers.rs` 97.1% to 97.8%; `llp.rs` 94.1%, `conflicts.rs`
96.7%, `audit.rs` 94.1%, `fuzz.rs` 93.7%, `split.rs` 93.4%, `plan.rs` 94.0%, `spec.rs` 96.3%,
`cite.rs` 74.5%, `lib.rs` 16.4%. `catalog.rs`, `imports.rs` and `step_targets.rs` are at 0%:
this group does not use them. The tests added after the measurement (`llp`, `split`, `fuzz`
below) cover more of `llp.rs`, `split.rs` and `fuzz.rs`.

| Case | Covering test, or the reason none is needed |
|---|---|
| `check`: a spec whose fences parse; a fence that does not parse, named at its line; a fence that is not there; a rule with no definition; a production with no desugaring rule; a fence left open; too few grammars; a rule in both grammars; a missing spec | `mod.rs` (`check_*`, `a_fence_left_open_*`, `a_spec_with_too_few_grammars_is_refused`, `a_rule_defined_in_both_grammars_is_refused`, `a_missing_spec_is_reported_with_its_path`) |
| Each report of `check` and `ring`: LAYER, MARK, DESUGAR (no production, two rules), TREE CHANGES, LEX, FAIL of a hole, DOC; FILE:LINE; a token rule with no kind; Python's `repr` | `check_reports::*` (9 tests) |
| `cases`: the real cases and left-recursion cases; each form of a case line; each way a case fails; a line that is no case; each block of leftrec; a missing cases file | `cases_runs::*` (6 tests), `mod.rs::cases_passes_on_the_real_cases_and_fails_on_a_wrong_bracketing` |
| `fences`, `ring` | `mod.rs::fences_counts_the_fences_and_lines_of_both_documents`, `ring_gives_the_lowest_ring_of_each_file_and_fails_on_one_that_does_not_parse` |
| `layer`: the table of defined words, a table that does not read, each word in its own position, a program and its files, a unit that does not parse, labels; each of the five target values (`#mcu` was missing, FAIL-layer-mcu-target-value) in a type, a pattern and an expression, and in `@require(target: …)` and `with target(…)` | `layer_roles::*` (7 tests), `mod.rs::layer_*` (3 tests), `fail_layer_mcu::*` (2 tests) |
| `audit`: needs, exact checklists, stale entries, old indexes, no part A, unreadable rows and each reason, entries in another layer's row | `mod.rs::audit_*` (9 tests) |
| `fuzz`: the same report for one seed, a sentence the old `break` derives, the real grammar; a count or seed that is not a number | `mod.rs::fuzz_*` (4 tests) |
| `fence_layers`, rejection rows | `mod.rs::fence_layers_*`, `rejection_rows_name_each_row_up_to_a_parenthesis_outside_code` |
| `progress`: steps marked done, a design with no plan, a long title cut, lines that only look like steps | `mod.rs::progress_*`, `tool_edges::progress_cuts_a_long_title_and_skips_what_is_no_step` |
| `sync`: copies written and a stale one found, no kernel grammar, the table of words, the directory or variable, prelude laws, build modes, a documentation fence's copy, no table of defined words | `sync::*` (6 tests), `tool_edges::sync_*` (2 tests) |
| Prose checks: kernel rules and T rules, prelude laws that disagree | `prose_checks::*` (2 tests) |
| `cite`: labels, steps, words that only contain a step, DESIGN.md, plan rows, dagview, exempt paths, no plan | `cite::*` (12 tests) |
| `conflicts`: pairs and paths, shared paths, a stale list, changed text, a plan that fails, no sections, an unknown option, a remark in a path span | `conflicts::*` (9 tests) |
| `plan`: levels and counts, needs with no row, duplicate ids, levels, cycles, stale counts, bars in titles, `--fix` in each case, unknown flags, this repository's plan | `plan::*` (24 tests) |
| `llp`: the real grammar's conflicts, stacks, nullable symbols, cycles, head copies, lookaheads, re-tagging rules, bad rules; a character class or an undefined name refused | `llp::*` (10 tests) |
| `split`: split and whole parse agree on the corpus and on damaged programs, cuts, lookaheads, a grammar the scan cannot read (brackets, no tokens, undefined names, a character class, a match inside brackets that leaves one open or closes one) | `split::*` (9 tests) |
| `cite::run`, `progress::run` and `done_row`, `sync::run`, `conflicts` with its default path | None in a test: they read this repository or call `git`; their logic is tested through the functions they call with a spec directory |
| `spec_checks` build modes (`build_modes`, `before_build`, `undefined_builds`, `defined`, `is_layer`) | Tested with their step in l07_03_unit_log_off/modes.rs |
| The test directories of the helpers: a name given once per test binary, under the binary's name (TEST-m0_03-flake) | `test_dirs.rs::a_test_directory_name_is_given_once_and_lies_under_the_binary_name` |
| `lib.rs` `main_of`, `compiler_dirs` | None: entry points of the binaries |
| `syntax.rs` `Tokens::char_at` and the `Expected::Class` closure | None: a grammar over tokens has no character class and no character to read (the character engine is tested in l01_08 `grammar_errors`) |
| `split::run` over files, `fuzz` output of a differing ring, `llp::run` with a rules file | Not yet covered: these print paths of the binaries, reached only on a failing grammar or a file argument |
| Large inputs | Benchmarks; `scaling::each_tool_benchmark_passes_at_small_sizes` and the `*_at_small_sizes` tests |
