# L1.15 kernel terms: cases and the tests that cover them

Code under test: `crates/zed-kernel/src/term.rs`, `print.rs`, `walk.rs` and `print/dag.rs`.
Measured with `-C instrument-coverage` and `llvm-cov` over this group alone, regions% / lines%:

| File | Before | After |
|---|---|---|
| term.rs | 60.96 / 58.49 | 66.37 / 63.40 |
| print.rs | 89.03 / 87.22 | 92.30 / 92.75 |
| walk.rs | 64.45 / 64.74 | 85.55 / 86.45 |
| print/dag.rs | 5.44 / 7.46 | unchanged; tested in l01_28_staging |

| Case | Test that covers it | Or reason none is needed |
|---|---|---|
| Each term variant built, equal to itself and to its copy | complete.rs `a_term_of_every_variant_built_twice_is_equal_to_itself_and_its_copy` | |
| Each variant differs from every other and from itself with one part changed | complete.rs `each_variant_differs_from_every_other_and_from_itself_changed` | |
| Patterns differ by each part | complete.rs `patterns_differ_by_each_of_their_parts` | |
| Pattern `Debug` | complete.rs `a_pattern_alone_debugs_as_derived`; deep.rs `debug_writes_the_derived_text` | |
| A part changed in place gets a new id; a shared part is copied first | complete.rs `a_part_changed_in_place_takes_a_new_id_and_a_shared_one_is_copied_first` | |
| Each primitive written at its arity | complete.rs `each_primitive_is_written_at_its_arity` | |
| Primitive codes | m0_07_canonicalization prim_codes.rs | |
| Primitive names | l01_18_scalar_interpreter prim_names.rs | |
| Every form written at each width | forms.rs `every_form_is_written_as_before_at_each_width` | |
| Line breaking: fits, breaks, indents, braces, flat text, characters not bytes | layout.rs (6 tests) | |
| Notation of the design's examples (fold, reindex, discard, definedness, lattice fix, gen, ports, match) | notation.rs (9 tests) | |
| Binders named, `and`/`or` written as operators, type patterns, declared shared parts | written.rs (9 tests) | |
| Read back: elaborated, built, entries, primitive functions, any-atom | read_back.rs (4 tests) | |
| Evidence is part of the address, not read by the evaluator; grades print by name | evidence.rs (4 tests) | |
| Deep and wide terms: copy, compare, print, drop | deep.rs, scaling.rs; benchmarks in bench.rs | |
| DAG printing of shared parts | l01_28_staging print.rs, differential.rs | Staging prints the DAG form |
| `pretty_in` | l01_28_staging print.rs | The printer for a user, tested with staging |
| `Prim::written_with`, `Prim::named` | m0_09_kernel_evaluator complete.rs `an_ill_typed_application_is_reported_as_a_compiler_bug_naming_it` | The evaluator names the primitive in that report (eval.rs) |
| `Prim::in_words` of `Path` | none | `Path` is built by staging; its words are read only where eval.rs reports a type error on it |
| `unreachable!` arms in `walk.rs` `shallow`/`copy` and `print.rs` `enter` | none | Unreachable by construction: each match only meets the variants its caller passes |
| `Shared::unwrap_or_clone` | l01_28_staging | Called by zedc-stage only |
| `Term::site_key`, and the site check in `walk.rs` `copy` | none | Used by `sites.rs` when `zedc::run` (run.rs `wave`) sets sites to place a run-time error in the program text; terms built in this group carry no sites |
| `walk.rs` `small`, and `held_twice` on a small part | l01_28_staging print.rs | Called by `print/dag.rs` |

Printer issues noted, not failures against DESIGN (DESIGN does not fix the kernel's printed text):
`Get`, `TupleGet` and `At` all print as `a[b]`; `Count` prints `count(a)` while `written()` gives
`.count`; an atom whose name is not a literal prints `#_()`.
