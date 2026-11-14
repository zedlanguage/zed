# Completeness: derivations and exact preimages on demand (L1.39b)

Row TEST-complete-reduced (author P189). The code under test is the building of a
rejection's derivation only when the rejection is reported (the counter `derivation_steps`
and its three increments in `crates/zedc-check/src/check/walk.rs`: a declared parameter's
step, where a value came from, and each default on the way), and the search of an exact
preimage only in a scope declared `@exact` (the counter `exact_steps` and its two increments
in `crates/zedc-preimage/src/preimage.rs`, reached through `Scope::exact`). Expected results
are from DESIGN.md step L1.39b, sec:plan ("Optional properties are computed on demand", items
4 and 6) and the store's `@exact` test for emptiness (sec:constraints, step L1.39).

llvm-cov of this group's tests, as a floor, regions (lines) before → after:
`crates/zedc-check/src/check/mod.rs` 40.89% (44.94%) → 45.71% (49.73%);
`crates/zedc-check/src/check/walk.rs` 32.92% (34.39%) → 40.49% (42.00%);
`crates/zedc-preimage/src/preimage.rs` 22.73% (25.29%) → 27.18% (29.52%);
`crates/zedc-preimage/src/product.rs` 12.13% (14.28%) → 14.93% (17.12%). Of the three
derivation increments, the two in `came_from` (walk.rs, where a value came from and each
default) were not reached before and are now.

Tests in `completeness.rs` unless a file is named.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| A clean program of n functions builds no derivation; one with a bad condition is rejected with its derivation | `mod.rs` `the_program_of_n_functions_is_accepted_and_the_one_with_a_bad_condition_is_not` | |
| Every accepted corpus and step unit builds no derivation and searches no exact preimage | `mod.rs` `a_corpus_unit_with_no_rejection_builds_no_derivation` | |
| Many declared parameters, no derivation | `mod.rs` `functions_of_many_parameters_are_accepted_with_no_derivation` | |
| An accepted unit of each construct (narrowing `if`, bit word under tests, failure with `else`, string and code-point words, lambda, tuple, test table, build-stage `if`) builds neither | `an_accepted_unit_of_each_construct_builds_no_derivation_and_no_preimage` | |
| Each kind of derivation a rejection reports: a declared parameter, a named value passed, a value through a name to a bit word, a value through defaults | `each_kind_of_reported_rejection_builds_its_derivation` | |
| A rejection with no derivation to build (an operation that always fails, a syntax error) | | DESIGN asks only that no derivation is built for a unit that reports none; how many parts a reported one counts is the message's (step L1.29) |
| One rejection of a fixed size costs the same among n functions and 8n | `one_rejection_of_a_fixed_size_builds_the_same_derivation_among_3_functions_and_24`; `bench.rs` `one_rejection_builds_the_same_derivation_among_n_functions_as_among_8n` | |
| Reading a counter resets it; an accepted unit after a rejected one builds nothing | `reading_a_counter_resets_it` | |
| A counter counts its own thread's work only | `a_counter_counts_the_work_of_its_own_thread_only` | |
| Plain scopes search no exact preimage | `exact.rs` `plain_scopes_search_no_exact_preimage`; `each_exact_scope_of_a_fixed_size_searches_the_same_boxes` | |
| One exact scope among n plain scopes and among 8n | `exact.rs` `one_exact_scope_searches_the_same_boxes_among_n_plain_scopes_as_among_8n` | |
| Each exact scope of a fixed size searches the same boxes: two cost twice one, whatever plain scopes lie between | `each_exact_scope_of_a_fixed_size_searches_the_same_boxes` | |
| An exact scope with no point is bottom, found by its search; the plain scope is not bottom and searches nothing | `an_exact_scope_with_no_point_is_bottom_and_a_plain_one_is_not` | |
| `@exact` written in source, on a declaration or an expression | `source_exact_is_not_compiled_yet` | its syntax is step L15.1; this zedc refuses it as not compiled, and nothing is searched |
| A unit that reads `@exact` searches its preimage, scaled at n and 8n functions | | step L15.1 (source syntax); the scope-level tests above stand in |
| Scaling of the check with no rejection, and with many parameters | `bench.rs` `checking_functions_that_ask_for_no_derivation_scales`, `checking_functions_of_many_parameters_scales` | |
