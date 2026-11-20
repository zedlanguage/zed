# Proofs in code comments: audit of proofdoc1 (DOC-proofs-in-comments-audit)

Crates swept: zedc-types, zedc-presburger, zedc-preimage, zedc-solvers, zedc-int, and the
`RunMark` site in zedc-check that dryC1 named. Sources, in order: the memos dryC1 named most
likely wrong in c4937d86c (re-proved first, each with a test that drops a value and builds a new
one at the same address); then the commits since 2026-11-01 that touch these crates and whose
messages name a proof, bound or argument (193 crate-commit pairs; the 37 pairs that added no
comment to the crate were each opened, the others counted as already there after reading their
added comments for a proof); then `command grep -a -i` of /home/luke/Work/wt/ledger.jsonl and
/home/luke/Work/wt/running-log.md for "not proved", "unproved" and "no proof" with these
crates' names (4 lines). The agent reports under /home/luke/Work/wt were not swept, and of the
commits only those named below were followed to their sites: the sweep is not complete.

Every memo dryC1 named is safe: none moved into zed-collections `ByAddress`. `RunMark` is safe
only by a fact about today's callers, which nothing enforces; its comment says Not proved and
the row TYPES-run-marks-move-safe makes it hold by type.

Counts per crate (found / already there / added or completed / marked unproved / corrected):

| Crate | Found | Already there | Added | Not proved | Corrected |
|---|---|---|---|---|---|
| zedc-types | 14 | 10 | 4 | 1 | 0 |
| zedc-presburger | 9 | 3 | 6 | 1 | 0 |
| zedc-preimage | 6 | 6 | 0 | 0 | 0 |
| zedc-solvers | 1 | 1 | 0 | 0 | 0 |
| zedc-int | 1 | 1 | 0 | 0 | 0 |

The `RunMark` proof is in ty.rs, so it is counted under zedc-types (its Not proved is the 1
there); its test is in zedc-check r10_tests.rs. A row naming several crates is counted under the
first. The 0588b18b0 row holds no argument and is not counted.

| Source | Claim | Code site | Status |
|---|---|---|---|
| c4937d86c (dryC1) | `pure_memo` keyed by part addresses reads no freed part | zedc-presburger presburger.rs `cell_sweep::cells_of` | added: proof, test `cell_sweep_reads_new_parts_at_the_address_of_dropped` |
| c4937d86c (dryC1) | `resolve_disj` memo keyed by addresses | zedc-presburger presburger.rs `resolve_disj`, `resolve_pure_or` | added: pointer to the proof at `pure_memo` |
| c4937d86c (dryC1) | `CellWalk` `memo` and `owns` keyed by `Rc::as_ptr` | zedc-presburger presburger.rs `cells_of` | added: proof (the input is borrowed; the walk is a local; the maps hold their Rcs) |
| c4937d86c (dryC1) | `BoundedWalk` `parts` and `ors` keyed by addresses | zedc-presburger presburger.rs `by_cells` | added: the same argument |
| c4937d86c (dryC1) | the order of `CellView::pieces` depends on addresses, no answer does | zedc-presburger presburger.rs `CellView::pieces` | added: proof from what `try_join` reads |
| c4937d86c (dryC1) | `Same::ids` keyed by row addresses | zedc-types ty.rs `Same` | added: proof, test `equality_reads_a_new_type_at_the_address_of_one_dropped` |
| c4937d86c (dryC1) | `Made` memos keyed by signature addresses | zedc-types ty.rs `Made` | added: four-step proof, test `renamings_read_a_new_signature_built_after_one_dropped` |
| c4937d86c (dryC1) | `some_value` `made` keyed by row addresses | zedc-types ty.rs `some_value` | added: proof |
| c4937d86c (dryC1) | `fn_index` keyed by addresses | zedc-types ty.rs `Pairs` | already there |
| c4937d86c (dryC1) | `entered` keyed by addresses | zedc-types ty.rs `first_seen_in` | already there (the walk borrows its input) |
| c4937d86c (dryC1) | `NameDigests::done` keyed by addresses | zedc-types ty.rs `NameDigests` | already there (`&'a`) |
| c4937d86c (dryC1) | `Encoder::memo` keyed by addresses | zedc-types ty.rs `Encoder` | already there (`Walked` holds the node) |
| c4937d86c (dryC1) | `RunMark` names only signatures held by `s` or `b` | zedc-types ty.rs `RunMark` | added: four-step proof; Not proved: callers read marks only of signatures in an `Arc` (step 3), not enforced; test `r10_tests::run_marks_name_a_new_signature_at_the_address_of_one_dropped` with a control that shows the hazard; row TYPES-run-marks-move-safe |
| 2516a0d3d | `by_halves` is O((m + k) log k) on a chain | zedc-presburger presburger.rs `by_halves_general` | added: proof (was in COMPLEXITY.md and at the bench only); Not proved: that each depth projects O(m + k) rows, counted at two sizes only |
| e2aba9df3 | the chunked build of `r5_leaf_frontier_fixture` gives the one-thread summaries | zedc-presburger extend.rs `r5_leaf_frontier_fixture` | already there |
| 29bbc866f | a chain's other parts are idle when the half-line certificate of their least holds | zedc-preimage product.rs `Scope::chain_rest_halfline_idle` | already there |
| 29bbc866f | `keep` loses no part when a chain is passed over whole | zedc-preimage product.rs `project_block` | already there |
| e5b5ea82e | no answer rests on the cost-only sites | zedc-solvers negsssp.rs; zedc-preimage spans.rs; presburger intervals.rs, shifts.rs | already there |
| df78c0880 | a chain of n ifs over n type parameters is checked in O(n log n) | zedc-types ty.rs, zedc-preimage product.rs | already there |
| a258b51b5 | `Sig::holds_no_var` gives the answer of the full walk in O(1) | zedc-types ty.rs `VarBits::is_empty` | already there |
| 97b5d1690 | a meet of functions over domains that differ is Never, (i) to (iii) | zedc-types ty.rs `Domains` | already there |
| 01cabf25c | the forward-need admission proof, parts (6), (7) and the refresh | zedc-types ty.rs; zedc-check r10_forward.rs | already there |
| a5b528407 | a variable standing once in an arrow's parameters may be widened | zedc-types ty.rs `repeated` | already there |
| 7591eae5c | a tuple held by a member of a shape's union is held as it is | zedc-types ty.rs | already there |
| b6895a66d | a chain over two inputs is summarized as `pa(v) + a*w` | zedc-presburger, zedc-preimage | already there |
| bbdf92520 | remaps alike share one need | zedc-preimage, zedc-types | already there |
| 41a8f58e2, cd8291d7e (gap1) | the min-gap chain's B trees have at most 15 nodes | zedc-preimage preimage_ref.rs, (C) | already there |
| e94c5eac6 | `Core::same` gets the coprime base of `coprime_base` | zedc-int | already there (proof at zed-numtheory `coprime_base_u64`, proofdoc1a) |
| running-log 2026-11-19 (neon-retry) | idle readers of `projected` (`contains_key` in product.rs) are not proved, only tested | zedc-preimage product.rs | already there as an open item of the `Scope::record` join tests; not re-proved here |
| 0588b18b0 | a placed entry reads its arguments before the buffer is emptied | zedc-presburger meter.rs | no argument at this site (a type alias only); the proof is in zed-native, swept by proofdoc1a |
