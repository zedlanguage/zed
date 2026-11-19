# Changes made for zed

This directory is a copy of imbl 7.0.2 as published on crates.io (upstream commit
834c67f1e08c63a4d662a4132425026a4cea7b25), used by the zed workspace through
`[patch.crates-io]` in the workspace Cargo.toml. It is licensed under the Mozilla Public
License 2.0 (LICENCE.md); each changed file keeps its license notice and says what changed.

2026-11-16, plan row IMBL-diff-branch-skip (COMPLEXITY.md PA-bind-cost in the zed repository):

- `src/nodes/btree.rs`: `Cursor::advance_skipping_shared`, which `OrdMap::diff` and
  `OrdSet::diff` call after each equal key, now steps over a subtree shared by both maps at
  any level without entering it (`step_over`, `step_entry`, `pending`, `enter`, `align`).
  imbl 7.0.2 entered the first leaf of every shared sibling of a changed path, O(B h²) nodes
  for maps that differ in one key; now O(B h). The proof is in the comment of
  `advance_skipping_shared`. `Node::level` is `pub(crate)`. Test-only additions: the counter
  `PUSHES` of nodes entered, and `Node::addresses`.
- `src/ord/map.rs`: tests only: `diff_skips_a_shared_subtree_at_the_root`,
  `diff_work_grows_with_the_height` and `diff_of_each_change_at_each_size`.

2026-11-19, plan row PERF-satellite-random-under9-redesign (stage 2):

- `src/nodes/btree.rs`: added join-based `Node::union_with_key` using
  `Node::split_lt`, `Node::join_with_sep` (`join_right`, `join_left`), and
  `Node::insert_with_key`, running in O(m log(n/m + 1)) for sizes m <= n
  (Blelloch, Ferizovic and Sun, SPAA 2016; Brown and Tarjan, JACM 1979).
  Strengthened `Branch::check_sane` (test/fuzzing only) to check the separator
  key invariant `max(left) < sep <= min(right)`.
- `src/ord/map.rs`: `GenericOrdMap::union` and `GenericOrdMap::union_with_key`
  now delegate to `Node::union_with_key`; added tests
  `union_with_key_sane_and_exact_across_shapes`,
  `union_disjoint_ranges_costs_logarithmic_comparisons`,
  `union_balanced_merge_tree_costs_n_log_n_comparisons` and
  `union_of_random_shapes_with_removes_after_matches_a_btreemap`. The last checks
  sanity only for maps with no `remove` in their history: imbl 7.0.2's `remove`
  rebalances a branch only below THIRD keys, while `check_sane` (and the comment on
  `Branch`) asks non-root branches for MEDIAN - 1, so a map built by removes can fail
  `check_sane` with unmodified imbl too (found 2026-11-19; lookups are unaffected).
- `src/ord/set.rs`: `GenericOrdSet::union` now delegates to
  `GenericOrdMap::union`.

Nothing here has been sent upstream.
