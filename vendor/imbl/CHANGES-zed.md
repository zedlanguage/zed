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

Nothing here has been sent upstream.
