# Proofs in code comments: audit of proofdoc3 (DOC-proofs-in-comments-audit-rest-2)

Author, STANDING, 2026-11-20: "also you must add proofs and reasoning in the code comments too".
This third pass reads what the second pass listed as not read (row
DOC-proofs-in-comments-audit-rest-2):

- the 156 commits of [proofdoc2](proofdoc2.md) "Not swept" (142 of them touch zed-kernel);
- the entries of [proofdoc2b](proofdoc2b.md) not read: its 28 at score 4 or more and the 382
  below. Its scoring cannot be rebuilt from its description, so this pass reads a superset:
  every entry (one commit in one crate, `git log --since=2026-11-01 6b9edf7fb -- crates/<crate>`
  for zedc-check, zedc-base, zedc-elab, zedc-types, zedc-presburger, zedc-preimage,
  zedc-solvers and zedc-int, less the commits named in proofdoc1.md and proofdoc1b.md) whose
  message matches `proof|prove|bound|invariant|derivation|derive|lemma|argument` at least once,
  less the commits in proofdoc2b's table: 820 entries, which hold the 28 and the elab parts of
  e5ff7920a and 7931d6ed6;
- [proofdoc2a](proofdoc2a.md)'s high-ranked zedc and zedc-syntax commits whose code moved out
  of those crates: the 39 commits since 2026-11-01 (to 6b9edf7fb) that changed a file of
  crates/zedc or crates/zedc-syntax that no longer exists, at score 3 or more on proofdoc2a's
  keywords (`proof|prove|bound|invariant|derivation|lemma|cannot|never|exact|argument`);
- the sites proofdoc2a names as not traced: zedc unit.rs `pinned` and `write_pins`, zedc-syntax
  builder.rs the hole taken once, and the grammar-shape `unreachable!`s and `expect`s;
- 80870e234 (PROOF-treap-digest-priorities), which proofdoc2b did not follow.

Commits after 6b9edf7fb are outside this pass. The work is split over three helpers, each with
its own section below: proofdoc3a (zed-kernel, read only, as kernel24 and kernel25 own it; the
lower crates; the front-end crates' part of the 156; zedc-preimage; 80870e234; the untraced
sites), proofdoc3b (zedc-check, zedc-elab, zedc-base; the moved commits), proofdoc3c
(zedc-types, zedc-presburger, zedc-solvers, zedc-int). Each claim a verdict rests on is proved
at its site, every step in a comment; or broken by a program, fixed with a test red first; or
marked Not proved at the site with the open sub-case.

## proofdoc3a: zed-kernel (read only), lower crates, front-end crates, zedc-preimage, untraced sites

Not yet written.

## proofdoc3b: zedc-check, zedc-elab, zedc-base, and the moved commits

Not yet written.

## proofdoc3c: zedc-types, zedc-presburger, zedc-solvers, zedc-int

Not yet written.
