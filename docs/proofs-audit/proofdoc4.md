# Proofs in code comments: audit of proofdoc4 (DOC-proofs-in-comments-audit-rest-3)

Author, STANDING, 2026-11-20: "also you must add proofs and reasoning in the code comments too".
This fourth pass reads the entries the third pass ([proofdoc3](proofdoc3.md)) did not read:

- proofdoc3b's 275 not read: zedc-check 153, zedc-elab 44, zedc-base 39, and the 39 commits
  whose zedc and zedc-syntax code moved to other crates;
- proofdoc3a's 172 not read: zed-kernel 62, zedc-preimage 85, and 25 in zedc, zed-native,
  zedc-resolve, zedc-zir, zedc-syntax, zed-numtheory, zed-rt, zed-tools and zedc-lattice;
- proofdoc3c's 361 entries, which it read only through four filters: zedc-types 129,
  zedc-presburger 198, zedc-solvers 18, zedc-int 16;
- the four claims in other crates that proofdoc3b met and did not check: 84ed8e51d
  `Walk::get_key`, 3cdd34f55 `Tx::invert_sep` (zedc-preimage), 305ad0293
  `Sig::standing_twice` (zedc-types), 4e6c5bfaa `type_var_form` (zedc-resolve, with zed-kernel
  print/names.rs).

An entry is one commit in one crate. Each entry is read in full: its message, and every comment
line it added in that crate, in context. Then the code that relies on each claim is read as it
is today, at its current site, which may have moved since the commit. Each claim a verdict rests
on ends in one of three states. It is proved at its site, every step in a comment. Or it is
broken by a program, and fixed with a test that fails first. Or it is marked Not proved at the
site, with the open sub-case. The 808 entries are split over seven helpers, each with its own
section below, its own worktree and its own merges. Lists: /home/luke/Work/wt/proofdoc4-lists/.

| Section | Entries | Entries read | Claims found | Already there | Added or completed | Marked unproved | False |
|---|---|---|---|---|---|---|---|
| proofdoc4a | zedc-presburger, first 108 | | | | | | |
| proofdoc4b | zedc-preimage 85, `get_key`, `invert_sep` | | | | | | |
| proofdoc4c | zedc-types 129, `standing_twice` | | | | | | |
| proofdoc4d | zedc-check 153 | | | | | | |
| proofdoc4e | zedc-presburger, last 90 | | | | | | |
| proofdoc4f | zed-kernel 62, zedc-elab 44, zedc-base 39 | | | | | | |
| proofdoc4g | moved 39, zedc-solvers 18, zedc-int 16, the 25 in small crates, `type_var_form` | | | | | | |

## proofdoc4a: zedc-presburger, first 108 entries

Not started.

## proofdoc4b: zedc-preimage, and the two zedc-preimage claims

Not started.

## proofdoc4c: zedc-types, and `Sig::standing_twice`

Not started.

## proofdoc4d: zedc-check

Not started.

## proofdoc4e: zedc-presburger, last 90 entries

Not started.

## proofdoc4f: zed-kernel, zedc-elab, zedc-base

Not started.

## proofdoc4g: the moved commits, zedc-solvers, zedc-int, the small crates, `type_var_form`

Not started.
