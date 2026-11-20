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

Part 1 of the list, entries 1 to 25 in score order, base commit 1915d2375. For each entry the
whole message and the whole diff under `crates/zedc-presburger` were read, and each claim was
checked at the code that relies on it on main today.

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zedc-presburger | 25 | 29 | 19 | 6 | 2 | 0 |

Of the 29, two are counted in no column: one claim (the race's bound, 24981fcda) and one research-branch behavior (4033def30) are no
longer relied on: the code they described is gone.

| Source | Claim | Code site | Status |
|---|---|---|---|
| 6ff7e1be7 | An outer meter around `Work::metered` is charged what the inner one used | meter.rs `Work::metered` | Already there |
| 6ff7e1be7 | 2 ms + 80 ns a unit bounds a cover's time | meter.rs `EXACT_LIMIT` | Already there (marked Not proved, decides only where a refusal falls) |
| 6ff7e1be7 | `a·s + c >= 0` gives `s >= ⌈-c/a⌉` for `a > 0`, `s <= ⌊c/-a⌋` for `a < 0` | zedc-int int.rs `row_range`, `row_bound` | Already there |
| 2143bead4 | No memo key names a freed node; `by_halves_general` O((m + k) log k) | presburger.rs | Already there, see proofdoc1 |
| 42273225f | `part_bounds` sound, exact hulls for difference rows, O(m log n) | presburger.rs `part_bounds`, `row_bounds`, `difference_hulls` | Already there |
| 3527c0a74 | An implied disjunction of one-row blocks is dropped with no change of points | exact.rs `implied_dropped`, `implied`, `met` | Already there |
| 030972c93 | The polygons cost no more than the join they replace | row_sums.rs `Plan::project`, plane.rs `project` | Already there (reworked by aabf487cc) |
| 80870e234 | Treap depth bounds need independent priorities | hull/rows.rs, extend/holes.rs, extend/images/intervals.rs `prio_of` | Already there, see proofdoc3a |
| d59fb9c44 | The rounds at the bounds reach one state in every order of events | forced.rs `Trial::holds` | Completed: the step named "Knaster–Tarski" with no steps is now proved by induction at the site |
| e5b5ea82e | The merge inequality behind O(n p log m log n) | extend/images/shifts.rs `Shift::apply` | Marked unproved (cost only; it was "not proved in Lean", and is proved nowhere) |
| 151c323ff | A forced row with one unknown bounds it by `⌈-b/a⌉` or `⌊b/-a⌋`; an equation needs `a \| b` | forced.rs `Graph::solve` | Completed: the local copy now calls zedc-int `row_bound` and `row_range`, whose comments derive both |
| 24981fcda | The join of row sums answers exactly | row_sums.rs module note | Marked unproved: the layer invariant is written nowhere; three open steps named (row PROOF-row-sums-join-exact) |
| 24981fcda | Nine papers cited | row_sums.rs "Papers" | Completed: the DOIs added (Bellman a book, Levin none on Crossref) |
| 24981fcda | The race's bound | (removed) | No longer relied on (PRES-switchover-not-race) |
| 7dd6559a9 | The forward certificate is sound; its decline leaves the loop unchanged; the work bound | exact/guarded.rs module note, exact.rs `exact_each` | Already there; completed: the CACM 1992 text had only the 1991 DOI, doi:10.1145/135226.135233 added |
| 5213e08d6 | Every disjunct is tested; the solver's refusal under every naming alike | presburger.rs `settle_as_sets` | Already there (Not proved, row PROOF-tied-projection-refusal-names) |
| a803272fb | The removed checks never fire | presburger.rs `cell_sweep`, `try_pick_disjoint_wide`; slack.rs `fill_row_model` | Already there |
| 09287a709 | Only pairs whose ranges meet can have a point; `meeting_pairs` gives each such pair once, k <= n for disjoint lists | exact.rs `two_distributed`, `atom_ranges`, `ranges_meet`; zed-collections intervals.rs `meeting_pairs` | Already there |
| 36e8b20a6 | A defined atom's values in a cell are `{x}`, `{c_0 - x}` or both; the substituted rows | presburger.rs `cell_sweep::sweep_involution` | Already there (substitution checked by hand) |
| 4033def30 | The cover keeps the solver's set where a question is refused | exact.rs `cover` | No longer relied on: a refused question now refuses the cover |
| 48dde176a | `Alone::point`'s answer does not depend on the names | presburger.rs `Alone::point` | Completed: the proof rests on `solve` answering alike under every naming, which is open (PROOF-solve-omega-path-renaming); the site says so |
| 48dde176a | An empty clause empties the regime | modular.rs `solve_regime_step` | Already there |
| 6130a038d | `Differences::search`: no name chooses; each node expanded at most twice | presburger.rs `Differences::search` | Completed: the steps written |
| 842e295c5 | Pugh's projection with a goal loses no value of the cell | exact/projection.rs `pugh`, `Held::push` | Already there |
| 9992e3560 | A hull bound moves only on a proof; `bounds_alone` sound | presburger.rs `tighten_each`, `Hull::tighten`, `bounds_alone` | Already there |
| 015f88415 | `tried` returns at most `allowed` used; `exempt` and `credit` move the limit by what they charge | exact.rs `exact_each`, `quick_search`; meter.rs | Already there (checked against the code) |
| 300df7ed3 | `liaproj` keeps one disjunct holding the point; splinter index `0 <= i < a` | exact/projection.rs `liaproj`, `dark` | Already there (splinter bound checked by hand) |
| 383cb5b66 | Batch and single projection each sound | presburger.rs `Level::open`, `batch_and_single_sound` | Already there |
| 9abde2cea | A snapped midpoint loses nothing; the question memo is sound | presburger.rs `Hull::tighten`, `Hull::asked_with` | Already there |

No code claim: zedc-presburger 7bfd6bba8.

Not read: ad40b4107 b467e298d b77467075 d6fa0ddbd d80e81d08 e22a4f8fa 0fe50a2fc 1ad3da05c
1faf391fd 1ffeb360d 355e67f4e 3e3db6907 4a8d78984 4e9bb0d27 5c102b331 78fdd83c1 8ee7ea8dd
90b8f2b61 a6562e094 e8fea7860 ea431f549 f0bde0d35 ff395d583 181ac91dd 1dc603590 1ff9a3b61
252abbb51 25ef78dd1 2b3e706f1 2d1365800 34989b330 36279a9f9 40bb19caa 4b1ccff17 53b114449
564bef57c 5bde6551f 65446a377 66e347e86 7bdf8c1f1 8e3867d18 94f38f6d3 96a4e186b 9758548e8
9e786fe17 a1a2a3c63 aa8366a07 ec537c0b1 ed1f1be11 f0186c022 f0ce6ac5e f4c033ccd f548497ad
fb9b82a6a 030a2d36d 136017dd7 28a3d9acb 32acdc5eb 384b173ac 4e48ee579 54ddb1f80 5dfd87a78
6e72af6bd 711b27b81 72d5f383f 7d23ca0c7 7dda7ea0d 7f771ec77 83ebfff6e 8575c70cc 8590c4d2b
889492a23 9f8961b3b a3273dbda a54f1b103 aabf487cc ac67403b3 ace60e16b b2ba71b22 c4964f39a
d73f3c8e1 f060dbed1 f835ff861 (later parts of this section).

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
