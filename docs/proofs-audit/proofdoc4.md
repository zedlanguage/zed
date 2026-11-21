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

Part 1 of the list, entries 1 to 25 in score order, base commit 1915d2375; part 2, entries 26
to 65, base commit 57ba7215b; part 3, entries 66 to 108, base commit b3be07e47. For each entry
the whole message and the whole diff under `crates/zedc-presburger` were read, and each claim
was checked at the code that relies on it on main today.

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zedc-presburger | 108 | 116 | 64 | 42 | 3 | 0 |

Of the 116, seven are counted in no column: they are no longer relied on, since the code they
described is gone: the race's bound (24981fcda, and again ec537c0b1), a research-branch
behavior (4033def30), the foreign-factor rule of `products` (e8fea7860), the batch and single
hulls agreeing (3e3db6907), the cancellation of products through opposite signs (f0ce6ac5e)
and the two facts `plane::allowance` rested on (c4964f39a).

One code change, in part 3 (8590c4d2b): the proof that `two_pins.rs` `bounded` reads a part
exactly from the polygon of its kept half-planes assumed the queue leaves no redundant row,
which nothing checked; a redundant row would leave corners of the polygon outside the region.
`bounded` now checks in O(V) that every kept row crosses its edge forward (the next row is
above zero at the corner before), and declines otherwise, so the part is read by its rows,
which is exact. The proof is written at the site in four steps. No input that the old code
answered wrong was found: the new test
`edges_tests::a_polygon_found_holds_every_half_plane_at_every_corner` (20,000 seeded systems)
passes with and without the check, so it is counted under "Added or completed", not
"Corrected".

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
| ad40b4107 | The cover ends with the exact projection; its count of questions; `joined` rows suffice; `negated` is the integer negation | exact.rs module note, `joined`, `negated` | Already there (the count of questions checked) |
| b467e298d | Every writing answered gets one set and one cause, functions of the formula | presburger.rs `project_each_with` | Already there |
| b77467075 | The shrink counts are those of the rows held after each `refresh` | presburger.rs `System::shrink`, `System::touch` | Already there |
| d6fa0ddbd | `names_in` keeps a prime; O(length) | refusal.rs `names_in` | Already there |
| d80e81d08 | A meet only narrows, so the first crossed range ends the scan | presburger.rs `one_term_bounds` | Already there |
| e22a4f8fa | Two stars of one class share one core but for the leaf's name | conjuncts.rs `class_core` | Already there (the reuse argument is in zedc-preimage) |
| 0fe50a2fc | The certificate on the part's allowance keeps the bound `4·k·L` | exact.rs `exact_each` | Already there (as 015f88415) |
| 1ad3da05c | A part with more atoms than definitions plus 2 declines from every atom | exact/guarded.rs `prepare` | Already there |
| 1ffeb360d | `two_var_domains` is exact | presburger.rs `two_var_domains` | Already there (the last step rests on zedc-solvers `project_convex`, proofdoc4g's crate) |
| 355e67f4e | `part_bounds`, `propagate`, `eliminate`, `hull_side` O(log d); each tier implies the one before | presburger.rs `part_bounds`, `propagate`, `eliminate`, `hull_side`, `Tier` | Already there |
| 4a8d78984 | `System::pendants` eliminates as the rows one at a time do; `Omega::deferred` changes only the order | presburger.rs `System::pendants`, `Omega::deferred` | Already there |
| 4e9bb0d27 | The cover's work does not depend on the order of the parts | presburger.rs `project_each_asked` | Already there |
| 5c102b331 | Two passes of arc revision over a forest of tie classes give each atom exactly its values | presburger.rs `forest_domains` | Completed: the five steps written; Freuder's DOI added |
| 78fdd83c1 | `by_intervals` exact; the doubling reaches each value of a range; `Group::window` exact | row_sums.rs `Plan::by_intervals`, `Plan::add`, `Group::window` | Completed: the doubling invariant at `Plan::add`; `window` is an open step of PROOF-row-sums-join-exact |
| 8ee7ea8dd | `Blocks::forest` holds exactly the entries whose block is in the forest, in order | conjuncts.rs `Blocks::put`, `detach`, `undetach` | Already there |
| 90b8f2b61 | `sink_rows`: each row is `s * e + c >= 0` with `s = ±1`; the two substitutions | presburger.rs `cell_sweep::sink_rows` | Already there (substitutions checked by hand) |
| a6562e094 | The probe's result does not depend on the order of the parts | presburger.rs `probe_unhandled` | Marked unproved: which disjuncts without a point reach `settle` depends on the order; the open sub-case written at the site |
| a6562e094 | A search without the one-atom sets that finds no point means none with them | presburger.rs `search_by_halves`, `OneAtomSet::holds` | Already there |
| e8fea7860 | The foreign-factor rule of `products` loses no proof | presburger.rs `products` | No longer relied on: replaced by `pairs::kept` |
| ea431f549 | `exact_side`: rows left by an exact elimination give the side | presburger.rs `exact_side` | Already there (rests on PROOF-shadow-exact) |
| f0bde0d35 | Eleven assumptions stated at their sites | presburger.rs, 11 sites | Already there as Not proved; completed at `atom_disjoint_parts`: two of its three steps proved, the third (a group's model names only its atoms) left open |
| ff395d583 | The trial at the bounds: a true answer is exact; free of names and order | forced.rs `Trial::holds` | Already there (proved in part 1) |
| 181ac91dd | A product alone holding a free atom can go; the fixpoint does not depend on order | pairs.rs module note | Completed: the induction from "monotone" to "the rows left do not depend on the order" |
| 3e3db6907 | Batch and single hulls agree where neither reports a cause | presburger.rs `by_halves_against_old` | No longer relied on: replaced by `batch_and_single_sound` |
| 1dc603590 | A leaf's disjunction may hold parts of the leaf alone | conjuncts.rs `Conjuncts::star` | Already there |
| 1ff9a3b61 | The polygons' projection is exact where each pair has a side of coefficient 1 | row_sums/plane.rs module note | Completed: Pugh was cited by name only; both DOIs added |
| 252abbb51 | No formula reaches the walk's tested branches | pick_wide_tests.rs module note | Already there (stated "not shown") |
| 25ef78dd1 | The envelope test; the monotone chain; `mod_hat` serves Pugh's step | presburger.rs `upper_envelope`; exact/projection.rs `project_read` | Already there (the cross-multiplied test checked by hand) |
| 2b3e706f1 | `full_dark`'s length is concave, so a binary search finds its peak | exact/guarded/two_pins.rs `poly_values` | Completed: the concavity steps written |
| 2b3e706f1 | `fenwick_split` finds the longest prefix below the target by one descent | presburger.rs `BoundedPickRow::fenwick_split` | Completed: why every weight is above 0, which `descend` needs |
| 2d1365800 | Two disjunctions projected exactly by distribution; an answer can need n²/2 pieces | exact.rs `two_distributed` | Already there (checked by hand) |
| 34989b330 | A stride is its range met with its class | exact.rs `block_set` | Already there |
| 36279a9f9 | A face is exact; one congruence kept of several | extend.rs `Faces::face`, `congruences_once` | Already there (rests on PROOF-shadow-exact) |
| 40bb19caa | No integer point lies past the real bound of the rows, rounded | presburger.rs `real_end` | Completed: the steps written; the 1991 DOI added |
| 4b1ccff17 | A clause whose literal holds the unit's set is dropped; `res_within` is the subset test | modular.rs `solve_regime_step`, `res_within` | Already there |
| 564bef57c | `row_box`: each set holds every value at a point; free of order and names | presburger.rs `row_box` | Already there |
| 5bde6551f | `force`: a term with `\|c_i\| > W − w_i` takes one value; `scaled` keeps the points | row_sums/classes.rs `force`, `scaled` | Already there (each step checked) |
| 66e347e86 | Every bound `drop_by_bounds` propagates is implied, so a removed disjunct has no point | presburger.rs `drop_by_bounds` | Completed: the invariant proof over `narrow` and `narrow_or`; stale test paths fixed at three sites |
| 7bdf8c1f1 | `two_ranges_of_one_value` exact; n²/2 pieces in bits; emptiness as hard as 3SUM; the class of `Classed::join_all` | exact.rs `two_ranges_of_one_value`, `two_distributed`; refusal.rs `Classed::join_all` | Already there (the ternary bound checked); the tests and what they cannot catch named at both sites |
| 8e3867d18 | The pairs counted before the cut are those charged at least `PIECE`, so a cut refuses only what the limit would | exact.rs `past_what_is_left` | Completed: the five steps (pairs counted, no `credit` on the path, `exempt`, the same strict test, `tried`) |
| 94f38f6d3 | The union over blocks is exact | exact.rs `block_set` | Already there |
| 94f38f6d3 | The hull's ends may be added to each block | exact.rs `block_set` | Completed: union and meet commute with meeting the hull |
| 96a4e186b | `along_shared_atoms`' order depends only on the rows, so one `cover_input` gets one answer | row_sums.rs `along_shared_atoms` | Completed: atom numbers follow names (`Rows::of` sorts by atom), which `cover_input` fixes |
| 9758548e8 | The dark shadow of the chained pipeline makes at most 4 rows per elimination | bench omega.rs `project_each_on_a_chained_pipeline_scales` | Already there (the invariant checked) |
| 9e786fe17 | A disjunction the box makes true can be left out | presburger.rs `without_box_true_disjunctions` | Completed: one step said "hull is empty" where the hull is every value (no bound); corrected in the comment, the code was right |
| a1a2a3c63 | `least_step` equals the walk | row_sums.rs `least_step` | Completed: the interval division proof, the test and its limits |
| a1a2a3c63 | The join stops at the same operation on every run | row_sums.rs module note | Already there (no hash order is read) |
| aa8366a07 | `join_lone_disjuncts` keeps the points | presburger.rs `join_lone_disjuncts` | Completed: why the final `retain` removes only the disjunctions emptied there; "never coarser" stays marked "Assumption, not proved" |
| ec537c0b1 | The four maps of a fused pair | row_sums.rs `Plan::fused` | Completed: the derivation of each map from the class sums |
| ec537c0b1 | `lattice`'s five parts cover the points | row_sums.rs `lattice` | Already there |
| ec537c0b1 | The doubling race costs at most 4 times | (removed) | No longer relied on (removed by a1a2a3c63) |
| f0186c022 | Two-term rows never widen a base row under elimination | presburger.rs `narrow_disjunction_hulls` | Completed: the pairing step (a row of w terms with a row of two gives at most w) |
| f0ce6ac5e | Products cancel only through opposite signs | presburger.rs `products` | No longer relied on: replaced by `pairs::kept` |
| f4c033ccd | The ray cap of `lean`; `envelope` keeps the rows the others do not imply; dropping free division pairs keeps integer satisfiability | extend.rs `lean`, `envelope`, `without_free_pairs_for` | Already there (each step checked) |
| f4c033ccd | `hull_of` may cut the ends at the form's bounds | extend.rs `hull_of` | Completed: the upper-envelope steps for both ends, tests and what they cannot catch |
| fb9b82a6a | The box test of two-term rows; dominated rows dropped in any order; the shrink count; pivots keep equality lengths; `repivot` renews one slot per variable | presburger.rs `implies_in_box`, `System::dominated`, `System::shrink`, `Equalities::repivot` | Already there (each step checked) |
| 030a2d36d | Treap priorities: ties at most (S + 1)/p a pair, 5-wise independent, O(log n) expected depth | hull/rows.rs, extend/holes.rs, extend/images/intervals.rs `prio_of` | Already there (DOI at each site; the (S + 1)/p bound checked) |
| 136017dd7 | A settled fast reading gives the slow reading's refusal and cause; `Repair::Empty` shows no point | presburger.rs `pick_reading`, `local_repair_status` | Completed: the step through `TermValues::specialize`, the tests and what they cannot catch |
| 28a3d9acb | The shared step keeps the call within 4·k·L | exact.rs `exact_each` | Completed: the test named and what it cannot catch |
| 32acdc5eb | The treap tie bound restated | the three `prio_of` sites | Already there (as 030a2d36d) |
| 384b173ac | `Cursor` holds its iterator borrowing the conjuncts | conjuncts.rs `Cursor` | Already there (the borrow is in the type) |
| 384b173ac | `UpperHull` keeps the upper envelope | upper_hull.rs `UpperHull::of`, `insert`; presburger.rs `upper_envelope` | Completed: Andrew's DOI at both sites, the envelope's "everywhere" step, the test and its range |
| 4e48ee579 | `dark_is_real`; the dark shadow is exact where it equals the real | presburger.rs `Side1::dark_is_real`, `shadow` step (5) | Already there (equal floors give the same integer bound, checked) |
| 4e48ee579 | The summaries of a chain are exact | extend.rs `Summary` | Completed: the link step ∃y.(d ∧ ∃z.B) = ∃yz.(d ∧ B), the facts used, the test and what it cannot catch |
| 54ddb1f80 | `satisfiable` drops the disjuncts the bounds refute, which have no point | presburger.rs `satisfiable_inner` `ask` | Completed: the proof it rests on (`drop_by_bounds`), what `None` means, what the test cannot catch |
| 5dfd87a78 | A factor's hull over its own part equals its hull over all premises where they have a point | presburger.rs `products` | Completed: the restriction and join steps, the empty case, two tests; a stale test path corrected |
| 6e72af6bd | `project_each` answers empty sets where the forced propagation proves the formula empty | presburger.rs `project_each_as_named`; forced.rs | Completed: the step written at the site; stale test paths fixed in two places |
| 711b27b81 | `learn` no longer records the implied bounds of a lone remaining disjunct | presburger.rs `learn` | Already there (leaving out implied facts cannot make an answer wrong) |
| 72d5f383f | Faces holding nowhere show the conjunction holds nowhere | extend.rs `Faces::free` | Already there |
| 72d5f383f | A point `Faces::free` finds is a point of the conjunction | extend.rs `Faces::free`; residues.rs `Reading` | Completed: the extension and join steps (`Within` only narrows) |
| 7d23ca0c7 | Faces of parts with disjunctions are exact projections; clauses and congruences said once | extend.rs `project`, `projected`, `clauses_once`, `congruences_once` | Already there (each step checked) |
| 7dda7ea0d | `PartCache`: a later symbol reaching a step that does not read it gets the same outcome at the same charge | exact.rs `PartCache`, `exact_each_checked` | Completed: the same-limit step, the test and what it cannot catch |
| 7f771ec77 | A kept atom passed between halves leaves `projected_each` equal to `by_halves` | presburger.rs `projected_each` | Completed: each step checked; what the test cannot catch added |
| 83ebfff6e | The sign `flips` chooses reads the equation, not the names; the meet of the writings' projections is sound | presburger.rs `flips`, `project_each_written`, `meet_each` | Completed: the two tests and what they cannot catch |
| 8575c70cc | A disjunct `refuted_by_links` removes has no point with `p` | presburger.rs `refuted_by_links` | Completed: the steps and the test; a stale test path fixed in `probe` |
| 8590c4d2b | `edges`: the kept half-planes are the part's polygon | two_pins.rs `bounded` | Completed with a code change: the proof needed every kept row to cross its edge, which nothing checked; the O(V) check, the four-step proof and a new test added (see above) |
| 8590c4d2b | The stretch length is concave; the open ends follow the dark shadow | two_pins.rs `poly_values`, `u_values` | Already there |
| 889492a23 | Pushing ancestor unary bounds into blocks, and an empty met box, keep the answers exact | exact.rs `read_once` pass 0 | Completed: steps 1 to 3, the tests and what they cannot catch |
| a3273dbda | `shadow`'s trial elimination is exact; `point_of` extends a point of the rows left; implied rows give sound hull bounds | presburger.rs `shadow`, `point_of`, `project_parts` | Already there (rests on PROOF-shadow-exact) |
| a54f1b103 | A point at the end of a sound hull, or past it, shows the end is the bound | presburger.rs `Hull::tighten` | Completed: the step, two tests against brute force, what they cannot catch |
| aabf487cc | The polygons, where they answer, cost no more than the join they replace | row_sums.rs `Plan::project` | Completed: the join with no limit is `Plan::prefixes`, the same calls in the same order, and `Plan::step` charges by its inputs alone; the test and what it cannot catch |
| ac67403b3 | The one-term rows of `disjunction_hulls` keep the part's points and join no two groups | presburger.rs `Level::open` | Completed: the step through each disjunct implying the rows; what the test cannot catch |
| ace60e16b | `eliminated` is exact over the integers or `None` | presburger.rs `eliminated`, `shadow` | Already there (PROOF-shadow-exact) |
| c4964f39a | The two facts `plane::allowance` rests on | row_sums.rs (removed) | No longer relied on: aabf487cc replaced the allowance by the join's own tables |
| d73f3c8e1 | The reading's even charge sums to `w`, each at most L; the call stays within 4·k·L | exact.rs `exact_each` | Already there (each step checked) |
| f060dbed1 | The join-based merges of the block indexes cost O(W log W) in all | conjuncts.rs `Blocks::at`, `moving_at`, `names_in`, `pairs`, `merge` | Completed: the DOIs of Blelloch–Ferizovic–Sun, Brown–Tarjan and Tarjan 1975 at the five sites |
| f835ff861 | Each built case is empty, gives its answer or makes its kind | presburger.rs `BOX_EMPTY`, `ANSWERS`, `LADDERS` | Already there (the arithmetic of `BOX_EMPTY` checked; each case has its own test) |

No code claim: zedc-presburger 7bfd6bba8 1faf391fd 53b114449 65446a377 ed1f1be11 f548497ad
9f8961b3b b2ba71b22.

Not read: none.

## proofdoc4b: zedc-preimage, and the two zedc-preimage claims

All 85 zedc-preimage entries of the list were read, base commit 1915d2375, with the two claims
proofdoc3b met and did not check: `Walk::get_key` (84ed8e51d) and `Tx::invert_sep`
(3cdd34f55). For each entry the whole message and the whole diff under `crates/zedc-preimage`
were read, and each claim was checked at the code that relies on it on main today. Two commits
not in the list, 364dd4a15 and 526f13c51, are cited by entries and have rows of their own. Five
claims were false in the code, not only in the comment, and are fixed, each with a test that
fails before the fix and passes after it:

- F1, threshold.rs `floor`: it negated the whole set at each call, O(P), so `members` cost
  O(N·P), not the O(N log N) its comment states; `floor` now mirrors `ceil` and costs
  O(log P). Test `threshold::tests::bench::many_upper_bounds_on_a_name_of_many_pieces_cost_near_linear_time`
  (red by its time limit, green at a ratio of 8.6 for 8n against n).
- F2, product.rs `Scope::bind_with`: a bind that shadows a name kept the name's enumerated
  keys, so a constraint on the new name was not enumerated again. Test
  `a_constraint_on_a_shadowing_name_is_enumerated_again` (red: `[0..=10]` where the four
  listed values were expected).
- F3, preimage.rs `clamp_treap`: an end crossing past i128 panicked in `small()`;
  `clamp_treap` now returns `None` and `Pa::clamp` gives up. Test
  `a_clamp_whose_crossing_lies_past_i128_is_given_up` (red by the panic).
- F4, product.rs `conjunctions`: an arm that is a conjunction of negated constraints was
  dropped, so all names empty did not mean that no conjunction has a point. Test
  `conjunctions_keep_an_arm_of_negated_constraints`.
- F5, product.rs `Scope::atom_names`: the `class_of` shortcut of 68b13f979 skipped the
  preimage for a name bound by a term that reads another name of the scope, and
  `through_terms` then had no values to list. The shortcut is not taken for such a name. Test
  `l01_39_reduced_product::let_terms::a_congruence_test_of_a_div_by_a_constant_narrows_its_input`
  (red: `x` in `[0..=9]`).

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zedc-preimage | 85 | 471 | 188 | 198 | 32 | 38 |

Corrected counts the false claims too (comments fixed, and the five code faults above). A claim
that was both corrected and marked unproved is counted once, in the first state its row names.
Of the 471, fifteen are counted in no column: seven are in other crates (zedc-check, zedc-presburger, zed-kernel)
and were left to those crates' sections; two describe code that is gone (`lone_hole`,
`Split::joined`); five are at sites preimg1 was editing (`Tx::forget` and
`Scope::core_leaf_bound`, since proved by its 8988ec584 and 7f66f344d, and the preimage_ref.rs
chain cost) and were not edited here; one,
`initial_star_base`, states no exactness claim.

| Source | Claim | Code site | Status |
|---|---|---|---|
| 030a2d36d | Divisor and name priorities tie with chance at most (S+1)/p | divisors.rs, images.rs `prio` | Already there |
| 030a2d36d | Pieces tie with chance at most 11/2^64 | preimage.rs `prio_of` | Corrected: 11/p, p = 2^64 - 59 |
| 030a2d36d | Spans tie with chance at most 15/p | spans.rs | Already there |
| 0b8979ea4 | 33,408/592/512 constraints; ratio 14.6 to 9.0 | product.rs `Scope::enumerate` | Already there (COMPLEXITY.md) |
| 0b8979ea4 | The early pass evaluates a constraint as the main pass does | product.rs `enumerate_on`, `[]` arm | Completed |
| 0b8979ea4 | The early pass lacks the main pass's `contains_key` filter | product.rs `enumerate` | Added; Not proved, marked: a pendant name outside the base map |
| 0b8979ea4 | Every write of bottom sets the flag, except at scope making and `extend_path` | product.rs | Completed |
| 0b8979ea4 | Each replacement puts a whole scope | product.rs `narrow_linear`, `join_kept`, `narrow_node` | Completed |
| 0b8979ea4 | A root failure is reported as the main pass would report it | product.rs `enumerate` | Not proved, marked: the order of root failures |
| 0b8979ea4 | At most twice the naive work | product.rs `enumerate` | Already there |
| 0ddc1c581 | Copy on write keeps every answer | product.rs `Product`, `DerefMut` | Already there |
| 0ddc1c581 | `true` means a strict descent | product.rs `Product::reduce_domains` | Completed |
| 0ddc1c581 | `while p.reduce_domains() {}` ends | product.rs `Product::reduce_domains` | Not proved, marked: the finite set and the type listing narrow only through `reduce_congruence`, not shown idempotent; the other steps unchecked |
| 0ddc1c581 | `walk_value` gives the arms and the value | product.rs `Run::walk_value` | Already there |
| 0ddc1c581 | An `if` with two literal arms gets the transfer's value | product.rs `walk_value_at` | Completed |
| 11f5598ba | Reference walk O(d^2) | product.rs `arms_and_value_by_transfer` | Already there |
| 127a9c7a7 | `Canon::combine` height by `checked_add` | address.rs `Canon::combine` | Already there |
| 1354133f0 | Every cycle weighs at least the sum of its names' gaps | product.rs `Potential` | Completed: telescoping proof; test `holes_put_in_a_ladder_built_first_are_linear` |
| 1354133f0 | A cycle of weight 0 has every edge tied | product.rs `Potential` | Already there |
| 1354133f0 | The ends are those of the projection | product.rs `Scope::shortest` | Completed: DOIs Jeavons-Cooper 10.1016/0004-3702(95)00107-7, Shostak 10.1145/322276.322288 |
| 1354133f0 | Repair keeps the potential or finds a cycle | product.rs `Scope::repair`, `put_in` | Completed: Cotton-Maler DOI 10.1007/11814948_19 |
| 1354133f0 | Lowering q_x keeps the edges into x and lowers those out of x | product.rs `Scope::raise` | Completed: the arithmetic, the loop x to x included |
| 1354133f0 | Each key pushed is at least the key popped | product.rs `Scope::bound_pass` | Already there |
| 1354133f0 | `hole_gap` O(1) | product.rs `hole_gap` | Corrected: O(p) at the first ask (lazy `max_gap` cache, zedc-lattice interval.rs), O(log p) after a one-piece change |
| 1354133f0 | `snap_down`, `snap_up` O(log p) | product.rs `snap_down`, `snap_up` | Already there |
| 1354133f0 | Cost bound of `shortest` | product.rs `Scope::shortest` | Already there |
| 1354133f0 | Placeholders to fill | product.rs | Already there (none left) |
| 16fe26be8 | `same_framed` means the same integers | product.rs `same_framed` | Added |
| 16fe26be8 | Pure two-symbol entries kept while the mask holds | product.rs `Part::pure_two_sym` | Already there |
| 16fe26be8 | Restoring outer projections is exact | product.rs `join_preserving_outer` | Not proved, marked: the hub restored after a leaf narrows |
| 16fe26be8 | Certified chains cover the higher members | product.rs `idle_by_chain` | Already there |
| 16fe26be8 | `initial_star_base` | product.rs | No exactness claim |
| 16fe26be8 | `count_links` | product.rs | Already there |
| 16fe26be8 | Citations | product.rs header | Already there |
| 1aff02482 | `Split::joined` cost | gone | Code no longer at base |
| 1aff02482 | The due vector keeps the first of equal entries | product.rs `Block::update` | Completed |
| 1aff02482 | The closed rule reads no row of `with` | product.rs `bounds_at` | Completed; Not proved, marked: `with.1` holds no equality when `with.0` is empty |
| 1c8fda1de | `lower_gap_test` exact on the x, y marginals, O(log k) a clause | product.rs `LowerGaps`, `Scope::lower_gap_test` | Added |
| 1c8fda1de | The early return of `project` keeps the projection exact | product.rs `Scope::project` | Added (`LowerGaps` step 3) |
| 1c8fda1de | `extreme_base` keeps every integer point | product.rs `extreme_base` | Added, with test `extreme_base_and_compact_abs_keep_every_integer_point` |
| 1c8fda1de | `compact_abs` keeps the Pareto frontier | product.rs `compact_abs` | Added, with the same test |
| 1c8fda1de | `eliminate` never makes more rows | product.rs `eliminate` | Completed |
| 1c8fda1de | Pugh dark shadow DOIs | product.rs `eliminate` | Already there, see proofdoc3 |
| 1c8fda1de | Pugh citation | product.rs `parallel_rows` | Already there |
| 1c8fda1de | The union holds every point | product.rs `conjunctions` | Corrected; the case of negated constraints is fixed (F4) |
| 1c8fda1de | The idle certificate is sound | product.rs `Scope::idle` | Added |
| 1c8fda1de | The sparse shared pass equals `range` | product.rs `Scope::idle` | Already there |
| 1c8fda1de | `covers_set` exact, O(s log s + p) | product.rs `covers_set` | Already there |
| 1c8fda1de | The chain shortcut keeps idleness | product.rs `Scope::idle_by_chain` | Already there |
| 1c8fda1de | Omega citation | product.rs `project_block` | Already there |
| 1c8fda1de | Puncture exactness | product.rs `PunctureContext` | Already there |
| 1c8fda1de | `allow_multi` image of hulls | product.rs `Scope::pendant` | Added |
| 1c8fda1de | The ray certificate of `unbounded_unit` is exact | product.rs `Scope::unbounded_unit` | Added; the open case for the whole union is closed by the F4 fix |
| 1c8fda1de | All names empty | product.rs `project_by_pendants` | Already there; its open note is closed by the F4 fix |
| 1dc603590 | A join keeps the looser end | product.rs `Scope::join` | Already there |
| 1dc603590 | An end is written only after a one-name test moves it, dropped at bind and unbind | product.rs `Scope::bind` | Already there |
| 1dc603590 | Stating direct ends is sound | product.rs `Scope::stated` | Added |
| 1dc603590 | A hub held as side s needs no settling | product.rs `join_settled` | Not proved, marked |
| 1f9051e98 | A group holding one name of a conjunct never makes the part due | product.rs `PartWith`, `Split::with` | Corrected: sound, not exact; Not proved, marked: S_y with holes. The test written for it gives `x` in {0, 10} in the eager scope as in the lazy one, so the loss is not this rule's alone |
| 1f9051e98 | `reframe` finds every part whose groups change | product.rs `Block::reframe` | Added |
| 1f9051e98 | `holding_two` exact | product.rs `holding_two` | Completed |
| 1f9051e98 | `linked` O((c + v) log v) | product.rs `linked` | Corrected: O((T + v) log v) |
| 1f9051e98 | `Block::vars` O(s log k) | product.rs `Block::vars` | Already there |
| 1f9051e98 | `Split::with` O(v log v) | product.rs `Split::with` | Already there |
| 1ffeb360d | A one-sided name dropped by `eliminate` keeps the projection | product.rs `eliminate` | Already there, see proofdoc3 |
| 1ffeb360d | `recession_cone_uncertified` uses `closed_cone_ray` soundly | product.rs `Block::recession_cone_uncertified` | Already there, see proofdoc3 |
| 1ffeb360d | Leaf-only tightening narrows no other part | product.rs `leaf_only_tightened` | Completed; Not proved, marked: fact (b) when an idle certificate left a part unprojected |
| 1ffeb360d | A unary guard holding on the box entails each disjunction under its `PunctureKey` | product.rs `guard_entailed` | Added |
| 1ffeb360d | Tightening the base by the extreme corner gives the exact projection | product.rs `PunctureContext::of` | Completed |
| 1ffeb360d | The best point is at one of at most 4 breakpoints | product.rs `PunctureContext::of` | Corrected: up to six candidates, with the proof; not tested |
| 1ffeb360d | `closed_cone_ray` gives a ray in the closed cone, `None` only for {0} | product.rs `closed_cone_ray` | Added |
| 1ffeb360d | Rays mode and the base-part use are idle certificates | product.rs `HalfLineMode` | Completed |
| 1ffeb360d | Keeping the outer projected entry in a case is sound | product.rs `Scope::record` | Completed |
| 1ffeb360d | `with_ver == outer.ver` means `with` is current | product.rs `ensure_part_with` | Added |
| 25ef78dd1 | i128 skip adds edges; divisor sign; `i128::MIN` gain `None`; Q reduced; `narrow_box` | product.rs | Already there (5 claims) |
| 2673c19fa | The `projected` map has one entry a part, bounded | product.rs `Scope::projected` | Completed |
| 2673c19fa | A join keeps the entry when both sides have the same `PartWith` | product.rs `join` | Completed |
| 2673c19fa | `PartKey`, `PartWith` | product.rs | Already there |
| 268eebefe | Pearce-Kelly invariant | product.rs `Potential` | Already there |
| 268eebefe | After a move every edge goes up the order | product.rs `Potential::reorder` | Completed |
| 268eebefe | Merge shifts, size doubling | product.rs `Potential::merge` | Already there |
| 268eebefe | `bound_pass` keys monotone | product.rs `bound_pass` | Already there |
| 268eebefe | Cotton-Maler citation | product.rs `Scope::repair` | Already there (added earlier in this audit) |
| 28cfdafe3 | `ByClass::clamp` bound | preimage.rs `Bound` | Already there |
| 28cfdafe3 | `Terms::form` explicit stack, O(n) | preimage.rs `Terms::form` | Already there |
| 2df2801ba | A divisor of any size; digit cost; the same key | preimage.rs `Tr::pair_by_constant` | Already there |
| 2df2801ba | One pair a dividend and divisor is exact | preimage.rs `Tr::pair_by_constant` | Added |
| 2df2801ba | \|c\| - 1 does not overflow; c != 0 at the callers | preimage.rs `Tr::pair_by_constant` | Added |
| 2df2801ba | Open: kept powers past i64 | preimage.rs `Walk::built` | Already there |
| 2fc841e15 | A projection kept over pairs holds exactly where the callee's relation holds | preimage.rs `projected`, second path | Added: four steps (equals substituted; Euclidean q and r unique; `presburger::eliminated` exact or `None`; dropped definition rows restated by `Tr::instance`); tests `each_answer_through_a_projection_kept_over_pairs_is_the_answer_of_the_relation_whole`, `the_unit_of_seed_4236942624890658512_is_answered_as_its_bodies_read`; they cannot catch two parameters or a binding that reaches itself |
| 2fc841e15 | The same for rows `Normal::lin` cannot write | preimage.rs `projected`, `renamed` fallback | Not proved, marked: a binding that reaches itself |
| 2fc841e15 | `Tr::instance` writes the callee's pairs at the call; the recursion ends | preimage.rs `Tr::instance` | Added: induction over the order of writing; test `one_scope::answers_are_those_reading_bodies` |
| 2fc841e15 | `Projection::pairs` dividends are over pairs numbered before it | preimage.rs `Projection` field `pairs` | Corrected: the order of writing (`Normal::made`), not the numbers |
| 2fc841e15 | The value term over pairs is exact | preimage.rs `value_projected` | Added |
| 2fc841e15 | `Normal` writes each atom once | preimage.rs `Normal` | Already there |
| 2fc841e15 | One pair a dividend and divisor | preimage.rs `Tr::pair_by_constant` | Already there |
| 2fc841e15 | Cost | preimage.rs `formula_called`, `lin_called` | Already there (measured, open; LOAD-call-relation) |
| 34e5a4454 | Potential pair weights; zero cycles tied | product.rs `Potential` | Already there |
| 34e5a4454 | Equality edges tied first | product.rs `Scope::repair` | Already there |
| 34e5a4454 | `reseed` tight edges, components | product.rs `Scope::reseed` | Already there |
| 34e5a4454 | Holes in two names break shortest paths | product.rs `Scope::shortest` | Already there |
| 34e5a4454 | `lone_hole`, `project_lone` projection | gone; replaced by `Scope::by_holes` | Code no longer at base |
| 36279a9f9 | `Scoped::interface` | preimage.rs `Scoped::interface` | Already there |
| 36279a9f9 | A stale `interfaces` entry after an undo is harmless | preimage.rs `interfaces` field | Completed |
| 36279a9f9 | `Faces::met`, `congruences_once` | zedc-presburger | Other crate, not checked (two claims) |
| 364dd4a15 | Failures kept under `CallKey` | preimage.rs `Tx::forget` | Owned by preimg1 (PROOF-preimage-forget-callkey), proved by its 8988ec584; not edited here |
| 37a8466a1 | The fixed-hub solutions are closed under min and max | threshold.rs module header | Added |
| 37a8466a1 | The forward and backward loops give the least and greatest members, or `None` exactly when there is none | threshold.rs `members` | Added: steps (a) to (d) |
| 37a8466a1 | `members` O(N log N) | threshold.rs `members`, `floor` | False: `floor` cost O(P) a call; fixed (F1), test `threshold::tests::bench::many_upper_bounds_on_a_name_of_many_pieces_cost_near_linear_time`, red before, green after |
| 37a8466a1 | An `Above` or `Below` run is the limit of runs at large c; the `Val` order | threshold.rs `At` | Added: the limit lemma |
| 37a8466a1 | Coefficients >= 0: hub values p..=c*, bounds at p, the doubling ends | threshold.rs `rising` | Added: steps (1) to (5) |
| 37a8466a1 | Coefficients <= 0 by the mirror | threshold.rs `solve` | Added: w' = -w, a zero coefficient, `hub.neg` O(N + P) |
| 37a8466a1 | A mixed hub of at most 2 values is the join | threshold.rs `mixed` | Added |
| 37a8466a1 | Call sites | product.rs `project_block`, `project_threshold` | Already there |
| 3cdd34f55 | `Tx::invert_sep` narrows each input by a Minkowski difference an input: sound, precision given up | preimage.rs `Tx::invert_sep` | Added |
| 3cdd34f55 | `bind_summarized` keeps the summary only while it holds | product.rs `View::holds` | Already there |
| 3cdd34f55 | `LetPa::image` is sound through `pa_bounds` | preimage.rs `pa_bounds` | Already there |
| 3cdd34f55 | `Sep` exact division, persistent add | preimage.rs `Sep` | Already there |
| 3cdd34f55 | `Ck::narrowed_at` | zedc-check | Other crate, not checked |
| 3db038e2c | `released` is the complement of `managed` | product.rs `Block::released` | Added |
| 3db038e2c | The joint projection is narrow enough | product.rs `Block::released` | Not proved, marked |
| 3f2a92b63 | The lazy summary is made once, ends, cannot deadlock, equals the eager one | product.rs `Lazy::get` | Added |
| 3f2a92b63 | Dropping a long chain does not recurse deeply | product.rs `Basis`, `Drop` | Completed |
| 3f2a92b63 | The updated `holds` tree equals a fresh one | product.rs `View::holds` | Added |
| 3f2a92b63 | The `names` keys differ only where the orders differ | product.rs `Scope::empty_if_bottom` | Not proved, marked: other writes of `names`; join inserts |
| 3f2a92b63 | The unshaped set only grows; an empty one may skip shaping | product.rs `Block::unshaped` | Added |
| 3f2a92b63 | Names kept by every conjunct part leave each part's names unchanged | product.rs `Block::reframe` | Added |
| 3f2a92b63 | A conjunct among hubs that is not a constraint meets one part's bound | product.rs `Scope::leaf_bound_stays` | Added |
| 3f2a92b63 | `drop_part` marks every kept block holding the part | product.rs `Seen::drop_part` | Added (extra marks cost only time) |
| 3f2a92b63 | A star's block is made with a new id | product.rs `Block::update`, star check | Added; corrected: ids repeat across `narrow_node`'s revert, and the check is still sound |
| 3f2a92b63 | The walk of moved names gives exactly the users to wake | product.rs `Block::update` | Added; cost corrected to s + min(c', u + 1) items; the note at `users_cheaper_than_diff` corrected |
| 3f2a92b63 | `Seen::record` outside a case: the other parts' records stay | product.rs `Seen::record` | Added (sound); Not proved, marked: precision in (a) re-projection, (b) break paths |
| 3f2a92b63 | `Seen::record` in a block | product.rs `Seen::record` | Already there (added earlier in this audit) |
| 3fb4bb8e4 | `lin_sum` reads the terms in the order one `lin` an operand would | preimage.rs `Walk::lin_sum` | Added |
| 3fb4bb8e4 | O(k log k) on a left chain | preimage.rs `Walk::lin_sum` | Already there |
| 46322ca2c | `cone_dirs` count 2m + 20(m - 1) | product.rs `cone_dirs` | Already there |
| 46322ca2c | `holding_two` gives the keys holding two names | product.rs `holding_two` | Already there |
| 46322ca2c | `PunctureContext` equals the old inline code | product.rs `PunctureContext` | Already there (moved code) |
| 46322ca2c | `cone_certified` is sound | product.rs `Block::cone_certified` | Completed: integer steps; test `tests_on_punctured_lines_at_seed_5` (cannot catch a wrong `true` in four names) |
| 46322ca2c | `recession_cone_uncertified` is sound (hub and leaf buckets) | product.rs `Block::recession_cone_uncertified` | Added: proof by moves |
| 46322ca2c | `closed_cone_ray` fallback | product.rs `closed_cone_ray` | Already there |
| 46322ca2c | `box_face_uncertified` | product.rs `box_face_uncertified` | Already there |
| 46322ca2c | `open_cone_sector` returns an open cone or `None` | product.rs `open_cone_sector` | Added |
| 46322ca2c | `recession_shape`: closed failure arc, linear or wrapping | product.rs `recession_shape` | Added |
| 46322ca2c | `Pst::report` correct, O(log k + output) | product.rs `Pst::report` | Completed: invariants H, E, K, P; cost |
| 46322ca2c | `Pst` removal O(log k) | product.rs `Pst` | Not proved, marked: the code shows O(log^2 k) (a rotation at each level, `push_down` O(height)) |
| 46322ca2c | `Pst` insertion O(log k) | product.rs `Pst` | Added: one rotation level, argued at the site |
| 46322ca2c | Sarnak-Tarjan, McCreight citations | product.rs `Pst` | Completed: DOIs |
| 46322ca2c | `reframe` references | product.rs `Block::reframe` | Completed: DOIs Sarnak-Tarjan, Averkov-Schymura |
| 46322ca2c | `removed_cons` in a case cannot narrow a part | product.rs `Block::reframe` | Added |
| 46322ca2c | Case groups are woken before any part projects | product.rs `Scope::block` | Already there |
| 46322ca2c | `chain_least` O(e log k), the least in each place | product.rs `chain_least` | Already there |
| 46322ca2c | Skipping a chain key whose least part is managed drops no unmanaged part | product.rs `wake_case_groups` | Added |
| 46322ca2c | Chain subsumption | product.rs `project_block` | Already there, see proofdoc1, proofdoc3 |
| 46322ca2c | `Scope::record` conservative, exact when the join restores | product.rs `Scope::record` | Completed |
| 46322ca2c | The `covers_set` sweep is correct, O(s log s + p), modulus | product.rs `covers_set` | Completed: Pugh DOI, proof |
| 46322ca2c | The shared-bounds pass gives the same intervals as `range` | product.rs `Scope::idle` | Completed |
| 46322ca2c | Rockafellar, Schrijver | product.rs `wake_case_groups` | Already there (books) |
| 47dbe05b9 | The four `bitAnd` rows hold at every sign | preimage.rs `bit_and_bounds` | Completed |
| 4c163dca4 | The `Tx::forget` undo log costs O(1) an entry | preimage.rs `Tx::forget` | Owned by preimg1 (PROOF-preimage-forget-callkey), proved by its 8988ec584; not edited here |
| 526f13c51 | The exact search holds only inputs the term reads | preimage.rs `split_read` | Already there, see proofdoc3 |
| 53622f271 | References | lib.rs | Already there |
| 53622f271 | Pugh DOI at each use | product.rs (7 sites) | Completed |
| 58489bea9 | Clamp assumption | preimage.rs `Bound` | Already there |
| 5eba9712b | gcd division keeps the integer points | zedc-presburger formula.rs `Con::reduced` | Added |
| 5eba9712b | Conjuncts canonical; a false conjunct gives {false} | product.rs `distinct_conjuncts` | Already there |
| 5eba9712b | A false conjunct part makes every name empty | product.rs `project_by_pendants` | Already there |
| 5ff79522f | Every question on a read name is found | product.rs `Scope::refused_on` | Added |
| 5ff79522f | O(m log k + q log q) | product.rs `Scope::refused_on` | Corrected: O(m log k + t log t + q log k) |
| 614b9d0cf | `forest_edges` order, cost unchanged | product.rs `forest_edges` | Already there |
| 635687ff7 | `kept_in` cost by treap cuts | product.rs `kept_in` | Completed (Blelloch-Ferizovic-Sun DOI) |
| 635687ff7 | `while reduce_domains()` ends | product.rs `reduce_domains` | Already there: the open case marked for 0ddc1c581 at `Product::reduce_domains` covers it |
| 635687ff7 | The type step is skipped when `ptr_eq` | product.rs `reduce_domains_now` | Already there |
| 635687ff7 | Equal sizes mean kept equals own | product.rs `reduce_domains_now` | Already there |
| 635687ff7 | The `Top` case of `ints_listed` | zed-kernel | Other crate |
| 635687ff7 | `fills` | product.rs `fills` | Already there |
| 635687ff7 | `IntsListed` record | product.rs | Already there |
| 635687ff7 | The two tests exist | product.rs tests | Already there |
| 65bf4b76c | The `UpperBounds` split gives the bounds of the whole reading | product.rs `UpperBounds` | Completed |
| 65bf4b76c | `at_lows` O(u·a) | product.rs `UpperBounds::at_lows` | Already there |
| 65bf4b76c | Dropping xl, yl from `fresh` is correct | product.rs `UpperBounds` | Already there |
| 669d3d2d0 | Every edge that can lower a bound is read | product.rs `Scope::bound_pass` | Completed |
| 669d3d2d0 | `Seeds::changed` | product.rs `Seeds` | Already there |
| 669d3d2d0 | O((s + a + m) log n) | product.rs `Scope::shortest` | Already there |
| 68416f089 | `Scope::shortest` is the projection; Shostak, Cotton-Maler DOIs | product.rs `Scope::shortest` | Already there |
| 68416f089 | `Potential` | product.rs `Potential` | Already there |
| 68416f089 | `reseed` tradeoff | product.rs `Scope::reseed` | Already there |
| 68416f089 | `Blocks::differences_only` | zedc-presburger | Other crate, not checked |
| 68b13f979 | The congruence meet is exact, `exact` true | product.rs `Scope::atom_names`, `class_of` shortcut | Completed |
| 68b13f979 | The preimage of a congruence test over an interval is exact, with no refusal | product.rs `Scope::atom_names` | Corrected: not exact over more than two periods or unbounded (`mod_pre`, `wide`) |
| 68b13f979 | Nothing downstream loses | product.rs `Scope::atom_names`, `Scope::through_terms` | False for a name bound by a term that reads another name of the scope; fixed (F5), test `l01_39_reduced_product::let_terms::a_congruence_test_of_a_div_by_a_constant_narrows_its_input`, red before (`x` in `[0..=9]`), green after |
| 68b13f979 | The ends are recorded as the preimage's meet recorded them | product.rs `Scope::atom_names`, `Scope::direct` | Not proved, marked |
| 68b13f979 | The tests cover it | xst::s4 tests | Completed (what they cannot catch) |
| 69c4cdd32 | `let_preimage` | preimage.rs `let_preimage` | Already there |
| 69c4cdd32 | `LetPa::sum` cost and tradeoff | preimage.rs `LetPa::sum` | Already there |
| 69c4cdd32 | `LetPa::sum` correct (acyclic, topological order) | preimage.rs `LetPa::sum` | Completed |
| 69c4cdd32 | The `seen_fresh` rebase gives the caches of the naive diff | product.rs `Scope::seen_fresh` | Completed |
| 69c4cdd32 | `View::holds`, `summary` | product.rs `View::holds` | Already there |
| 6a79d26fb | Equal divisor sets have one number | divisors.rs header, `make`, `union` | Added |
| 6a79d26fb | A set number means something only under its `Tr` | divisors.rs header | Added |
| 6a79d26fb | `union` O(m log(n/m + 1)) when disjoint | divisors.rs `union` | Completed |
| 6a79d26fb | O(1) a shared subtree | divisors.rs `union` | Not proved, marked |
| 6a79d26fb | `up_from`, `down_from` give an in-order run, O(depth + found) | divisors.rs | Added |
| 6a79d26fb | `Defined::meet` nonzero equals every divisor nonzero | preimage.rs `Defined::meet` | Added |
| 6a79d26fb | `shown_nonzero` | preimage.rs | Already there (added earlier in this audit) |
| 6a79d26fb | `Defined::arm` is true only where the condition holds | preimage.rs `Defined::arm` | Added |
| 6a79d26fb | `FormulaNumbers` are equal if and only if the formulas are | preimage.rs `FormulaNumbers` | Added |
| 6a79d26fb | Calls with one key share a translation | preimage.rs `shared_call_key` | Added (relative to the next claim) |
| 6a79d26fb | The callee's translation depends only on the key | preimage.rs `shared_call_key` | Not proved, marked |
| 6a79d26fb | The `defined_called` condition is the call's | preimage.rs `defined_called` | Added |
| 6a79d26fb | On the held path `Aux(n) == at` ties the atoms | preimage.rs `defined_called` | Not proved, marked |
| 6a79d26fb | `divByZero` is the only failure of `exactly_equal` | preimage.rs | Already there (added earlier in this audit) |
| 6a79d26fb | `Walk::defined`: unkeyed calls | preimage.rs `Walk::defined` | Corrected |
| 6a79d26fb | `PRIORITIES` depth O(log n) | divisors.rs | Already there, see proofdoc3 |
| 6aeb43eff | Block walk O(d log d) | product.rs `bind_with`, `Run::walk_at` | Already there |
| 701def5c6 | Forward term square | product.rs | Already there |
| 73ed87c26 | Skipping `meet_ints(points)` changes nothing | product.rs `Product::ints_among` | Already there |
| 73ed87c26 | `is_subset` O(d log k) | product.rs `Product::ints_among` | Not proved, marked |
| 7a7417966 | `union_into` keeps the root; groups numbered by `at`; O((c + v) log v) | preimage.rs, product.rs | Already there (3 claims) |
| 7bb934574 | The one-pass `If` shortcut: the same elements, the same premises except those made under the `if` | product.rs `Run::walk_value_at`, `If` arm | Completed |
| 7c47ed27d | Invariant V | product.rs `Potential` | Already there |
| 7c47ed27d | `Scope::repair` is sound | product.rs `Scope::repair` | Completed (tests named) |
| 7c47ed27d | The bounds pass does not depend on the potential | product.rs `bound_pass` | Already there |
| 7c47ed27d | `reseed` once a tree | product.rs `Scope::reseed` | Already there |
| 83079757e | Fires at finite ends only | product.rs `Block::reframe` | Already there |
| 83079757e | Skipping a key in `spent` is sound | product.rs `Block::reframe` | Added |
| 83079757e | Each key fires once on a path | product.rs `Block::reframe` | Not proved, marked: c changed constraints reach one key, O(c·f) |
| 83079757e | `spent` union at a join | product.rs `Scope::join` | Already there |
| 84ed8e51d | Nothing in zedc-preimage matches `Prim::Tuple` or `TupleGet` by name | preimage.rs `Walk::get_key` | Corrected: `Walk::reads` matches `TupleGet` |
| 84ed8e51d | The formula is the same under the inputs `formula_by_get` binds | preimage.rs `Walk::get_key` | Completed; Not proved, marked: `reads_mod` false and `defined` true at that name |
| 84ed8e51d | A tuple callee read only as `p[k]` is read once for all callers: the arms read it only through `mentions`, `reads_mod`, `defined` | preimage.rs `Walk::get_key` | Not proved, marked: not checked arm by arm |
| 84ed8e51d | A term's number is never reused | preimage.rs `Tx::reads` | Completed |
| 84ed8e51d | The `.get` atom is held by no written name or canonical atom | preimage.rs `Tx::by_get` | Completed |
| 84ed8e51d | The check sees every occurrence of p | preimage.rs `Walk::reads` | Completed |
| 84ed8e51d | `formula_by_get` binds each parameter over every integer | preimage.rs `formula_by_get` | Already there |
| 84ed8e51d | 7.841 at 8n, control 59.131 | bench checker.rs | Already there (COMPLEXITY.md) |
| 84ed8e51d | Two spans are equal only for one place | zedc-check walk.rs `Ck::need` | Already there, see proofdoc3 |
| 84ed8e51d | Tested for every kind of use that is paired | l01_26 function_variance.rs `uses_alike_at_two_calls_give_the_errors_of_each_use_alone` | False; corrected: the comment names the kinds tested and the kinds not tested |
| 84ed8e51d | `AlikeSite::Sum` keys the receiver as written | test `sum_of_t_and_t_sum_alike` | Not proved by reading; the test asserts it |
| 84ed8e51d | The `one_scope` units cover direct, between, constants, `sum(t)` | one_scope.rs | Already there |
| 84ed8e51d | `reads_mod` is false and `defined` true at `c.get` | preimage.rs `Walk::get_key` | Completed (`reads_mod_at` gives `None`, so false; `defined_at` after `constant_at` gives `None`, so `Some(top)`); test path corrected to `l01_38_omega_test/one_scope.rs` |
| 84ed8e51d | The fixed-answer arms read no operand | preimage.rs `Walk::get_key` | Not proved, marked: not checked arm by arm |
| 875e58597 | Every `lin_at` term is an integer | preimage.rs `relations`, `lin_at` | Added |
| 875e58597 | `Scoped::relation` the same | preimage.rs | Added (covered by the above) |
| 8bf067d56 | `empties` true means the reduction empties | product.rs `Product::empties` | Added |
| 8bf067d56 | Cost Θ(k^2 log k) to near linear | product.rs `reduce_with` | Already there |
| 8c8b49f18 | O(d log^2 d) under unpatched imbl | product.rs `Scope::bind_with` | Already there |
| 8ecea2e9f | A part not reported on a valid face edge narrows no name | product.rs `box_face_uncertified` | Completed |
| 8ecea2e9f | O(log^2 k) insert, O(log k) query | product.rs `ThreshHullTrie` | Corrected: O(depth log^2 k), O(depth log k), depth <= 136 |
| 8ecea2e9f | Overmars-van Leeuwen | product.rs (3 sites) | Completed (DOI) |
| 8ecea2e9f | The report filtered by `keep` is a subset of `wake` | product.rs caller | Already there |
| 9322ec490 | The greatest and least points exist (closure under max and min) | holes.rs module doc | Added (Jeavons-Cooper DOI) |
| 9322ec490 | The ends are exact | holes.rs `greatest` | Added |
| 9322ec490 | Components come sources first | holes.rs `components` | Added (Tarjan 1972 DOI) |
| 9322ec490 | S11 cycle composition | holes.rs `Run::cycle` | Added |
| 9322ec490 | `inner == n` means one cycle | holes.rs `component` | Added |
| 9322ec490 | Contraction of tied cycles | holes.rs `component` | Added |
| 9322ec490 | A Bellman count k > n means a negative cycle | holes.rs `hull` | Added |
| 9322ec490 | A `paths` `Err` makes the caller refuse | holes.rs `paths` | Added (the `Err` is never reached after `hull`) |
| 9322ec490 | The least point is the greatest point of the negated system | holes.rs `solve` | Added |
| 9322ec490 | A refused negated run: the potential can fail | holes.rs `solve`, negated `Refused` arm | Corrected (the comment was false; the arm is never taken) |
| 9322ec490 | `big`, `inf`, `wide`, `end` keep the finite ends apart | holes.rs `solve` | Added |
| 9322ec490 | The `by_holes` ends are exact | product.rs `Scope::by_holes` | Added |
| 9322ec490 | `by_holes` O(N log N) | product.rs `Scope::by_holes` | Not proved, marked: false for a hub of k star blocks apart (`relation.mentioning`), and `holes::solve` is O(n·m) without the potential |
| 9322ec490 | k holes no longer cost Θ(k^2) | product.rs `project`, raise loop | Added (O(k log k) on a cycle with no slack; raises that all succeed are open, O7) |
| 9322ec490 | Tarjan DOI at each use | holes.rs `tie_cycles`, `components` | Already there at `tie_cycles`; added at `components` |
| 9322ec490 | Dijkstra and Bellman DOIs | holes.rs `hull`, `paths` | Already there |
| 9322ec490 | References | lib.rs | Completed: Dijkstra 1959 added with its DOI |
| 94ad265c0 | The test is true exactly where D and C | preimage.rs `Walk::defined` | Already there |
| 94ad265c0 | `exactly_equal` exact | preimage.rs `Walk::exactly_equal` | Added |
| 94ad265c0 | The `shown_nonzero` forms | preimage.rs `Defined::shown_nonzero` | Added |
| 94ad265c0 | The arm condition is true when known or the guard covers | preimage.rs `Defined::arm` | Already there |
| 94ad265c0 | O(1) beside each entry, memo | preimage.rs `Walk::defined` | Already there |
| 94ad265c0 | `Tr::definedness` | preimage.rs `Tr` | Already there |
| 97e69e64a | `Order::unmark` keeps the places equal to `place` | product.rs `Order::unmark` | Completed |
| 99fb0bc99 | For + - neg min max the bounds of `forward` are those on hulls | shared_ints.rs `monotone` | Completed: the corner argument for each operation |
| 99fb0bc99 | Each set listed once, operands first | shared_ints.rs `Ints::list` | Completed: stack order, no cycle, O(sets + links) |
| 99fb0bc99 | `join` O(1) | shared_ints.rs `Ints::join` | Already there |
| 99fb0bc99 | Dropping a chain does not recurse | shared_ints.rs `Drop for Node` | Already there |
| 99fb0bc99 | Cost O(kH) to shared pieces | shared_ints.rs `Ints` header | Already there |
| 99fb0bc99 | The map keys stay valid | preimage.rs `SharedInts` | Already there |
| 9c56b1189 | Cost O(bits of k) | preimage.rs `Walk::built` | Corrected: memory only, and only for a power of 2; time O(b log b) |
| 9c56b1189 | The value is exact | preimage.rs `Walk::built` | Added |
| 9c56b1189 | `Scoped::unbuilt` describes the last relation; `None` with the flag is refused with a message | preimage.rs `Walk::built`, `Scoped::relation`, `Scoped::new` | Added |
| 9c56b1189 | The preimage keeps a kept power unbuilt | preimage.rs `Walk::built` | Added |
| 9d757cc8c | `invert_read` gives `invert_sep`'s box; shadowed inputs over their own domains; no term missed | preimage.rs `Tx::invert_read` | Added |
| 9d757cc8c | A read's value is void unless an empty input is shadowed | preimage.rs `begin` | Added |
| 9d757cc8c | The reads of one transfer are in one scope | preimage.rs `SummaryRead::scope_ints` | Already there |
| 9d757cc8c | The landmarks use the run's own domain | preimage.rs `Tx::marks` | Already there |
| 9d757cc8c | The scope is emptied once; nothing narrows after | product.rs `Scope::empty_if_bottom` | Completed (the meet-of-bottom step marked inferred) |
| 9d757cc8c | `exclude` stops at bottom | product.rs `exclude` | Already there |
| 9dd3c3158 | A constant at an unread parameter may leave the key; the same relation | preimage.rs `Walk::claimable` | Completed; Not proved, marked: both keys refuse the same inputs |
| 9dd3c3158 | `Reads::Not` means no `Var(p)`, binder of p, or `Node::Other` | preimage.rs `Walk::reads` | Already there |
| 9dd3c3158 | The `formula_called` key and the `canonical_formula` memo do not clash | preimage.rs `claimable`, `formula_called` | Already there |
| a27a35c15 | Narrowing again is sound | product.rs `narrow_kept_again` | Completed |
| a27a35c15 | The narrowing loop ends | product.rs `narrow_kept_again` | Not proved, marked: `case_list` only shrinks |
| a27a35c15 | `dead` runs once a trigger | product.rs `KeptTests::dead` | Corrected: a join can widen ends, and the trigger fires again |
| a27a35c15 | Class-move cost | product.rs `KeptTests::dead` | Completed; Not proved, marked: unbounded ranges |
| a27a35c15 | The `x mod 2 != r` arm is exact | product.rs `KeptTests` arm | Added |
| a27a35c15 | `case_triggers` is the union of the arms' | product.rs | Already there |
| ab07cdcd9 | The `Address` order never reads the reads memo | address.rs `Address::cmp` | Added |
| ab07cdcd9 | `Address` has no `Hash` | address.rs test | Already there |
| ab07cdcd9 | Reads on deeply shared terms | zed-kernel | Other crate |
| ace60e16b | `projected` is exact as `presburger::eliminated` is exact, or `None` | preimage.rs `projected` | Completed |
| ace60e16b | Complexity tradeoff, Pugh DOI | preimage.rs `projected` | Already there |
| ace60e16b | `Walk::projection` memo | preimage.rs `Walk::projection` | Already there |
| b18332dd5 | `image_shifted` equals `image` over shifted inputs | preimage.rs `image_shifted` | Completed |
| b18332dd5 | `changed_since` lists every input whose shift may differ | preimage.rs `changed_since` | Completed |
| b18332dd5 | `Pa` equality O(1) for a shared tree, else O(p) | preimage.rs `Pa`, `eq` | Already there |
| b1ab5efcb | The route where a bottom names no name | product.rs | Already there |
| b1ab5efcb | All names empty means no conjunction has a point | product.rs `project_by_pendants` | False: `conjunctions` dropped an arm that is a conjunction of negated constraints; fixed (F4), test `conjunctions_keep_an_arm_of_negated_constraints`, red before, green after |
| b991293a4 | Citations at the use sites, the header list | product.rs | Already there |
| c1cd72c8d | Lazy chain-wake proof; `chain_left_by_idle`; subsumption | product.rs | Already there (3 claims) |
| c4c6e7e3e | A star's leaf not moved from the hubs' side loses nothing | product.rs `let leaf = b.leaf.clone()` | Completed |
| c4c6e7e3e | `Scope::due`: the leaf is unbounded away from the hubs | product.rs `Scope::due` | Already there |
| c8cac82fa | A constant past 64 bits is read at its size | preimage.rs `Walk::lin_at` | Completed |
| c8cac82fa | A divisor past 64 bits is read at its size | preimage.rs `Walk::lin_at` | Completed |
| c8cac82fa | Still open: 2^200 and divisors >= 2^127 dropped | preimage.rs `Walk::built` | Already there (closed at base) |
| ca4ccc654 | `fills` is the same with >= as with == | product.rs `fills` | Completed |
| ca4ccc654 | `kept_by_listed` exact | product.rs `Product::kept_by_listed` | Already there |
| ca4ccc654 | `ints_all_listed` gives x | product.rs `Product::ints_all_listed` | Already there |
| ca4ccc654 | The tests of the shortcuts and what they miss | product.rs `listed_shortcuts_on` | Completed |
| ce1450451 | A union of two boxes is a box only when one holds the other or they differ in one input | preimage.rs `Tx::union` | Completed: the converse (inputs i != j, u in A_i \\ B_i, w in B_j \\ A_j); conservative when a name is stored at its whole domain; test `scopes::a_union_of_boxes_is_exact_when_it_is_a_box` |
| ce1450451 | `class_of` uses Granger's congruence arithmetic | preimage.rs `class_of` | Already there (Granger 1989, DOI 10.1080/00207168908803778) |
| ce1450451 | (r mod m)(s mod n) is rs mod gcd(mn, rn, sm) | preimage.rs `class_of`, `Mul` | Completed: the expansion, Granger Prop. 4.1; test `exact::the_classes_alone_decide_a_box_of_any_size` |
| ce1450451 | x mod k is one value when k \| m, else r mod gcd(m, k) | preimage.rs `class_of`, `Mod` | Completed: the derivation; new test `tests::the_class_of_a_remainder_is_kept_modulo_the_gcd` |
| ce1450451 | The `@exact` branch and prune ends: each box is smaller | preimage.rs `branch`, `halve` | Completed |
| ce1450451 | `covers`: one or two class ranges, O(P log P), Fenwick | preimage.rs `covers` | Already there |
| ce1450451 | The witness search holds two boxes a halving | preimage.rs `witness` | Already there |
| ce1450451 | `reads_mod` false means the transfer is the same in every class | preimage.rs `reads_mod` | Not proved, marked: a `Some` that `by_class_node` returns before the `reads_mod` check of `by_class_at`, on a term reading no remainder |
| ce1450451 | The stack holds distinct lambdas | preimage.rs `Tx::enter` | Already there |
| ce1450451 | `mod_pre` gives at most 2p + 1 pieces | preimage.rs `mod_pre` | Completed: the first two lines of the comment, lost in d4894aaa0, restored from 0c89e5443; test `l01_25_preimage_catalog::random::a_remainder_inverts_to_its_first_and_last_periods_and_one_piece_between` |
| ce1450451 | `listed` lists no more than the source writes | product.rs `listed` | Completed: the missing writer, `Scope::zero_reached` roots, added |
| ce1450451 | A constraint is enumerated once a set of static-name values | product.rs `Scope::enumerated`, `enumerate` | False: a shadowing bind kept the enumerated keys, so the rewrite was skipped; fixed (F2) in `bind_with`, test `a_constraint_on_a_shadowing_name_is_enumerated_again`, red before, green after |
| ce1450451 | The `Refused` order does not depend on the meeting order | product.rs `Refused` | Completed |
| ce1450451 | `close` reads each name as the function saw it; each function is visited once | product.rs `Scope::close` | Completed; cost corrected to O((r + s) log(r + s)) |
| ce1450451 | `refuse` keeps sets that do not depend on the order | product.rs `Scope::refuse` | Completed |
| ce1450451 | A failing case costs O(k) narrowings | product.rs `assume_case` | Completed |
| ce1450451 | Joining cases without reducing each join gives the same answers | product.rs `join_cases` | Completed (soundness); Not proved, marked: equal answers (the inner join's reduction by congruence and finite set) |
| ce1450451 | `cases` is the join of `case_list`, or `None` | product.rs `Scope::cases` | Already there |
| ce1450451 | The written copy is dropped when exact for one name or a unit sum | product.rs `atom` | Completed (unit sum) |
| ce1450451 | Each part comes out of the merge once, in order | product.rs `Users::due` | Completed |
| ce1450451 | Earlier rows: `project_block` keep, `project_part`, PROOF-ints-listed-writers | product.rs | Already there, see proofdoc1, proofdoc3 |
| ce1450451 | `kept_meet` and `join_settled` do not depend on the order | product.rs `kept_meet` | Completed |
| ce1450451 | `core_leaf_bound` | product.rs `Scope::core_leaf_bound` | Owned by preimg1 (PROOF-preimage-core-leaf-bound), proved by its 7f66f344d; not edited here |
| ce1450451 | `Scoped` tradeoff: `Frame` coordinates; tests in `l01_38_omega_test::one_scope` | preimage.rs `Scoped` | Corrected: `Frame` was removed in b273d0f62; test path `bench::one_scope` |
| ce1450451 | `lams`: addressing a key while borrowed | preimage.rs `Scoped::lams` | Completed |
| ce1450451 | `Tr::truncate` undoes the definitions from the mark on | preimage.rs `Tr::truncate` | Completed |
| ce1450451 | `div_mod_by_term`: one disjunct a sign, Euclidean; n == 0 fails | preimage.rs `div_mod_by_term` | Completed |
| ce1450451 | A `Count` at depth d has d bits | preimage.rs `Count`, `joined` | Corrected: d + 1 bits |
| ce1450451 | `Terms` numbers are never reused while keyed | preimage.rs `Terms` | Completed |
| ce1450451 | `drop_fresh` drops the entries first | preimage.rs `Tx::drop_fresh` | Completed |
| ce1450451 | The landmarks are finite, so there are finitely many summaries | preimage.rs `Tx::landmarks` | Completed |
| ce1450451 | `call_back`: an input is the same interval wherever the summary is reached | preimage.rs `call_back` | Completed |
| ce1450451 | The clip hull is an operator on the ends | preimage.rs `clip_at` | Completed |
| ce1450451 | max(a, b) >= lo needs b an integer | preimage.rs `back_binary`, `Min`, `Max` | Completed |
| ce1450451 | c ^ 0 is 1 where c is an integer | preimage.rs `back_unary` | Completed |
| ce1450451 | A void box is empty in every name; nothing narrowed keeps the domains | preimage.rs `Tx::none`, `Tx::whole` | Not proved, marked: void by a read |
| ce1450451 | A first-kind `Entry` is sound where `Walk::cached` reuses it | preimage.rs `Entry`, `Walk::cached`, `Walk::made`, `Tx::enter`, `Tx::leave` | Added |
| ce1450451 | Second-kind entries are reused on every stack | preimage.rs `Entry` | Already there, see proofdoc2b |
| ce1450451 | The `ByClass` bound is within i64 | preimage.rs `Bound` | Already there, see proofdoc2b |
| ce1450451 | `split_at` halves in i128 | preimage.rs `split_at` | Completed |
| ce1450451 | `clamp_treap` visits O((m + 1) log n) nodes | preimage.rs `clamp_treap` | False: alternating 0, 10 at c = 5 visits all; corrected to O((m + s + 1) log n), s the switches |
| ce1450451 | `clamp_treap` makes only ends in range | preimage.rs `clamp_treap`, `Pa::clamp` | False: a crossing past i128 panicked in `small()`; fixed (F3), test `a_clamp_whose_crossing_lies_past_i128_is_given_up`, red before, green after |
| ce1450451 | `invert_treap` O((m + 1) log n) | preimage.rs `invert_treap` | Corrected: O((m + j + 1) log n) |
| ce1450451 | `shift` exact | preimage.rs `shift` | Completed |
| ce1450451 | `reflect` exact | preimage.rs `reflect` | Completed |
| ce1450451 | `times_pre` exact | preimage.rs `times_pre` | Completed |
| ce1450451 | `div_pre` exact | preimage.rs `div_pre` | Completed |
| ce1450451 | `split_residues` exact | preimage.rs `split_residues` | Already there |
| ce1450451 | `in_class`: the first to the last member | preimage.rs `in_class` | Completed |
| ce1450451 | `enumerate` costs at most the listed members | preimage.rs `enumerate` | Completed (the box-within-domain step inferred) |
| ce1450451 | `preimage_listed` cost | preimage.rs `preimage_listed` | Completed |
| ce1450451 | `Tx::forget` | preimage.rs `Tx::forget` | Owned by preimg1 (PROOF-preimage-forget-callkey), proved by its 8988ec584; not edited here |
| ce1450451 | After a bind nothing mentions x | product.rs `Scope::bind` | False (F2, fixed); `spent` and `refused_by` are not cleared on a shadowing bind, noted at the site |
| ce1450451 | `forward_prim` holds every value of the operation; each argument once | product.rs `forward_prim` | Added |
| ce1450451 | `@exact` is sound and keeps the point and the ends | product.rs `enumerate_exactly` | Added |
| ce1450451 | Blocks share at most one name: a forest | product.rs `project` | Added (Harary 1969; Hopcroft-Tarjan DOI 10.1145/362248.362272, written from memory and not checked) |
| ce1450451 | The bound along the tree costs each block once | product.rs `project` | Corrected: O(origins × blocks) |
| ce1450451 | The whole-block projection gives the fixed point | product.rs `project_block` | Corrected: no wider than it |
| ce1450451 | The worklist stops | product.rs `project_block` | Not proved, marked: the chain and released pushes |
| ce1450451 | `project_part` meets with the projection; congruence | product.rs `project_part`, `framed` | Already there, see proofdoc3 |
| ce1450451 | Each constraint and name is visited once | product.rs `group` | Added |
| ce1450451 | `Tree` ids are equal up to side order, height then form | product.rs `Tree`, `rank` | Added (open: atoms of equal text) |
| ce1450451 | Sides held exactly come first | product.rs `rank` | Corrected: most often; precision only |
| ce1450451 | `term_at`: the size of the subtree, log depth | product.rs `term_at` | Added; within a factor of 3 |
| ce1450451 | `plain_comparison` | product.rs `plain_comparison` | Added |
| ce1450451 | `run_closed` runs only terms shown to end | preimage_ref.rs `run_closed` | Added |
| ce1450451 | `same`: each pair once | preimage_ref.rs `same` | Added; corrected for `Other` pairs |
| ce1450451 | `Demand::holds`, `Terms::add`, `through`, `closes`, `call_back`, `meet`, `union`, `callee`, `back_compare`, `scan`, the one-axis `enumerate`, `exact_search` and `fails_in`, the `witness` and `branch` halving, `class_of` (Granger DOI), `Fwd::fails`, finite landmarks, the file used only by tests | preimage_ref.rs | Already there (18 claims; `Fwd::fails` and the landmarks inferred, the last by `git grep`) |
| ce1450451 | `mod_pre` gives at most 2p + 1 pieces | preimage_ref.rs `mod_pre` | Completed: the first two lines of the comment, lost in d4894aaa0, restored from 0c89e5443 |
| ce1450451 | `POWER_FACTORS` is kept by the frozen copy | COMPLEXITY.md row C19 | Corrected: no crate defines it any more |
| ce1450451 | Chain cost, `back_doubt` | preimage_ref.rs header | Owned by preimg1 (PROOF-preimage-ref-chain-cost); not edited |
| ce1450451 | `Scope::lazy` gives the eager product | product.rs `Scope::lazy` | Corrected: equal to it or finer; Not proved, marked: never coarser than the eager one at a leaf that is not stale; test `the_eager_join_is_as_tight_as_the_lazy_one_at_these_seeds` (six seeds) |
| ce1450451 | The joins are Karr's | product.rs `join_settled` and three other sites | Completed: Karr 1976, DOI 10.1007/BF00268497, at each |
| ce1450451 | The `Time` lattice, `Product::leq`, the C5 listing limit, the `IntsListed` writers, `reduce` ends | product.rs | Already there (5 claims; the writers see proofdoc2b, proofdoc3) |
| d8026ecb5 | The rank falls after a step | product.rs `Potential::rank_after` | Completed |
| d8026ecb5 | The `END_STEP` value | product.rs `END_STEP` | Added |
| d8026ecb5 | Block claims | zedc-presburger | Other crate |
| dcd3018d1 | The rebase equals the cache with x | product.rs `Scope::seen_fresh` | Already there |
| dcd3018d1 | The next `Order::sync` places every leaf as without the rebase | product.rs `Scope::seen_fresh` | Added |
| dcd3018d1 | A lazy scope keeps no order | product.rs `Scope::seen_fresh` | Added |
| dcd3018d1 | 16.7x to 9.0x | product.rs `Scope::seen_fresh` | Completed (benchmark named) |
| e1dd4b593 | `constant_arm` reads no name | preimage.rs `constant_arm` | Already there |
| e275c5f0b | `paths` gives `Err` on a negative reduced weight | holes.rs `paths` | Already there |
| e275c5f0b | Each name comes up once | product.rs (zed-graph `Dijkstra::lower`) | Already there |
| e275c5f0b | Dijkstra 1959 | product.rs (2 sites) | Completed (DOI) |
| e802f7960 | The pendant row is exact | product.rs `PendantRow` | Completed |
| e802f7960 | `extend_pendant` checks two values | product.rs `extend_pendant` | Completed |
| e802f7960 | Freuder citation | product.rs `extend_pendant` | Added (pointer to the DOI in the header) |
| e802f7960 | `moved_since` | product.rs | Already there |
| e8981310f | 0 <= r <= \|c\| - 1 formed without overflow; Euclidean | preimage.rs `Tr::pair_by_constant` | Added |
| e8981310f | The precondition c != 0 is met by every caller | preimage.rs `Tr::pair_by_constant`, `Walk::lin_at`, `Tr::instance` | Added |
| eaef33ced | A read gives the same answer whatever earlier read it starts from | images.rs `updated` | Completed |
| eaef33ced | `Scope::holds` cost | product.rs `Scope::holds` | Already there |
| eaef33ced | A test costs its summary's inputs | product.rs | Already there |
| eaef33ced | The treap shape comes from the names alone | images.rs | Already there |
| ebd6faee5 | At most t roots | product.rs `Scope::zero_reached` | Corrected: 2t - 1 (Descartes) |
| ebd6faee5 | Cucker-Koiran-Smale | product.rs `Scope::zero_reached` | Completed (DOI) |
| ebd6faee5 | Meeting x with the roots removes no state where t is 0 | product.rs `Scope::zero_reached` | Added |
| ebd6faee5 | Sound under overflow; no double evaluation | product.rs `enumerate_on` | Already there |
| f060dbed1 | The `Staircase` AVL tree keeps `max_a`, height, size | product.rs `Staircase` | Added (Adelson-Velsky and Landis 1962, which has no DOI) |
| f060dbed1 | `lower_x`, `upper_y`: one path, O(log k) | product.rs `Staircase::lower_x`, `upper_y` | Added |
| f060dbed1 | The `upper_dec` descent is exact | product.rs `Staircase::upper_dec` | Added |
| f060dbed1 | `cover_staircase` exact | product.rs `Block::cover_staircase` | Added, with test `staircase_queries_and_plane_cones_match_a_scan` |
| f060dbed1 | The common-ray bound | product.rs `ray_high` | Completed (sound, not exact) |
| f060dbed1 | `in_cone` membership | product.rs `in_cone` | Added (Carathéodory, DOI 10.1007/BF01449883, checked at Crossref), with the same test |
| f060dbed1 | `Turn` order | product.rs `Turn` | Already there |
| f060dbed1 | Carathéodory | product.rs `bounds_at` | Completed (DOI) |
| f060dbed1 | The `UpperBounds` cache is current | product.rs `UpperBounds` | Added |
| f0bde0d35 | The `Walk::made` entry; the scan entry | preimage.rs `Entry` | Already there (2 claims) |
| f0bde0d35 | `put_in` sides | product.rs `put_in` | Already there |
| f0bde0d35 | The `project_block` skip | product.rs `project_block` | Already there (its open case was marked before this audit) |
| fe51539ce | `start_from(begun)` keeping the ints answers as a fresh start does | preimage.rs `preimage_in` | Added; Not proved, marked: the `SummaryRead` reads in `begin` are pure |
| fe51539ce | A `pows` entry is a function of its key | preimage.rs `pows`, `SharedInts.pows` | Not proved, marked: false for a `Word::Kept` exponent equal in value to a `Big` one (precision and order only) |
| fe51539ce | The `order_with_literal` rewrite | preimage.rs | Added |
| fe51539ce | 10.4x bytes | COMPLEXITY.md | Already there (a measurement, not rerun) |
| fe51539ce | The test path in the complexity comments | preimage.rs (3 sites) | Corrected to `l01_25_preimage_catalog::bench::powers`, and at COMPLEXITY.md rows S30, S47, PA-bind-cost |
| fffe13699 | A split keeps the heap order | preimage.rs `split_at`, `split_around` | Added, with test `a_split_keeps_the_heap_order` |
| fffe13699 | Split cost O(depth) | preimage.rs `split_around` | Added |

No code claim: 0e8df04e7, 23c5a37c0, 9e3cc1480.

Not read:

## proofdoc4c: zedc-types, and `Sig::standing_twice`

Base commit 1915d2375. Each entry of /home/luke/Work/wt/proofdoc4-lists/c.txt was read in full:
its message, its zedc-types diff, and every comment line it added, then the code that relies on
each claim as it stands on main, at its current site (all in `crates/zedc-types/src/ty.rs`
unless named). Where a later commit rewrote a claim, the claim checked is the one the code now
rests on. The open sub-cases already marked at their sites under row PROOF-sweep-zedc-types
(`Cx::compared`, the binding that no search shrinks while it lives, recall under `b`, `admits`
facts F2 and F3, the equal-signature step of `fits_in`, the ceilings) were found still marked;
none is closed here.

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zedc-types | 129 | 107 | 94 | 9 | 3 | 1 |

The three marked unproved: a034e80cd's claim is false for a written difference (red probe
below; the fix is in zedc-check, row FAIL-ty-diff-function-rows); 27e8e2464's "equal
signatures have equal digests" is open where one keeps a compact forward (row
FAIL-map-chain-d6-digest owes the test); dd8b42f68's "the shape of its own is the first of its
bucket" is open where an earlier shape has the same class places and keys (row
PROOF-types-own-shape-first-of-bucket). The one corrected is 305ad0293's `standing_twice`
claim, made false by 9ff4e6673, which landed while this section was being merged. A written
variable that a failed test narrows lost its name in what the test leaves, so the print
showed `_` there. It is fixed at `Scope::open`, with a red and then green test (row below).

| Source | Claim | Code site | Status |
|---|---|---|---|
| 2143bead4 | `Same` keys only by root address; `RunRenames`; `some_value`; run marks keyed by ROOT | `Same`, `RunRenames`, `some_value`, `RunMark`/`sig_walk` | Already there |
| 1233ccd22 | pins of variables bound alone keep the rule of one shape | `struct Bound` (trie proof, left-out proof, lists proof) | Already there; "nothing shrinks a binding while a search lives" stays Not proved at the site (PROOF-sweep-zedc-types) |
| f3970ac46 | the arrow merge of `Domains` is exact where either arrow is | `Domains` arrow merge, before `at: HashMap<&[Ty], usize>` | Completed: each step, and tests l01_23 `judgments::a_meet_of_an_exact_and_a_partial_arrow_over_one_domain_is_one_arrow`, l01_26 `fits::a_partial_arrow_keeps_its_value_type_apart_from_its_lookup_type`, with what they cannot catch |
| f2297a652 | `left_out_by_vars`; union pins; trie cost O((k + 1) log n); no place twice on a path | `left_out_by_vars`, `Bound`, `BoundTrie`, `Bound::pin` | Already there |
| 13e376cb7 | a pinned shape that leaves the member out is passed, not failed | `Bound` left-out proof | Already there; pins holding while bindings grow is the open sub-case above |
| 5d9bad32b | `Cx::open` renames apart; ceilings needed only where a tuple holds a value; `Binds::of_arrow` | `Cx::open`, `Binds::of_arrow` (Pierce and Turner, DOI at the site) | Already there |
| 09f77b6f3 | `held_as_is` holds out of written order; `unbound_carriers` | `held_as_is`, `unbound_carriers` | Already there |
| 37dad5731 | `fits_read` answers alike wherever a reading is met: its key holds every input | `fits_read`, before `read_key` | Completed: each other field of `Cx` classed; the `compared` step rests on the assumption at `Cx::compared` (PROOF-sweep-zedc-types); tests l01_22 `kinds::function_types_nested_whose_inner_levels_hold_the_outer_variable_fit` and control |
| ced805157 | `Cx::read` of a payload, O(n) with its memo | `Cx::read` | Already there |
| 08e6206a4 | `Domains::meet` and its outside union | `Domains::meet`, `Pairs::fns_met` | Already there (proofdoc3c) |
| 18cc11692 | a partial arrow prints `->?` and reads back partial | `Sig::parts` | Already there |
| 475e582ff | test cases built by hand, each derived | `mod tests` | Already there |
| 62c5ace4b | `sub_near` skips the form where the other side holds a function of its own variable | `sub_near` | Completed: tests l01_22 `kinds::a_generic_function_type_holding_a_function_of_its_variable_fits_itself_renamed`, l01_26 `bounds::functions_in_tuples_whose_bounded_variables_only_they_hold_fit_under_other_names`, and that a missed case is a false no, never a false yes |
| 64eede4ce | `Domains::within` keeps the unknown; `Domains::plain` | `Domains::plain` (PROOF-domains-plain-meet) | Already there |
| 76705768a | a list type is refused in a bound check | `kernel_form` | Already there |
| 7da6fc4a6 | a printed clause binds only written variables | `Scope::written` | Already there |
| e7180d4db | `fits_in` reads only held entries of `bound_fns` | `Cx::bound_in_fns`, `held_reading` | Already there |
| 69844cb07 | the printer hoists a clause inside a key or bound union | `PrintAt::Member`, `Print::Closes` | Already there |
| 7fc4ac500 | skipping parts with no variable keeps the counts | `Shared::closed` | Already there |
| 922be74e7 | `PrintAt::Listed` places | `PrintAt::Any` (the claim reversed by the grammar later) | Already there |
| afbdffe42 | a derivation's text lifts repeated tuples, linear text | `defs::lift` | Already there |
| d4ce3868b | `closed_left_out` changes no verdict or binding | `Searched::closed_left_out`, `some_value` | Already there |
| f26b8a8e5 | `permitted` skips only where `instances` gives `None` from its walk | `permitted` | Already there |
| e70d43315 | `every_arrow_fits`, `answers_within`, the least instance | `answers_within`, `instances`, `instance_within` (rewritten proofs) | Already there |
| 2981d4645 | `Domains::plain` by the branches of `Ty::meet` | `Domains::plain` | Already there |
| 83920e1d6 | `some_value` gives a rational zero | `some_value` | Already there |
| 83a509ae3 | `Dense` ranks and intervals | `Dense` | Already there |
| a98079c36 | a message names each scope of a comparison | `Scope::of_comparison` | Already there |
| b59ca2ae8 | parentheses only where precedence needs them | `PrintAt` | Already there |
| bcb0fcb93 | a power's base holds no int | `NeedKind::Power` | Already there |
| c38724eb5 | `var_steps` order; `must_decode` cases | `sig_walk`, `Replacer::must_decode` | Already there |
| d20413aae | an equal signature fits; `equal_fits` | `fits_in`, `equal_fits` | Already there; the reflexivity step stays Not proved at `fits_in` (PROOF-sweep-zedc-types) |
| f0bde0d35 | each assumption the comparison makes | the ASSUME sites listed above | Already there (each proved since or still marked) |
| fed6e73e4 | forward naming; step order | `sig_walk`, `RunMark` | Already there |
| feeafc10c | printer parentheses | `PrintAt` | Already there |
| 0e50ec37c | uses alike kept by kind | `Need::alike` | Already there |
| 2ec6b9418 | `fits_alone` (1)-(4); `answers_within` sound | `fits_alone`, `answers_within` | Already there |
| 3189a1922 | domains that fit have equal keys; a collision only merges parts | `domain_key` | Completed: tests l01_23 `judgments::functions_at_one_place_whose_tuples_all_meet_are_decided`, l01_22 `kinds::functions_unlike_on_both_sides_at_one_place_are_refused`, with what they cannot catch |
| 405650a5b | `VarFacts::add_to` cost; SipHash | `VarFacts::add_to` (DOI 10.1007/978-3-642-34931-7_28) | Already there |
| 7028f23a2 | a forward's stored summary is valid only at the ranks and span it was built at; the exit-rank guard | `FwdNeed`, `r10_hash::cached_fwd_summary`, `build_sig_needs_summary` | Already there |
| 7d9e078c0 | a refused check is not stated as a proved failure | `kernel_form` (kernel_type.rs) | Already there |
| a3cee3606 | the rest of a payload shape is the exact difference; cost; some inputs need w^k shapes | `Comparing::shape_rest`, `parts`, `widest` | Already there (proof since put on kernel types, PROOF-diff-exact-skip) |
| b623e6fe0 | a place whose near pairs are no more than its functions is decided in O(n) | `star_pairs` (PROOF-star-pairs, every step), `met_at`, `Forms` | Already there |
| c1e5a82e3 | unbounded own variables bound through a function are checked as bounded ones; `Mark` equality; two guards | `Binds`, `Cx::held_own`, `Mark` | Already there |
| e5a605a6e | a joined row costs a bounded factor of the rows written out | `Comparing::row_in` | Already there (stated as measured, not proved; a cost, not a verdict) |
| e82d77ca9 | `closed_form` gives what `fits_read` gives | `Comparing::closed_form` | Already there |
| 1c2b6a270 | a need field added later fails to compile in `debug_sig` | `debug_sig` (destructured with no `..`) | Already there |
| 305ad0293 | `Sig::standing_twice` counts as the printer counts, so the two never differ | `Sig::standing_twice`, `Scope::open` | Corrected. The steps are at the site: the same three steps of the print, and why neither difference changes a count (closed parts are passed over; the outer and kept names of `Sig::text_around`). The claim was false after 9ff4e6673. That commit prints a written variable by its kept name, as a `VarSlot::Name`, and `Scope::open` joined a `Narrow` leftover only to a free variable. So `g(positional r: T) = r else 0` printed `T -> _` where Display prints `T -> 0 \| T`, and `standing_twice` named a leftover that the print wrote `_`. Red test: zedc-types `what_a_failed_test_leaves_of_a_kept_variable_prints_by_its_written_name`, which printed `T -> _`. Fix: `Scope::open` gives the leftover the kept name, after every free-to-free join. Green: the same test, plus l01_29 `fresh_names::what_else_leaves_of_a_written_variable_prints_by_its_written_name` |
| 4ef43bf6c | nine guards no input reaches | `Replace::made_held`, `Need::site_mut`, `fits_alone`, `Bound::pin` | Already there but `Bound::pin`: completed (both callers pass one bucket's slice and its own `exact`; the slice rises) |
| 400b14585 | `VarBits` cost | `VarBits` | Already there; the O(n²) case of every bit is named at the site (row CK-every-bit) |
| 6e2e39396 | a remap's rank | `NeedKind::Remap`; proof at zedc-check `Ck::remap_of` | Already there |
| 701def5c6 | equal written ranges have one text | `impl Hash for WrittenRange` | Completed: the text is a field `Eq` compares, so equal values hash alike |
| 875e58597 | `Sig::int_params` and its callers' filter | `Sig::int_params` | Already there |
| 9778881e0 | `Forms::level` of nested marks | `Forms::level` | Already there |
| a034e80cd | a row with no kernel type is kept whole: the rest may hold more, never less | `Comparing::diff`, the shape case | Marked Not proved: false for a written `a \ b`. Probe (not committed): `((int) -> int, #a \| #b) \ ((int) -> int, #a)` reads as `((int) -> int, #a \| #b)`, and `f(p: that type) = p; g() = f(p: (inc, #a))` is accepted. Sound for `is not`. Fix in zedc-check (`TypeKind::Diff`, check/mod.rs), proof7's crate: row FAIL-ty-diff-function-rows |
| a619cb307 | `permitted` skips only where `instances` would | `permitted` | Already there |
| a670bd1cb | `first_seen` decode condition; `held_read_places` | `Sig::first_seen`, `Settle::must_decode` | Already there |
| a9443c314 | `found_in_nest` stop; `held_foreign_fn` | `found_in_nest`, `FwdNeed::held_foreign_fn` | Already there |
| af8174807 | a call need's key holds no site | `NeedKind::Call` | Already there (the reach proof is zedc-check's) |
| d20f8009e | a written range alias prints and reads back | `WrittenRange::new` | Already there |
| 01063a0ca | `mutable_key_type` allowed: the key never changes | each `allow` site | Already there |
| 03e64b6da | a guard's test, with control | `mod tests` | Already there |
| 148a42eb4 | entries and folds in the order met | `NeedKind::Entries`, `NeedKind::Fold` | Already there |
| 1d9291f72 | `accepts` skip; `fns_met` apart | `accepts`, `Domains::witness` | Already there (proofdoc3c) |
| 22dd31a36 | `Absorb` reads as the reader reads | `Absorb`, `may_absorb` | Already there |
| 27e8e2464 | `Domains` proofs; equal signatures have equal digests | `Domains::*`; `Pairs::fns_met`, `r10_hash` constants | `Domains` already there; the digest claim marked Not proved at both sites (row FAIL-map-chain-d6-digest): where it fails, time is lost, never a function |
| 2e3a7b0a4 | nine cited results | each site | Already there, each with its DOI |
| 2f99f5283 | `Same` by union-find and addresses | `Same` | Already there |
| 47be53825 | `fixed_payload` table | `fixed_payload` | Already there; the flaw that `subtype` ignores `Sig::data` is reported as row FAIL-types-subtype-ignores-family |
| 493ff031b | `Cx` on an explicit stack keeps order and short-circuits | `Cx` | Already there |
| 6704ae0ff | `FwdNeed` hash reads a subset of what `==` reads | `impl Hash for FwdNeed`, `emit_bounds` | Already there |
| 69526a75a | a call need's site | `NeedKind::Call::site` | Already there |
| 7a54c17f9 | `recall` checks the one refusal state | `Comparing::recall` | Already there; rests on the assumption at `Cx::compared` (PROOF-sweep-zedc-types) |
| 807260a3b | the binding's index behind an `Arc` | `impl Piece` tradeoff | Already there |
| 811505cca | the encoder memo by address and context | `r10_hash::Encoder::memoized` | Already there |
| 92a76ed89 | rows searched fewer than twice the rows held | `Comparing::row_in`, `split_at` | Already there; the measured part is named at the site (PERF-types-joined-split-several-differing) |
| 9b35c8ab0 | a morphism type reads back to its arrows | `Sig::morphism` | Completed: test l01_22 `kinds::morphism_types_print_as_written_and_read_back`, and what it cannot catch |
| 9e8f139f1 | a shared part gets one definition; linear text | `write_parts`, `Morphism` | Already there |
| b991293a4 | Tarjan and van Leeuwen | `Same`, `Walk` | Already there, with the DOI |
| c289ffeca | fresh names skip program names | `Scope` (proof at zed-kernel `fresh_name`) | Already there |
| cbc003938 | `meets_here`, `near_shapes`, `Pairs::alone` | those functions | Already there |
| d2a97b1f9 | kept memos read alike in every state | `fits_alone`, `fns_outside` | Already there |
| e6dfb6877 | a union key or bound is parenthesized | `PrintAt::Key`, `PrintAt::Bound` | Already there |
| eb6e0ad7f | the benchmark named | `Comparing::row_in` | Already there |
| 06d1dc49c | `CallPath` Debug outermost first; `debug_cut` | `impl Debug for CallPath`, `debug_cut` | Already there |
| 08d2feda8 | `closed_form` sound | `Comparing::closed_form`, `held_reading` | Already there |
| 0de5b565c | `fits_read` names never made again | `fits_read` | Already there |
| 205591658 | `Entries` cost | `NeedKind::Entries` | Already there |
| 2d09ac322 | `Same` room argument | `Same`, `Lazy`, `Above` | Already there |
| 3248fbce2 | merged forms keep the verdict | merged forms in `Forms` | Already there (proved since, every step) |
| 3fd923c4a | `BindMap` costs | `BindMap` | Already there |
| 453066558 | `fits_written` memo; `Forms::fns` | `fits_written`, `Forms::fns`, `held_reading` | Already there |
| 47681f229 | `Dense` tradeoff | `Dense` | Already there |
| 47b73bd8f | merged forms | `Forms` | Already there |
| 620307b4c | a variable standing twice prints by name | `Walk`, `Plan`, `write_parts` | Already there |
| 65a9230a8 | the read key holds the masks of outer names | test with control `NO_KEY_MASKS` | Already there |
| 78f2ca158 | an answer true kept under the binding it gave | `Comparing::keep` | Already there |
| 81f3d8487 | drop, facts and digest without recursion | `drop_types`, `Sig::held_without` | Already there |
| 929e7e04a | free-variable weights joined smaller into larger | `r10_hash::FreeWeights`, `walk_vars`, `VarFacts::of` | Completed: the book's ISBN (no DOI) at the citation |
| 9b5729b46 | `closed_binds` may stop at the first other variable | `closed_binds` | Already there |
| a16eb1e6e | runs name each internal result once | `FwdNeed::materialize_result_tys` | Already there |
| d18e52a0a | a mark is named after `String` | `Ty::write_vars` | Completed: every name `fresh_name` gives begins with `T` to `W` (`Names::nth`) |
| dd8b42f68 | the shape of its own holds `first` and not `second`, and is the first of its bucket | `own_shape`, `unchosen_text` | The first by construction; the second marked Not proved where an earlier shape has the same class places and keys (row PROOF-types-own-shape-first-of-bucket) |
| df3fa8308 | eight guards no input reaches | each guard | Already there |
| e2ef08f39 | held names carried; `first_seen` premise | `VarFacts`, `Sig::first_seen`, `Need` | Already there |
| ea2effe91 | the parameter names a call may write | `Sig::callable_names` | Already there |
| fb5f2416f | five cost fixes | `Comparing::diff`, `Piece`, `ArrowIndex::keep_missing`, `atoms` | Already there |

No code claim: bbae90d38 (the claim is zedc-check's), 0d87a73ca, 25ef78dd1, 2b3e706f1,
444cdb15b (the claim is tested in zed-kernel), 995200322, 9d877b65c, d493d34a3 (the check is
zedc-check's), 65f995fee, 6945f496b, 6ebe63b42, ee79685e4, 67dd99e3a, 718e9ecda (message
wording), 8412a61b4 and b5317f47c (tests only), 29bf6b297, 3e597380e, 4abfd2ae1 (docs; the
checks are zedc-check's), bd7d5aa55 (the crate split: comments moved unchanged, read under the
entries that wrote them), c1dfb00f7 (coverage tests), d6a84bc7c (the naming is zedc-check's).

Not read:

## proofdoc4d: zedc-check

The 153 zedc-check entries of /home/luke/Work/wt/proofdoc4-lists/d.txt, in list order. Each
entry's message and its whole zedc-check diff were read, then each claim's site as it stands
on main; the sites were read on origin/main 1915d2375 and rechecked at each merge's rebase.
Claims in other crates are listed and not counted; they belong to the helper of that crate.

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zedc-check | 153 | 243 | 179 | 42 | 9 | 13 |

| Source | Claim | Code site | Status |
|---|---|---|---|
| 516e1324a | `note_fn_uses` costs O(p), plus O(s) only at a call that gives a declared function; naive O(s²) | walk.rs `Ck::note_fn_uses` | already there |
| 516e1324a | `order_by_names` is O(p) and gives a bijection or none | walk.rs `order_by_names` | already there |
| 516e1324a | the adapter put at a forwarded argument is right because each other need passes it into a slot of the same order | walk.rs `Ck::reorder_forwarded` | corrected (FAIL-reorder-union-slot): the search for a slot of the other order went through `only_fn` and skipped a slot that holds the function type beside an atom or another member, `((y: int, x: int) -> int) \| #none`; `pass(g) = app2(f: g) + app3(k: g)` was accepted and ran `re` with its arguments swapped (33 for 24). Now every function member of every slot is searched. Test `function_variance::a_reordered_function_the_generic_body_also_passes_into_a_union_slot_is_refused`, red before, green after |
| 516e1324a | a need that reaches `coerce_forwarded` at a forwarded place passes into a slot of the written order, or into another type that takes no function of another order | walk.rs `Ck::coerce_forwarded` doc | corrected: false for the union slot above before the fix; the doc now states the case and the fix |
| 549d0d033 | `written_at`: O(n) per message with the memo; naive O(n²) | mod.rs `Ck::written_at` | already there |
| 549d0d033 | the walk ends on every input | mod.rs `Ck::written_at` | argument added: each pass breaks or inserts into `passed`, a set of the unit's spans; tests named, and what they cannot catch |
| 5767fe37a | a bare decimal is listed at three carriers, at most three runs | walk.rs, bare-decimal listing | already there |
| 59fe136e7 | `read_image` complexity | walk.rs `Ck::read_image` | already there (COMPLEXITY.md WALK-read-image-n2) |
| 5decb7fcc | `widening` reads a listed type by casting each value and back, as `cast_loses` does | mod.rs `widening` | already there |
| 5decb7fcc | cost: one cast and its inverse per listed value (C66) | mod.rs `widening` | already there |
| 5decb7fcc | an infinity cast back to `rat` is `#overflow`, so never equal | mod.rs `float_exact` | already there |
| 5decb7fcc | the carrier rule keeps no value a listed cast changes | mod.rs test `a_cast_keeps_a_listed_value_exactly_where_its_carrier_rule_says` | already there |
| 61be98168 | `declared_again` is O(step) | mod.rs `declared_again` | already there |
| 628d33f6d | `kernel_build` sizes a build by the kernel's own `room` asks | mod.rs `kernel_build` | already there |
| 628d33f6d | `too_large_build`: what builds, the kernel's size, what is left open | walk.rs `Ck::too_large_build` | already there |
| 628d33f6d | spans nest or are disjoint, so two range reads find an inner operation; O((b + r) log r) | walk.rs `Ck::powers_over_main_limit` | already there |
| 635687ff7 | the `f64` part's listing gates `call_values` with no change of result | walk.rs `Ck::unfixed_calls` | already there |
| 65f995fee | `fresh`: O(L + k), k at most one more than the number of names | walk.rs `fresh` | argument added: the names tried are distinct, each failed one is in `words`, `\|words\| <= L`; test named |
| 65f995fee | a width is tested by both bounds | walk.rs `test_repair` | already there |
| 6e2e39396 | every chain of remap needs is finite | walk.rs `Ck::remap_of` | argument completed: W is read from the remap alone and every need of a chain is of one remap (`remap_need`, `remap_goes_on`, `remap_met` key it by `e.span`), so W is one number along a chain |
| 6e2e39396 | `remap_goes_on` cost | walk.rs `Ck::remap_goes_on` | already there |
| 701def5c6 | `x * x` of one binder is never below 0 | mod.rs, `square` in `Ck::known` | already there |
| 701def5c6 | a parameter's range is read in O(1) beyond its bounds | mod.rs, the range reading | already there |
| 7d0cc8d9f | `x ^ k` has at least `k(L - 1) + 1` bits per built part | walk.rs `Ck::too_large_power` | already there |
| 809f95c53 | `ints_here`: soundness and O(1) table operations per node | walk.rs `Ck::ints_here` | already there |
| 84f080d6b | `Within::Bytes` is increasing, never empty | walk.rs `Within` | already there |
| 84f080d6b | `holds_none_of`: one search, O(log p) | walk.rs `Within::holds_none_of` | already there |
| 86322e10b | `main_limits` O(statements + arguments); `through_names` ends by a visited set | limits.rs | already there |
| 924583b1b | the refusals of part reads are placed once, at the expression read | walk.rs `Ck::read_in_scope_at` | already there |
| 9aff48777 | each argument read once per arrow, O(A v log v), "A is at most five for an operator" | walk.rs `Ck::fewest` | corrected: `ORDER` and `EQUAL` past its refused tuples have six arrows (zed-kernel term.rs `Prim::arrows`; `prim_arrows` drops refused ones); comment now says six, with the count per list |
| 9e3cc1480 | `read_here` gives the same read at every place | walk.rs `Ck::read_here` | already there |
| 9e4acde1f | the cast takes `rat`, `f64`, `f32` out of an unresolved class; O(log N) find | walk.rs `Ck::int_not_whole` | already there |
| a034e80cd | `subtracted_args` cost, built only for a printed message | mod.rs `Ck::subtracted_args` | already there |
| a55b75fd8 | decoded copies keep their addresses: no function walked twice is replaced, no address reused | mod.rs `Ck::r10_decode_fwd_needs` | argument completed: tests named; no test makes the allocator reuse an address, so (ii) rests on the argument |
| a55b75fd8 | `keep` holds every copy to the end of `finished_with` | mod.rs `r10_promote_open_fwds`, `finished_with` | already there |
| a55b75fd8 | the `FinishMemo::held` memo is sound | mod.rs `FinishMemo` | already there |
| a55b75fd8 | a copy of a held function's runs met after the first is named as the first | mod.rs `NameOrder::dups` | argument completed: no known program and no test reach a second copy; said at the site |
| a670bd1cb | the needs `guarded_needs` drops, and its cost | walk.rs `Ck::guarded_needs` | already there |
| a670bd1cb | `permuted_sig` cost and `inv` | walk.rs `permuted_sig` | already there |
| a670bd1cb | `needs_in_order` gives the order the needs were met in | walk.rs `needs_in_order` | already there |
| a670bd1cb | the `#4-outer` guard no test reaches, O(1) | walk/r10_forward.rs | already there |
| a9443c314 | an exit some need is on is a receiver at the next level | mod.rs, building `on_vars` | argument completed: test named |
| a9443c314 | `held_foreign_fn` agrees with `Sig::holds_only_own_variables` | probe.rs field doc | argument completed: test named; the agreement is zedc-types' `FwdNeed::held_foreign_fn` |
| af6a5a696 | the `Value::Big` arm of the unread-call message, O(the text) | walk.rs, the unread-call message | already there |
| af8174807 | the `site_free` key | mod.rs `site_free` | already there |
| af8174807 | calls alike are one need: same shape and class, so the same functions reach both | walk.rs `Ck::need` | argument completed: test and benchmark named |
| af8174807 | `settle_calls` is O(p) | walk.rs `Ck::settle_calls` | already there |
| af8174807 | whether a call is placed does not depend on the order the calls are met in | walk.rs `Ck::record_call` doc | corrected: the marks may depend on the order (see 69526a75a below); what runs does not, with the argument at `unaligned` |
| b18332dd5 | the tree of images updated from an earlier read equals a fresh one | walk.rs `Ck::read_image` | argument added: each input a leaf reads is among the keys reset, and the fold is associative; tests named, and that none compares the two trees |
| b3469579a | a checked merge's operand is not checked again; the record is keyed by failures | walk.rs `Ck::merged_data` | already there |
| b3469579a | a record left from an earlier walk with equal failures is skipped soundly | walk.rs `Ck::merged_data` | marked "Not proved here": rests on the errors of a check not being undone outside a trial, not traced |
| b7edc27fd | a divisor that cancels is zero wherever it is reached | walk.rs `Ck::cancels` | argument added: one binding per name, every coefficient and the constant 0, exact ints and rats; `div` and `mod` take ints, `/` of f64 is excluded by `zero_divisor`; tests named |
| b7edc27fd | `always_fails_word` | walk.rs `Ck::always_fails_word` | already there |
| bfe7e7956 | `with_entries`, `entry_classes`: the parameter takes only those entries | walk.rs | already there |
| d20f8009e | `two_pow_text`, `alias_range` O(1), the alias arm of `Denote`, `read_part` refuses an alias name | walk.rs; read.rs `read_part` | already there |
| e7b12dd2e | a new spelling compared with one entry tells one spelling from two | mod.rs `Ck::spells` | corrected: the doc said "the first", the code reads the least span; the step "while not mixed every spelling is the same" added; `forget_printed` runs at every record, not only at a change |
| ee79685e4 | `bound_through_fn` is sound | walk.rs `bound_through_fn` | already there |
| ee79685e4 | a section and a plain value at one bracket are rejected in either order | walk.rs `Ck::bracket_meaning` | argument added: both orders and the both-at-once case traced to `bracket_met_both` and `bracket_both_here`; test named |
| ee79685e4 | the group key is deferred | walk.rs, `group` | already there |
| 01063a0ca | `mutable_key_type` allowed: no key's hash or equality can change while it is held | walk.rs `heads`, `known`; walk/r10_forward.rs, two maps | argument completed at all four sites: where each fact is established in zedc-types ty.rs |
| 03a4f95f2 | `key_bounds` is linear in the arrows | walk/fp_ops.rs `Ck::key_bounds` | already there |
| 03a4f95f2 | a zip whose four key bounds are one set has sure keys | walk/fp_ops.rs `Ck::zip_end` | argument added: `L ⊆ U` for each side gives the chain of inclusions; tests named |
| 03a4f95f2 | `list_concat_end`'s recursion ends | walk/fp_ops.rs | already there |
| 0f6b67903 | literal repairs come before casts, O(r) | walk.rs `Ck::repairs` | already there |
| 0f6b67903 | a literal fix adds at most three trials | walk.rs `apart` | already there |
| 148a42eb4 | an `Entries` need is bound at each call before any use recorded after it | walk.rs `Ck::word_entries` | argument completed: the word calls it through `lambda_entries` before `word_fn` checks the lambda; that `replay` keeps the order is inferred, not traced; tests named |
| 148a42eb4 | `word_entries`' recursion ends | walk.rs `Ck::word_entries` | corrected: the reason given ("built before the class is resolved") does not hold; replaced by the invariant at `Class::resolved` |
| 148a42eb4 | a fold by an unknown function on a known family: no `fsig` only where `f_class` holds | walk.rs | already there |
| 1cdb4bf0e | a class of carriers alone cannot be called | walk.rs, `call_value` | argument completed: `mask & OTHER == 0` means no function, by `Class::mask` and `mask_of`; tests named |
| 1cdb4bf0e | `gives_within` restricts a class piece through `piece_into` | walk.rs `Ck::gives_within` | argument completed: its doc had been merged into `gives_made`'s; moved back, the closed-`r` limit stated, tests named |
| 2cccffee8 | `top_f64_leaves` reads each display part once, O(size) | walk.rs `top_f64_leaves` | argument completed: tests and benchmark named |
| 2cccffee8 | `retyped` gives the type a body gives | walk.rs `retyped` | argument completed: same tests |
| 2cccffee8 | `display_ty` is O(n) unions | walk.rs `display_ty` | already there |
| 47be53825 | `fixed_payload_fits`: the fit rules and the open cases | walk.rs `Ck::fixed_payload_fits` | argument completed: tests named |
| 47be53825 | a checked merge is not checked again | walk.rs `Ck::merged_data` | already there (as b3469579a) |
| 4d3221711 | the sweep of unchecked uses | walk.rs `Ck::sweep_unchecked_uses` | already there |
| 55045d490 | `handled` is Tarjan's, O(B + R + E) | mod.rs `handled` | already there (doi:10.1137/0201010) |
| 57434d47b | `++` takes only `Ranks` | walk/fp_ops.rs `list_concat_end`, `ranks_count` | already there |
| 57434d47b | `zip` gives the stronger tag | walk/fp_ops.rs | already there |
| 578bbc92d | the tokens `part_tokens` moves are those a new lex gives | read.rs `part_tokens` | argument completed: the "Not proved" names its row PROOF-part-tokens-slice-lex |
| 5af4b2f2a | a block that exports nothing writes when a statement writes | ports.rs `silent_tail` | already there |
| 5db8eb317 | a literal's own join does not ask; a merged class is asked if either was | mod.rs `Class::asked` | already there |
| 5db8eb317 | `resolve_top_parts` reads each class once | walk.rs `Ck::resolve_top_parts` | already there |
| 5ff79522f | `refused_notes` is O(m log k) and writes nothing in a trial | walk.rs `Ck::refused_notes` | already there |
| 5ff79522f | `asked_at` is O(log p) | mod.rs `asked_where` | already there |
| 60ce2dad4 | `Into` and `Data` uses are met by the mask; the joined use stays an obligation | walk.rs `Ck::resolve_top_parts` | already there |
| 60ce2dad4 | the sweep's list of discharges | walk.rs `Ck::sweep_unchecked_uses` doc | corrected: it listed a join in `merge` as a discharge, which was removed |
| 60ce2dad4 | the checker builds no arrow from a tuple the table marks `refused` | mod.rs `prim_arrows` | argument added: the field's contract quoted, and what it costs a call |
| 61299315a | F189 is O(c + l), and why the float formats | walk.rs | already there |
| 64d244789 | cycles and names with no value | walk.rs | already there |
| 6704ae0ff | `r10_finish_fwd_callee` is a post-order on an explicit stack, O(V + E) | walk/r10_forward.rs | already there |
| 6704ae0ff | the split memo with its `listed` set | walk/r10_forward.rs | already there |
| 6704ae0ff | `key_watchers`, `open_watchers`, `deferred_open` are O(1) amortized | probe.rs | already there |
| 6704ae0ff | B3, the key with the lambda cleared | walk/r10_forward.rs | already there |
| 6704ae0ff | B1, the cfg setters | probe.rs | already there |
| 6704ae0ff | the ranges of `closed_internal_ranges` are disjoint, which the lookup needs | probe.rs field doc | argument added: each range is one block `reserve_ids_o1` reserves, and `logical_len` never decreases in sparse mode; no test checks it directly |
| 67dd99e3a | a remap need is made only by `remap_need`, which inserts into `remap_exprs` first | walk.rs, `remap_met` | already there |
| 67dd99e3a | the plan read from the text is the same at every type | walk/remap.rs `remap_text_plan` | already there |
| 67dd99e3a | the witness is merged | walk/remap.rs `remap_alone` | already there |
| 67dd99e3a | `group_of`'s recursion ends | walk.rs `Ck::group_of` | corrected: the reason given does not hold; replaced by the invariant at `Class::resolved` |
| 67dd99e3a | the writers of `Class::resolved` keep its invariant | mod.rs `Class::resolved` | argument completed: the copy of writer (3) in walk/r10_forward.rs named |
| 6817d8ebc | `Arms::longer` is O(log s) | arms.rs | already there |
| 6817d8ebc | soundness without monotonicity | arms.rs | already there |
| 6817d8ebc | `Carried::around` visits each test once | arms.rs | already there |
| 69526a75a | `unaligned` is O(p + a) | walk.rs `unaligned` | already there |
| 69526a75a | `record_call` is undo-logged | walk.rs `Ck::record_call` | already there |
| 69526a75a | "the conditions are equalities, so each function that agrees with the first agrees with every other" | walk.rs `unaligned` doc | corrected: a side with no default agrees with any default, so the marks depend on the order; why the result does not, at the site; test `functions_with_and_without_a_default_curried_alike_run_in_either_order` (three orders, and the refusal); that the later call is checked against each function of the union is inferred |
| 727dae146 | `carriers_only` | walk.rs | already there |
| 727dae146 | masks only narrow | mod.rs `Class::mask` | already there |
| 74d26e990 | each literal is read once in `follow_param` | walk.rs `Ck::follow_param` | argument completed: by the `binder` guard, which the pass always sets; the old reason holds only through `fix_bound` |
| 74d26e990 | a class `fix_bound` leaves as it is never meets two parameters | walk.rs `Ck::follow_param` | marked "Not proved" at the site |
| 7a7417966 | which root survives a union does not change a mark read | mod.rs `VarSets` | already there |
| 7d0d766ad | `mentions` enters blocks; blocking.rs skips a block that returned | walk/remap.rs; blocking.rs | already there |
| 7dc27aa9e | `#emptySeparator` exactly where the separator's type holds `""` | walk/fp_ops.rs `strings_end` | already there |
| 7dc27aa9e | each test reads the separator's type once | walk/fp_ops.rs | already there |
| 81e1bb50f | two remaps with one computed key go through the same steps | walk/remap.rs `remap_alike` | already there |
| 81e1bb50f | the tables copied are all a computed key records | mod.rs `copy_alike_keys` | already there |
| 81e1bb50f | the kept keys never overlap, so one lookup finds the key | mod.rs `copy_alike_keys` | argument completed: the two levels of one remap, by spans of distinct expressions |
| 84e65bf61 | the domains are nested, so the smallest need per binder decides each call | walk.rs `Ck::floor_on` | already there |
| 84e65bf61 | the chain's notes are built only for an error | walk.rs `Ck::floors_at` | already there |
| 8d9f4f9d2 | no later use narrows a class of a comparison's side | walk.rs `Ck::equal_classes` | already there |
| 8d9f4f9d2 | O(size of the sides + literals) per comparison | walk.rs `Ck::equal_classes` | already there |
| 981ec6c8a | `bitAnd`, `bitOr`, `bitXor` as values need only `int[0..]` per operand | mod.rs `bit_word_value` | already there |
| 981ec6c8a | O(1) per use of the name | walk.rs | already there |
| 9ad186cfe | no expression names an output port | walk.rs | already there |
| 9b35c8ab0 | `L .. U -> V` as `(L) -> V`, `(U) -> V \| #notFound`; rule 6 takes the first | mod.rs `Denote` | already there |
| 9b35c8ab0 | what `takes_all` answers | mod.rs `Ck::takes_all` | argument added: by the set, by the bound's `OTHER`, or yes for the unknown, another variable or a class |
| 9b35c8ab0 | a class parameter whose carriers hold no atom never stands before an arrow that takes the atoms | mod.rs `Ck::takes_all` | marked "Not proved" at the site |
| 9e8f139f1 | `parse_type` is linear in the text | read.rs `parse_type` | already there |
| b3de801c3 | a literal lies in another `if` iff the largest end among those starting at or before it reaches past it | mod.rs `Ck::resolve` | already there |
| b3de801c3 | each operation is read at each carrier at most once | walk.rs `lit_fit` | already there |
| b3de801c3 | a dead branch is noted alone | walk.rs | already there |
| b48d21bcd | a key past 64 bits misses a dense family with `#outOfBounds` | walk.rs | argument completed: tests named |
| b991293a4 | a find in `Class` is O(log N): union by rank, no path compression | mod.rs `find` | already there |
| ba11fed9c | the spans of a class's operations do not overlap | mod.rs `copied_values` | already there |
| ba11fed9c | `text_rat` computes no power but of 0, 1 and -1 | mod.rs `rat_step`, `text_rat` | already there |
| ba11fed9c | `word_unoffered` is O(size of the operand), once per application | walk.rs | already there |
| bad0d2e86 | `chunkBy` runs are ranked from 0 with every rank present, so the keys are `0 ..< n` | walk/fp_ops.rs `chunk_by` | already there (rests on zedc-elab `chunk_by_term`, whose run counter starts at 0 and adds 1 per change) |
| bd3c630e0 | a default's value at every call lies in the recorded ints | walk.rs `note_default_ints` | argument completed: tests in l01_24 default_ints named, and the `match` default they cannot reach (`a_default_from_a_match_is_not_compiled_yet`, row TEST-default-ints-match) |
| bd3c630e0 | a default literal sum takes its carrier | walk.rs `infer_defaults` | already there (FAIL-default-literal-sum-carrier, test default_carrier.rs) |
| bea44d4a5 | an operand below `2^w`, or a `k` below `w`, at the smallest width stays so at every width | walk.rs `bit_domains` | already there |
| bea44d4a5 | `whole_bytes`: every value is a multiple of 8 | mod.rs `whole_bytes` | already there |
| c289ffeca | chosen names clash with no name the program binds or the message writes | mod.rs `lay_out`; walk.rs `check_with`, `check_given` (`ProgramNames::hold`) | already there |
| d11373afd | `StmtKind::Initial` never reaches the walk | walk.rs `unreachable!` | already there (the resolver's refusal was not traced again) |
| d59b4756e | a repair never narrows a type | walk.rs `wrapped`, `cast_side`, the `r.atoms() == held.atoms()` filters | already there |
| d83518eb5 | `carriers_only` refuses a destructured random family | walk.rs | already there (FAIL-random-f64-destructured-family and its test) |
| d9d8729bb | `merged_data` cost | walk.rs `merged_data` | already there |
| da0895a4f | `f64_operands` is O(\|e\|); `open_lits` is one walk | mod.rs | already there |
| df8cea00b | an operation in `lit_open` has all the operations inside it there too, so the walk stops at the first; each operation is walked once | walk.rs `lit_open_within` | argument completed: the insert sites (a `+ - * / ^` that is a `/`, has an open operand or a bare decimal; unary `-` of an open operand), the removal in `lit_takes` and why it keeps the invariant, the two scaling tests |
| e2e0e0612 | `seconds` rounds up to a whole nanosecond | limits.rs `seconds` | argument added: the three cases, with the ceiling identity |
| e2e0e0612 | `seconds` gives `None` only where `r` is not above 0 or passes `u64::MAX` ns | limits.rs `seconds` | corrected (false): `r` was built first, so a tiny or huge kept power, `1r / 2 ^ (2^40)`, was rejected as "not a time the run can have ... above 0" although above 0. Now placed against both ends by `Rat::try_cmp` before anything is built. Test `main_limits::a_time_of_a_power_too_large_to_build_is_judged_by_its_size` (l01_29_diagnostics), red before, green after |
| e2e0e0612 | an in-range time is built | limits.rs `seconds` | marked unproved: a value between the ends whose two sides are powers too large to build (`3 ^ a / 2 ^ b`), and a value agreeing with an end in more bits than the memory allows, can still give `TooLarge`; both depend on the machine |
| ebd6faee5 | the cost of the root search (Cucker, Koiran and Smale, doi:10.1006/jsco.1998.0242) | walk.rs | already there (the rest is zed-kernel's) |
| ef56f8c84 | `data_checked`: a class keeps the data need it had | mod.rs `Class::data_checked` | marked unproved: the union `c.data \|= data`, `Undo::DataChecked` and the one clearing in generalize `take` are named, with the test `a_trial_undone_after_the_memo_entered_a_row_leaves_no_memo`; open: a row that outlives its level |
| ef56f8c84 | `clean`: a class's level only goes down | mod.rs `Class::clean` | argument added: a class takes a level once (`Ck::class`, the `need` class, a forced forward's class), `Ck::lower` only lowers, the union keeps the minimum, `Undo::Class` and `Undo::Clean` roll back together; benches and `ZEDC_CHECK_CLEAN` named; a row holding a forward's class before it is forced is named as not traced |
| ef56f8c84 | `lasting` | mod.rs | already there |
| f240a5462 | `folds` has at most seven entries per check | mod.rs `folds` | argument completed: the six numeric and other carriers and none, the tests in l08_02_remaps::empty, and that they cannot catch REDUCE-generic-identity-rest |
| f240a5462 | `finish` gives one identity or one per call | mod.rs `Ck::finish` | already there |
| f38d90beb | a repair word has at most five arrows; the cost of `split` | walk.rs `wrapped` | already there |
| f6c6b1f99 | an arm with no export | ports.rs | already there (with its test and the open case of a block that leaves early) |
| f79ee52bf | an ordering arrow takes two values of one carrier | walk.rs `both_cast` | already there |
| f8f4ddabb | the uses of a need are only added to, so a cache keyed by length is current | walk.rs `need_arg_via` | argument completed: the only writes are the push in `Ck::need` and the prepend `combined` in mod.rs, neither removes a use, no `Undo` touches them; bench `many_calls_of_a_body_with_many_named_calls_scale` |
| f923d44b9 | `String(b)` of a `bool` never reads as a number | walk.rs | already there |
| fffe13699 | the `fit_lambda` name map is O(p) | walk.rs `fit_lambda` | already there |
| 019b3519b | nested `if`s cost O(n), O(a + l) | walk.rs | already there |
| 06d1dc49c | `Names` by induction on depth, BLAKE3 at 128 bits, keyed by address, the `deep_flat` memo | r10_tests/expected.rs | already there (test code) |
| 0b05cc8cf | `ints_as_int` reads parameters soundly, O(q·s) | walk.rs | already there |
| 0cbb40ab4 | the search cost of `arrow_lambda_twice` | mod.rs | already there |
| 19514ef8c | `translate_called` translates each definition once in post order on an explicit stack | walk.rs `translate_called` | already there |
| 205591658 | a key needs a decidable equality; a key holding a function is a type error | walk.rs, the comment above `keys_at` | already there |
| 205591658 | `s.es[i + 1]` is in range for a map display | walk.rs `display_step` | argument added: a map's parts are built in key, value pairs, so their count is even and `i + 1` is a value's index |
| 205591658 | the `in` key is checked as data | walk.rs | already there |
| 2059d260b | two functions that differ in names share their names by place | walk.rs `name_by_place` | already there |
| 2059d260b | content-equal scopes get the same scope class | walk.rs `Ck::compute` | already there (the memo assumption is marked at zedc-presburger `project_each`) |
| 2059d260b | implicit calls with equal printed arguments mean one value | walk.rs | already there (marked "Assumption, not proved (ASSUME-documented)") |
| 2059d260b | `read_here` reads only its scope | walk.rs `read_here` | already there |
| 256d0fc5d | `ungrouped` costs O(t) | mod.rs `ungrouped` | already there |
| 256d0fc5d | taking off the parentheses inside a cast keeps the meaning | mod.rs `ungrouped` | argument added: an argument is a whole expression and the cast takes the place the group held; tests `ungrouped_takes_off_only_the_parentheses_around_the_whole_code` and `casts::a_cast_takes_the_place_of_the_parentheses_around_its_operand` named |
| 29bf6b297 | `dense_read` | walk.rs `dense_read` | already there |
| 29bf6b297 | `out_of_bounds`: the `#notFound` a key brings is passed by, a stored one stays | walk.rs `out_of_bounds` | already there |
| 30b46ffdb | `holds_power` costs the size of `e` | mod.rs `holds_power` | already there |
| 30b46ffdb | `written_alone` costs the length of `at` and the edits | mod.rs `written_alone` | already there |
| 30b46ffdb | a fix with a `^` names the operation, not the value | mod.rs `folded`, `binder_holds` | already there (LIT-power-expression named) |
| 30b46ffdb | a compared tuple's pairs with a `^` are named as written | mod.rs `compared_holds` | already there |
| 35f48821c | an asked class prints as its carriers, O(1) per class | mod.rs `as_literals` | already there |
| 3b7276f38 | each read of `main::files` outside `main` is one O(1) lookup | blocking.rs | already there |
| 3b7276f38 | the outside reads join `main`'s port after the walk | blocking.rs `Walk::outside`, `facts` | already there |
| 3e597380e | the chain of remap needs below a key level ends | walk.rs `remap_of` | already there (PROOF-remap-chain-termination) |
| 3e597380e | `remap_level` visits each class once | walk/remap.rs `remap_level` | already there |
| 3e597380e | `remap_pending` is one walk of the key levels | walk/remap.rs `remap_pending` | already there |
| 47681f229 | default ints cost O(1) expected per default | walk.rs `note_default_ints` | already there |
| 47f742016 | the wrapper's citations and cost | coprime.rs `base_of` | already there (both DOIs) |
| 480291d0e | output ports cost O(P + A + U) by one backward search | ports.rs | already there |
| 4abfd2ae1 | a key accepted at a call lies in the parameter's ranges, which the remap's witness assumes | walk.rs `keys_at` | marked unproved: the listed ints and a declared parameter passed on (the subset check `written_ints(m).is_subset(&written_ints(r))`, `family` taken on) are argued; open: from the floor of a parameter of no declared type to each outer call, covered for one level by `a_parameter_of_no_declared_type_takes_the_need_on_to_its_calls` |
| 4abfd2ae1 | `keys_at` costs O(arrows · listed keys · ranges) | walk.rs `keys_at` | already there |
| 4abfd2ae1 | the key's range bounds every key the remap meets | walk/remap.rs `key_span` | already there (rests on `keys_at`) |
| 4abfd2ae1 | `family` is final when the signature's need is built | walk.rs `Frame::InferEnd` | already there |
| 4ce8104bb | `silent_tail` visits each node on the paths once | ports.rs `silent_tail` | already there |
| 4e55a11ba | copies are removed by the full order, since two texts at one span can alternate | mod.rs, walk.rs | already there |
| 51ae6534c | `main_tails` visits each expression once | mod.rs `main_tails` | already there |
| 51ae6534c | each `int` `main` gives is checked in `0..=255` | walk.rs `status_in_range` | already there |
| 5ccb21f3f | each tuple component is read once | walk.rs | already there |
| 5ccb21f3f | O(A v log v), A at most five for an operator | walk.rs | already there (the five is zed-kernel's table and sets only the constant) |
| 61590f5c5 | a rejection with k fixes costs k + 1 checks, at most 3 per argument | walk.rs `fixes_checked` | marked unproved: the counts of `menu` (one fix for an int literal or bare decimal, two for a suffixed decimal) and `unfixed` (one per carrier) are written; open: one argument taking fixes from both, and the other menus of a recorded construct |
| 61590f5c5 | groups of fixes join smaller into larger, a fix moves O(log fixes) times | mod.rs, walk.rs | already there |
| 61590f5c5 | `lit_fit` reads each operation once per carrier, at three carriers at most | walk.rs `lit_fit` | corrected: four numeric carriers (`int`, `rat`, `f32`, `f64`); still O(1) |
| 61590f5c5 | a comparison offers at most six casts and one component per index | walk.rs | already there |
| 61590f5c5 | `Found::id` finds an error by binary search | walk.rs | already there |
| 620307b4c | a capitalized name written twice is a variable of the outermost signature, O(n) | read.rs | already there |
| 620307b4c | free names are the scheme's variables | mod.rs `denoted_free` | already there |
| 650ec1e0a | `a ..` is one interval with no upper end | walk.rs | already there |
| 65fe79c41 | O(A p) tests | walk.rs | already there |
| 65fe79c41 | a refusal claims nothing about the types | walk.rs, `Ty::refused` | already there |
| 695a25e74 | each int a call gives lies in the callee's hull | mod.rs `call_hull` | already there |
| 695a25e74 | a default's value at every call lies in its recorded ints | walk.rs `note_default_ints` | already there |
| 6a1038700 | a function not in the set cannot block | mod.rs, blocking.rs | already there |
| 788205304 | the left operand of `mod 2^k`, k at most 64, is computed wrapping, so nothing in it is reported | widen.rs module doc | marked unproved: the ring-map argument that the wrapped value gives the exact residue is added; open: that the build computes the operand wrapping (not traced) |
| 7b5ff433f | a term is translated once per (span, reading); d nested tests cost O(d) | walk.rs `Ck::term_for`; arms.rs `Reading` | already there |
| 7efc39992 | proof forest: merges of N classes cost O(N log N) | mod.rs `Ck::link_proof` | argument added: the doubling step, that `Ck::merge` passes the smaller side, the DOI; test path corrected to `bench::scaling` |
| 7efc39992 | `merges_between`: the walks meet at the nearest common ancestor, at most twice the path | mod.rs `Ck::merges_between` | argument added: why the first meeting is the nearest common ancestor, the bound 2·max(dx, dy) + 2 |
| 7efc39992 | the citation of Nieuwenhuis and Oliveras | mod.rs `Class::proof` | already there |
| 807ba2009 | a step past `FOLD_ASK_BITS` fails whatever the machine | walk.rs `fixed_value`; mod.rs `FOLD_ASK_BITS` | already there |
| 81f3d8487 | `Denote::ty` takes time linear in the size of `t`, with no stack growth | mod.rs `Denote::ty` | corrected: the steps are linear; each `Make` and `And` costs its union, difference, meet or signature, which is not O(1); stack tests named |
| 8824fb555 | `text_literal`: the cost of reading a literal as text | walk.rs `Ck::text_literal`; mod.rs `Lit::as_text` | already there (O(d) for a decimal int, the kernel's conversion otherwise, COMPLEXITY K81; tests named) |
| 893f60ac7 | `Drop for Part`: every drop returns after one level | mod.rs `impl Drop for Part` | argument completed: the fact it rests on (no `Rc` held twice inside one tree) and where it holds; the test and what it cannot catch |
| a16eb1e6e | `left` holds no compact forward after a call | walk.rs, the `debug_assert!` after `replay` | argument completed: where each step is shown (`r10_try_admit`, `replay`, `FwdNeed::decode_from`) |
| a16eb1e6e | F5-1: proof (b) needs no premise on what the checker gives | walk/r10_forward.rs | already there |
| a7dba5382 | `recovered` finds exactly the atoms the rows determine | walk/remap.rs `recovered` | already there |
| a7dba5382 | `family` sound but not tight; `flat_map_end`, `group_end` costs | walk/remap.rs | already there |
| af7540d08 | each catalog entry of `injective` recovers the key | walk/remap.rs `injective` | argument added: the residue, Euclidean (zed-kernel eval.rs `Prim::IntDiv`, `Prim::Mod`), packing (equal strides pass only after a span of 0) and affine cases; tests named |
| b3c21a87e | `fixed_value` reads each expression once, finite with cycles | walk.rs `Ck::fixed_value` | argument completed: tests named |
| b5444f558 | `sum` leaves `_` as a chain of `+` does | walk.rs `sum` | already there |
| b6b810dec | the fold reads of `Ck::finish` cost O(u + e + s + r) | mod.rs `Ck::finish` | already there |
| b6b810dec | `same_use`: every check of the first use is one of the second | mod.rs `same_use` | already there |
| b6b810dec | `saw_uses` costs O(d) | walk.rs `Ck::saw_uses` | already there |
| b6b810dec | a function passed to an escaping call takes none of its identities | mod.rs `Info::escaping_calls` | already there |
| e2ef08f39 | proof (b) part (B) holds for held names | walk/r10_forward.rs | already there |
| e2ef08f39 | `finished_with` is linear | mod.rs `Ck::finished_with` | already there |
| e2ef08f39 | no name of a program holds a NUL, so no other variable is cut | mod.rs `r10_internal_name` | argument completed: the identifier rule (DESIGN.md L1.2) cited; the checker's own names named as not traced |
| e36d97342 | two passes over the links join every class to a carrier class it leads to or comes from | walk.rs `Ck::join_narrowed` | marked unproved: the links are sorted by the tested class's root, which may be older than the class; the chain k0 → k1 → k2 → k3 that two passes miss is written at the site (row FAIL-join-narrowed-root-order proposed) |
| e8755d8a1 | `value_parts` linear; `unfixed_args` O(a + n + l)·α | mod.rs, walk.rs | already there |
| fbb2b68aa | `fold_level` and `sum_method` end | walk.rs; mod.rs `Class::resolved` | already there |
| fbb2b68aa | `group_of` ends because a class is resolved to a type built before it | walk.rs `Ck::group_of` | corrected in 16ab7836d: it ends after one step because a root's type holds no variable (the invariant at `Class::resolved`) |

Other crates, not counted: 5767fe37a and 9aff48777 the arrows of `Prim::arrows` (zed-kernel),
635687ff7 treap set bounds (zed-kernel) and `Product::meet_type` (zedc-preimage), 809f95c53
`forward_pow` (zedc-lattice), 86322e10b run-time limits (zed-rt, zed-native), a034e80cd
`Comparing::diff` (zedc-types), a670bd1cb `Sig::first_seen`, `WantRange`, `holds_internal`
and `Settle::must_decode` (zedc-types), a9443c314 `emit_bounds` and `emit_sig` (zedc-types),
af6a5a696 `built` and `TooLarge` (zed-kernel), b18332dd5 the treap of images (zedc-preimage,
doi:10.1007/BF01940876 at the site), b7edc27fd `Ty::meets`, which `key_outside` rests on
(zedc-types), d20f8009e `fixed_width::name` (zedc-syntax), 47be53825 the `fixed_payload`
table (zedc-types), 578bbc92d the keyword lookup (zedc-syntax), 5ff79522f `refused_on`
(zedc-preimage), 64d244789 `order_around_cycles` (zedc-resolve), 6704ae0ff B4 and B5, the
`Hash` (zedc-types), 7a7417966 `UnionFind` (zed-graph), 7d0d766ad no kernel name is `$k@j`
(zed-kernel), 7dc27aa9e `split` on an empty separator (zed-kernel), 97beabefa
`Sig::standing_twice`, moved to zedc-types, 9e8f139f1 `Type::surfaces_by_name` (zedc-types),
b991293a4 `zed_graph::UnionFind` (zed-graph), c289ffeca `fresh_name` (zed-kernel), 1a19cae20
the projection memo (zedc-presburger, marked there), 205591658 the walk of `Entries`
(zedc-types), 2059d260b `project_each` (zedc-presburger), 47f742016 the coprime base
(zed-kernel `num::coprime`), 480291d0e `Frame::Push` (zedc-elab), 4ce8104bb the parser rule
(zedc-syntax), 5a5ef9670 `forward_pow` (zedc-lattice), 81f3d8487 `Drop for Sig`,
`Sig::facts`, `Sig::digest` (zedc-types), 929e7e04a `FreeWeights` (zedc-types) and `m61::inv`
(zed-numtheory), d18e52a0a `cmp_values` as a total order (zed-kernel), e2ef08f39
`Sig::first_seen`, `FwdNeed::held_names_of` and others (zedc-types), eaef33ced `Scope::holds`
(zedc-preimage), fbb2b68aa `Elab::generic_sum` (zedc-elab), ebd6faee5 poly/roots.rs
(zed-kernel).

Claims gone from main, not counted: af8174807 `call_records` (replaced by `record_call`
marking the call placed), 275d434e7 `env_config` and `ZED_DISABLE_D` (E was removed in
f83194447). ee79685e4 `fold_dir_end`'s round bound was not read again: it is known false
(FAIL-fold-rotating-tuple-rounds). b6b810dec `type_holds_needs` is no longer in zedc-check.

No code claim: b2ba71b22 (test helpers), c50a8965b (message texts), fe770de11 (in zedc-check
only a test helper calls `zed_numtheory::is_prime`), 275d434e7 (its one claim is gone),
97beabefa (its one claim moved to zedc-types), 718e9ecda (message text), e6dfb6877,
009e52933, 00a508032 (behavior only), 131d7f7fd (the brackets doc states a definition),
3fd923c4a (a loop rewritten as `update_each`), 929e7e04a (in zedc-check only tests),
aea083d67, c8fa18353 (message wording), dd8b42f68 (repair wording), eb156f28d (`Info::ints`
is a definition).

Not read:

## proofdoc4e: zedc-presburger, last 90 entries

The list is `proofdoc4-lists/e.txt`, 90 entries numbered 1 to 90 in its order. Part 1, entries
1 to 20 and the six review ids R4-CLAUDE-2, R4-CLAUDE-3, R4-CLAUDE-8, I4.3, I4.15 and I4.11,
base commit 8c9dd3cbd; part 2, entries 21 to 59, base commit 8f447824e; part 3, entries 60
to 90, base commit 0a78446c2. merge_check: part 1, 2851 pieces and 6 of `tests/full`, none
failed; part 2 the same. For each entry the
whole message and the whole diff under `crates/zedc-presburger` were read, and each claim was
checked at the code that relies on it on main today, except where "Not read" below says
otherwise.

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zedc-presburger, part 1 | 20 | 44 | 31 | 6 | 0 | 5 |
| zedc-presburger, part 2 | 39 | 42 | 35 | 4 | 0 | 2 |
| zedc-presburger, part 3 | 31 | 44 | 34 | 7 | 0 | 3 |

Of the 44, two are counted in no column, since the code they described is gone: the sieve
proof of fe770de11 (moved to `zed-numtheory` `least_prime_factors`, complete there, and no
longer used by this crate) and R4-CLAUDE-8 (a comment on the top-level split that round 5
removed). The review ids are counted with the entries, I4.15 and I4.11 under 2df2801ba.

Two claims were false, each in a comment that the code relied on:
- `extend/residues.rs` `over` merged the bounds of `a - m q` and `a + m q` within one
  disjunct, since it took `m = |kb / ka|` and dropped the sign: `x - 4q >= 0 && x + 4q <= 1`
  was read as the window `0..=1`, though it holds at every `x`, so `read` emptied a face that
  has a point. The fix keeps one signed ratio per disjunct, and the module's proof now says
  why that is exact. Red, then green: `extend::residues::tests::
  bounds_of_a_plus_and_a_minus_one_quotient_are_no_window` (empty at `x = 2` before the fix).
- `MapHull::compose` said composition is associative. It is for `lo`, `hi` and `step`, not
  for the `exact` flag: `({0, 10} + {0, 1}) + {0..9}` is inexact and `{0, 10} + ({0, 1} +
  {0..9})` exact, both `{0..20}`. Each `true` is sound, so the bracketing of `HullProduct`
  changes only which method answers, not the answer. The doc is corrected, and the test
  `r5_hull_tests::map_hull_values_compose_associatively_and_the_exact_flag_does_not` pins
  both halves.

In part 3, one claim was false and one proof had an open case, both in `extend.rs`
`same_divisions`:
- The doc said a second division `t + c == m q + r` sets `q` to `q' + (c' - c) / m`; the code,
  its test and the arithmetic give `q' + (c - c') / m`. The sign is corrected and the proof
  (the remainders of one value are one) written at the site.
- The doc said "Exact, since the rows stay", but the caller substitutes the map into the rows.
  That is exact when no atom the map sends to is itself set; nothing kept a quotient that a
  first division sends to from being set by a later one (`w + 7 == 7 f + s` setting `f` while
  `x + 2 == 2 h + r` set `h` to `f + 1`). No wrong answer was found from it, but the proof did
  not hold. The fix skips such a division (`targets`), and the proof of exactness is now at
  the site. Red, then green: `extend::tests::one_substitution_sets_no_atom_it_sends_to` (the
  map set `Aux(1)` and sent `Aux(7)` to it before the fix).

| Source | Claim | Code site | Status |
|---|---|---|---|
| fe770de11 | the sieve of least prime factors is exact | `zed-numtheory` `least_prime_factors` | no longer relied on here |
| fe770de11 | `plane::bezout` gives the old signed Euclid's cofactors | `zed-numtheory` tests `bezout_cofactors_give_the_gcd_and_are_the_least` | already there |
| fe770de11 | `combine_crt_pair` gcd costs what `wide_gcd` did | `modular.rs` `combine_crt_pair`, `Int::gcd` | already there |
| 04ebcda96 | `fails_past_lid` is exact | `two_pins.rs` 741-748 | already there |
| 04ebcda96 | the split of the rays is exact (`rb >= 0` implied) | `two_pins.rs` 750-797 | already there |
| 04ebcda96 | `TANGENT_SIZES` predict a ratio of 10.0 | `two_pins` tests 4489-4498 | already there |
| 134e107ca | `search_by_halves` marks failed only disjuncts with no point | `search_by_halves`, the marking loop | completed: proof at the site |
| 134e107ca | `learn`'s `rest` is the disjunction without `d` | `learn` doc | completed: with `d` from `search_by_halves` |
| 16490c8d2 | the shadow charge equals the solver's | `projection.rs` 937-958 | already there |
| 26e45260d | `met_atoms` over a shared base is exact | `met_atoms` | completed: `⋂ (B ∪ E_i) = B ∪ ⋂ E_i`, DOI 10.48550/arXiv.1301.3388 |
| 26e45260d | `by_cells` answers alike whatever atoms `cells_of` takes | `by_cells` doc | already there |
| 2df2801ba | I4.15: `solve_regime` reads the residue in a canonical coordinate | `modular.rs` 2355-2440 | already there |
| 2df2801ba | I4.11: `Refusal::said` names the moduli | `refusal.rs` `Refusal::said` | already there |
| 2df2801ba | I4.11: the moduli print in increasing order | `zedc/src/front.rs` `linear_questions` | completed: holds for numerals, said so |
| 2df2801ba | the PNCX cost comments (`forced_pair_bounds` at most two clauses) | `modular.rs` | already there |
| R4-CLAUDE-2 | a clause is moved into the last product | `modular.rs` 2718 | already there |
| R4-CLAUDE-3 | the scope test exercises the top-level split | `one_scope.rs` `the_fails_questions_of_pairs_scale` | corrected: the split is gone |
| R4-CLAUDE-8 | the split keeps the model order | removed in round 5 | no longer relied on |
| I4.3 | 64 of the 5,000 formulas are refused | `one_scope.rs` the 5,000 test | corrected: 6 now; 64 is a ceiling |
| 30732fe05 | each rule of `residues` reads a superset, so empty means empty | `extend/residues.rs` module doc | already there |
| 30732fe05 | `over` reads the bounds of one quotient as a window | `extend/residues.rs` `over` | corrected: false, fixed, red then green |
| 364dd4a15 | `Summaries::make` may eliminate a product outside the key | `extend.rs` `Summaries::make` | completed: exact as `decide` reads a product; test `decide_reads_a_product_as_an_atom_of_its_own` |
| 364dd4a15 | the key keeps a product when it keeps both factors | `extend.rs` | already there |
| 374a5823a | `tighten_each` moves a bound only on proof | `tighten_each`, `linked_conjuncts` | already there |
| 3bd1b249d | the sweep agrees with the pick | `cell_sweep_empty_tests`, `sweep_against_pick_tests` | already there |
| 3fb4bb8e4 | `forest_row_hulls` and `deep.rs`'s early return are exact | `forest_row_hulls`, `deep.rs` 470 | already there |
| 47dbe05b9 | the bounds of a `bitAnd` variable hold | `zedc-preimage` `bit_and_bounds` | already there (outside this crate) |
| 47dbe05b9 | `linear_reading` sets `bitAnd` variables operands first | `linear_reading` | completed: why the numbers give that order |
| 47dbe05b9 | `eval` reads products as products, an absent atom as 0 | `Lin::eval` | already there |
| 4e52a49fc | `MapHull` composition is associative | `MapHull::compose` | corrected: not for `exact`; test added |
| 4e52a49fc | `compose`, `add`, `exact_union`, `exact_sum` keep `exact` sound | `OffsetHull` | already there |
| 4e52a49fc | `progression_meets` solves the congruence | `progression_meets` | already there |
| 4e52a49fc | `catalog_live` meets over disjoint bases | `catalog_live` | already there |
| 4e52a49fc | `chain_witness` assumes its chain | `chain_witness` | already there (marked not proved) |
| 4e52a49fc | `Faces::free` answers `Ok(false)` only on proof | `extend.rs` `Faces::free` | already there |
| 4e52a49fc | `met_outside` fixes atoms the equations force | `extend.rs` `met_outside` | already there |
| 4e52a49fc | `point` answers `Ok(None)` exactly | `extend.rs` `point`, `Bound::of` | already there |
| 5a5c167cf | `drop_outside_values` removes no point | `values::drop_outside_values` | already there |
| 5eba9712b | `Con::reduced` keeps the points | `formula.rs` 651-687 | already there |
| 68416f089 | `edges` reads difference constraints and bounds | `conjuncts.rs` 657-705 | already there |
| 68416f089 | `differences_only` is read from two counts | `conjuncts.rs` `Blocks::differences_only` | already there |
| 6d5a815dd | without a top-level first step no part has its value | `forced.rs` `may_start` | corrected: a part below may; `false` still sound |
| 6d5a815dd | the subset reductions' counts are necessary conditions | `reduce_subset_row_eqs`, `slack.rs` 63 | already there |
| 6d5a815dd | `settle`'s count check loses no answer but an early empty | `row_domains.rs` `settle` | already there |
| 7a7417966 | each use of the shared union-find keeps the root its caller needs | `conjuncts.rs`, `exact.rs` `split`, `extend.rs` | already there |
| 8780d212c | `difference_hulls` reads the least and greatest values as shortest paths | `presburger.rs` `difference_hulls` | already there |
| 8780d212c | Shostak 1981 cited at the sites | `difference_hulls` doc, `conjuncts.rs` `Edge` | added: doi:10.1145/322276.322288 at both |
| 8ecea2e9f | `remove_covered` drops only covered rows | `conjuncts.rs` `remove_covered` | already there |
| 9312fea5a | `substituted_difference_hulls` is exact | its proof at the site | already there |
| 9e25afa99 | `merge_pieces` with different rests is the union | `extend.rs` `merge_pieces` | already there |
| 9e25afa99 | `by_pairs` rewrites exactly, both signs | `extend.rs` `by_pairs` | already there |
| b991293a4 | DOIs at the cited sites | file headers, Seidel and Aragon, Tarjan and van Leeuwen | already there |
| b991293a4 | the union-find descriptions match their code | `guarded.rs` `ties`, `conjuncts.rs` `uf_merge` | already there |
| bf0be61bc | `DeepHulls` is sound (meet of the base, join of live disjuncts) | `DeepHulls` | already there |
| bf0be61bc | `settle_tied`: an empty base means an empty formula | `settle_tied` | already there |
| c8cac82fa | the domain intersection by complements and the `x = 1` shortcut | removed since | no longer relied on |
| c8cac82fa | `ScalarWitness` answers true only at a point | `modular.rs` `ScalarWitness` | already there |
| cc9e97345 | `drop_jointly_empty` projects each disjunct exactly | `drop_jointly_empty` | already there |
| cc9e97345 | `hold_waiting` keeps every point of the search | its proof at the site | already there |
| cd403f3b0 | the two-pin reading is a unimodular change of variables, the dark term Pugh's | `two_pins.rs` module doc, `shadow` | already there |
| d3f5e50c3 | the exposed range of `sweep_row_unbounded` | `slack.rs` `sweep_row_unbounded`, test `unbounded_row_tests` | already there |
| d3f5e50c3 | `main_m` are the right-to-left suffix maxima | `slack.rs` two comments | corrected: they are the left-to-right maxima, listed from the last |
| d77a6be8e | `stable_colors` moves its colors as an exchange moves the starting colors | `Renamed::individualized` | completed: proved by the induction of `RowGraph::refine` |
| d77a6be8e | `permutes_onto_itself` says yes only to a symmetry | `Renamed::individualized` | already there (marked not proved) |
| dc637c0d3 | `merge_pieces` gap side and `without_free_pairs` counts | `extend.rs` | already there |
| e8981310f | `Orbit::residue` counts the skipping steps | `extend/images.rs` `Orbit::residue` | completed: derivation at the site |
| f17dead5b | `Omega::flush` loses no elimination by its loose pairs | `presburger.rs` `flush` | already there (marked assumption) |
| f9936c4fe | `two_atom_side` is a unimodular substitution | `two_atom_side` | already there |
| f9936c4fe | Pugh 1991 cited at the sites | `two_atom_side`, the unit-equality step | added: doi:10.1145/125826.125848 at both |
| fafbc69a5 | `exact_each` asks in one order | `exact.rs` `exact_each_checked` | already there |
| fafbc69a5 | the fast paths have a quarter of the limit | `exact.rs` `tried` doc | corrected: the whole limit, as the code and the note below say |
| fdb5fda2a | `kept` and `took` keyed by `Parts::id` | `probe`, `search_by_halves` | already there |
| 0d4b0170a | full citations and checks | `lib.rs` References | already there |
| 104c0e177 | `satisfiable` reads a missing atom as zero | `satisfiable` doc | already there |
| 11e2c2786 | `by_cells` answers alike whatever cells `cells_of` takes | `by_cells`, `cells_of` | already there |
| 1a19cae20 | `ProjectionMemo` keys by formula, symbols and path flags | `ProjectionMemo` | already there (marked assumption) |
| 23ae5cdd3 | "splinter" is not Pugh's word | `lib.rs` References | already there |
| 23c5a37c0 | a constraint with no atom decides its part | `Parts::of` | already there |
| 2dfb9e87f | `solve` may defer the splinters | `solve`, its proof | already there |
| 2f837d6da | the Atom-order fallback | `modular.rs`, superseded by the I6.3 fix | already there |
| 34e5a4454 | `Blocks::gaps` and `is_gapped` | `conjuncts.rs` | already there |
| 3aa6326c3 | `Extending::extend` settles on a part with no point | `extend.rs` `extend` | already there |
| 3f2a92b63 | kept blocks brought up to date from diffs | `family`, `class_core` | already there |
| 4a9b79d02 | `learn` searches by doubling | `learn` | already there (monotonicity marked not proved) |
| 5202d9698 | `System::symmetries` maps a tie onto itself | its proof in the doc | already there |
| 5a5084526 | `swaps_onto_itself` says yes only to a symmetry | `System::swaps_onto_itself` | already there |
| 6da69df6f | the interval operations moved to `zed_collections::intervals` keep their proofs | `zed-collections` `intervals` | already there (outside this crate) |
| 729325cd6 | `forest_domains` unions simple disjunctions alone, component by component | `presburger.rs` `forest_domains` | already there |
| 8bf067d56 | the `Ord` fast path of nodes of constraints alone is the derived order | `deep.rs` `cmp_node` | already there |
| 96dae93e0 | `rays_once` bounds and merges | `extend.rs` `rays_once` | already there |
| 96dae93e0 | `unit_classes` substitutes exactly (keys never roots) | `extend/residues.rs` `unit_classes` | already there |
| 96dae93e0 | a cut widened by the scale's absolute value less one reaches no other image | `extend/holes.rs` `Holes::cut` | completed: proof at the site |
| 96dae93e0 | `same_divisions` sets `q` to `q' + (c' - c) / m` | `extend.rs` `same_divisions` | corrected: `(c - c') / m`, proof added |
| 96dae93e0 | `same_divisions` is exact since the rows stay | `extend.rs` `same_divisions` | corrected: open case closed by a check, red then green |
| 9b756f7ea | `read_once` pushes boxes down soundly, small to large | `read_once` | already there |
| 9c56b1189 | `walk_segments` is its own mirror; free coordinates take least offsets | `modular.rs` | already there |
| 9c56b1189 | CRT combination and `score_witness` | `combine_crt_pair`, `combine_crt_tree`, `score_witness` | already there |
| 9c56b1189 | `graph_coloring_witness` gives a point that meets every clause | `modular.rs` `graph_coloring_witness` | completed: proof and Baetz and Wood DOI; each point is also checked by `solve_modular_whole` |
| 9eaff655d | `forced::empty` before the renaming answers alike | `forced.rs` module doc | already there |
| a7032e3f4 | `Bound` substitutes exactly through its union-find | `extend.rs` `Bound` | already there |
| b3ff809f1 | keys behind `Arc` compare by content | `conjuncts.rs` | already there |
| b87677be2 | each case built for a kind of draw gives it | the seventeen random tests | already there (eight spot-checked) |
| bbe8ee73e | each message of `local.rs` is a relaxation | `local.rs` module doc | already there |
| c2f253250 | `point_past_refusal` checks its point | `presburger.rs` `point_past_refusal` | already there |
| c74ad4124 | the least-prime table is exact | `zed-numtheory` | already there (outside this crate) |
| c80855b33 | each repair offered repairs | the repair tests | already there |
| cb6445059 | a fast path charges at most `2L` | `exact.rs` `tried` | already there |
| cb6445059 | Monniaux, Bjørner and Janota, Pugh cited | `exact.rs`, four sites | added: their DOIs |
| cc5576aea | the union-find, the worklist order, the I6.3 tie | `modular.rs` | already there |
| cc5576aea | `forced_pair_bounds`, `three_disjoint_pairs` | `modular.rs` | already there |
| cc5576aea | Baetz and Wood cited | `brooks.rs`, `lib.rs`, `graph_coloring_witness` | added: doi:10.48550/arXiv.1401.8023 |
| cdc669612 | laminar subtraction, the halving of `FastGreedy`, `Hull::shown_empty` | `slack.rs`, `presburger.rs` | already there |
| cf2546144 | the hull of `v0` in seed 1446, case 7, is `[1, 4]` | its test's hand proof | already there |
| cf65370dd | `bridge` relabels the smaller side | `conjuncts.rs` `bridge` | already there |
| cf65370dd | without the conjunct the blocks are a path from `u` to `v` | `conjuncts.rs` `peel` | completed: proof at the site |
| cf65370dd | Holm, de Lichtenberg and Thorup cited | `conjuncts.rs` `peel` | added: doi:10.1145/502090.502095 |
| d5ae3f504 | the capped system is checked alone | `extend.rs` tests | already there |
| d8026ecb5 | `Lin::cmp`'s fast path is the derived order | `formula.rs` `Lin::cmp` | already there |
| d8026ecb5 | Bagwell's hash array mapped trie | `conjuncts.rs` `Blocks` | completed: full citation, no DOI found |
| ecfbd2bd0 | the share bound gates the search; stage C's empties | `modular.rs` | already there |
| ed3971714 | priorities fix the shape alone; the chain's cost bound | `extend/images/shifts.rs` | already there (bound marked not proved, cost only) |
| eea76fee4 | a name `#n` given an absent atom meets no other | `Renamed::there_all` | already there |
| eea76fee4 | the empty check before renaming answers alike | `project_each_with` | already there |
| eea76fee4 | least span first is the order of least work | `extend.rs` groups | already there (marked not proved, cost only) |
| efe9dcf29 | `pairs`, `by_pairs` and the remainder rewrite are exact | `extend.rs` | already there |
| efe9dcf29 | `envelope` drops only rows under the others | `extend.rs` `envelope` | already there |
| efe9dcf29 | a piece meets only its neighbors in a group | `extend.rs` `merge_pieces` | corrected: the reason (the nearer piece may hold no point) |
| f3778742d | `satisfiable` reads products as atoms | `presburger.rs` 276-281 | already there |

The potential that `Scope::shortest` keeps (68416f089) is in `zedc-preimage` `product.rs`,
outside this crate, and was not checked here; nor were `twovar::ends` (f9936c4fe, in
`zedc-solvers`) and `lin_at` (c8cac82fa, in `zedc-preimage`).

No code claim: 0f5f38d66 (tests pinning refusals), 295d02151 (comments dated), 6b87a1c3a
(tests moved to `r4_tests.rs` and `r6_tests.rs`), 12c58bd41 (no `#[ignore]` left), 141a411e3
(import cycles), 23ce8727a (tests only), 4c17c8e8f (crate move), 5168f5a37 (clippy),
5ccb21f3f (import cycles, clippy), 62e774ae6 (a doc link made plain text), 81878e7cb (tests
use `part()`), 8980815f3 (a doc link made plain text), da7810c72 (formatting), f02739989
(lint fixes), f66d9b0b1 (the four ignored scaling tests, since moved to bench modules).

Not read: of e8981310f, all of `extend/images.rs` but
`Orbit::residue` (`answer`, `joint`, `shifts`, `Clamp`, the `Frame` operations) and its
changes to `extend.rs`.

## proofdoc4f: zed-kernel, zedc-elab, zedc-base

Entries of list f in list order, each message and its whole diff in the crate, with every
claim checked at its site: 001 to 010 at base ae22906d0 (merge 1, 3d8817975); in part 2, at
base 3d8817975, 011 to 015, 022, 025 to 029 and 034 to 051 in full and 016, 030 and 052 in
part. Part 2's entries were read by four reader agents of proofdoc4f (stopped on the
coordinator's order, see below), whose edits proofdoc4f read before the merge. Three claims
are "covered by" a row another agent owns; they are counted under "Already there".

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zed-kernel | 39 of 62, 3 in part | 128 | 70 | 55 | 2 | 1 |
| zedc-elab | 0 of 44 | 0 | 0 | 0 | 0 | 0 |
| zedc-base | 0 of 39 | 0 | 0 | 0 | 0 | 0 |

| Source | Claim | Code site | Status |
|---|---|---|---|
| 00171c62b | A candidate tuple of a region's row that `holds` in `f` shows `f` met with the region is inhabited, so the fork's answer `false` is exact | `types/empty.rs`, `tuples_on`, the K134 comment | completed: the steps (`reps` gives a value of each `g.r[j] & a[j]`, `holds` tests it is in `f`) |
| 00a508032 | `ieee_min_max` follows IEEE 754-2019 `minimum`/`maximum`: NaN absorbs, -0 below +0 | `value.rs`, `ieee_min_max` | already there (quotes, doi:10.1109/IEEESTD.2019.8766229, C23 N3096, test named) |
| 0b1008760 | The five `(false, true)` atom arms are unreachable: a finite atoms map lists no name whose part is `AtomPart::none()` | `types.rs`, `Atoms` (the invariant on `names`); arms in `types/empty.rs` and `empty/shared.rs` | completed: the invariant stated at `Atoms` with every writer of `names` (`set`, `default`, the universe, `zip`, `minus`, `join`, `not`) |
| 0b1008760 | `(None, None)` in `shape` is unreachable: a diagram node has a leaf branch | `types/empty.rs`, `shape` | completed: why `b` is a list there (`Bdd` has the forms `Leaf` and `List`; `branch` of a list is `Bdd::view`), and the test with what it cannot show |
| 0e8168cc1 | A constant node of a BES has no child, is no parent and is on no cycle (three `unreachable!` arms) | `types/bes.rs`, `gfp` and `delete_cascade` | already there (checked: `Bes::add` and `Bes::set` assert it, `simplify` sets `Bot` only on a node whose children in `h` stay empty, `seal` makes parents only of children) |
| 10cc98a38 | A list cell's digest is a fold of its blocks in order and a set's a sum of its literals, the same for every shape | `types/bdd.rs`, `folded`; `types/bdd/set.rs`, `make` | already there |
| 10cc98a38 | Drawn cell priorities give expected depth `O(log m)` (Seidel and Aragon 1996) | `types/bdd.rs`, list `priority` | already there (doi:10.1007/BF01940876 at the site) |
| 10cc98a38 | The same bound cited for sets and treap joins | `types/bdd/set.rs` (priority doc, `union_if_agree`); `types/bdd/list/treap.rs`, `insert` | completed: doi:10.1007/BF01940876 and doi:10.1145/2935764.2935768 added where the cite had none |
| 19311b3fe | Records beside the pairs do not change the check of a list witness | `types/empty.rs`, `verify_step` | already there (proof and red-first test at the site) |
| 19311b3fe | `step_shape` gives one row or more, so `chain_row` and `joined_car` are not both none | `types/empty.rs`, `step_of` | already there |
| 1a78001da | `proc_kib` reads a kB field by its whole key, checked for `u64` overflow | `limits.rs`, `proc_kib` | completed: the test named at the site, and what it cannot catch |
| 1f50505a3 | Finding repeated addresses by hash finds the same repeats as the ordered set | `provenance.rs`, `Provenance::repeated` | added: `Hash for Position` writes `hash_value` and `eq` is false where they differ, so the `Hash`/`Eq` contract holds; the bench named |
| 1fcf49287 | One backward pass is exact: every input `k` of fact `j` has `k < j` | `provenance.rs`, `origins` | completed: why `k < j` (the one writer of `Fact::inputs` in `eval.rs`, `fact`) |
| 222adf91b | The parity bench's `T0` is 0, so its treap bound is the `n log n` one | `types/bdd/bench.rs`, `parity_built_a_literal_at_a_time_scales` | already there (asserted on every input) |
| 26f8d7d35 | `stand_in` keeps exactly the matches of every type | `eval.rs`, `Held::stand_in` | completed: induction on depth (`matches_any` on a bare function, `Type::member` on a family, `contains` part by part, `with_parts`); no test runs `is` on a held value (row TEST-kernel-held-is) |
| 26f8d7d35 | The marks of a held atom are each taken once | `eval.rs`, `Machine::held`, `Prim::Atom` arm | completed: `atom_with` keeps the order, `atom_named` sorts and unzips, a permutation |
| 26f8d7d35 | A held atom is never bare | `eval.rs`, `matches_any`, `Pattern::Atom` arm | completed: the one maker of `Shape::Atom` runs only when a part is no data |
| 26f8d7d35 | `Drops` frees without recursion | `eval.rs`, `Drops` | already there |
| 26f8d7d35 | Held values cost O(parts) | `eval.rs`, held tradeoff comment | already there |
| 2ab9f29af | `bytes_text` rounds to the nearest | `num/room.rs`, `bytes_text` | completed: `to_f64`, the exact division by 1024, `{:.1}` rounding, the infinite case; test named |
| 2de401ae4 | The tree depth is at most 63 | `text.rs`, module doc | completed: a part of height `k` holds `2^k` blocks or more, so `b >= 2(2^d - 1)`; tests named |
| 2de401ae4 | The `chunks` stack holds at most `6d + 9` parts | `text.rs`, `chunks` | added: the derivation; test named |
| 2de401ae4 | `nodes` takes 2 to 12 parts and makes at most 4 nodes of 2 or 3 | `text.rs`, `nodes` | added |
| 2de401ae4 | Amortized O(1) push (Hinze and Paterson) | `text.rs`, module doc, `push_back` | already there (DOIs, departure, tests) |
| 2de401ae4 | `Size::add` does not overflow | `text/tree.rs`, `Size::add` | already there |
| 3204ef377 | `part_boxes` `(None, None)` cannot happen | `types.rs`, `part_boxes` | already there |
| 3204ef377 | `Rep::key` is never called on `Of` or `Closure` | `types/empty.rs`, `Rep::key` | already there |
| 3204ef377 | The two-operand arm sees `y` none only for `Not` | `types/empty.rs`, `Choices` | already there |
| 3204ef377 | An exclusive-or component has a cell | `types/empty.rs`, `Choices::index` | already there |
| 3204ef377 | `system`'s `Not` arm cannot happen | `types/empty.rs`, `system` | already there (`Group::new` rejects through `flipped`) |
| 3204ef377 | `folded` sees only meets and lists | `types/print.rs`, `folded` | already there |
| 3204ef377 | `bad` is always an `Expr::Ref` | `types/rec/group.rs`, `Group::new` | already there |
| 3204ef377 | The `sweep` walk, `local` never `Of`, `pair_picks` leaves, `put` with class `Of` | `types/empty/sweep.rs`, `types/empty.rs`, `types/print.rs` | already there (comments read, not traced line by line) |
| 34a583731 | A value found in a region's piece is a value of the part | `types/empty.rs`, `class_rep`, `key_pieces` | already there |
| 37148785d | Each new phase adds a type to `dead`, which bounds the phases | `types/empty.rs`, `Search::settle` | completed: `end_phase`, `settled`, `pop_open_forks`; that the types made are finitely many is stated as not shown (row PROOF-kernel-search-types-finite); the `no_key`/`no_keys` claims not read |
| 59a32b29b | `sqrt` and `mul_add` are correctly rounded | `eval.rs`, `prim_on`, `Prim::Sqrt`/`Fma` | completed: the Rust std "Precision" docs quoted |
| 59a32b29b | Measured cost, 8.0 times the work at 8n | `eval.rs`, same site | completed: the stale test name replaced by the bench `sqrt_fma::n_calls_cost_linear_time`; numbers dated to 59a32b29b |
| 59a32b29b | IEEE 754 citation | `eval.rs`, same site | already there (DOI and quotes) |
| 6017477df | `Form::holds`, the Not arm | `types/bdd.rs`, `Form::holds` | already there |
| 6017477df | `choose`: two `false` branches cannot meet | `types/bdd.rs`, `Connect::choose` | already there (arm removed by 6bb9bb93f) |
| 6017477df | `clause`: `Form::Or` cannot happen | `types/bdd.rs`, `clause` | already there |
| 6017477df | `Part::xor`'s let-else always matches | `types/bdd.rs`, `Part::xor` | already there |
| 6017477df | `node`'s unreachable arm | `types/bdd.rs`, `xor::node` | already there |
| 6017477df | `meet` of two lists: the second is a literal | `types/bdd.rs`, `xor::meet` | completed |
| 6017477df | `pair`: a list reaches the last arm only as a chain of two | `types/bdd.rs`, `xor::pair` | completed |
| 60f594a97 | A zero-atom row with `fc == MAX` makes the type empty | `types/empty/escape.rs`, `decide_counted` | completed: the step on killed rows, and what the tests cover |
| 6ae1d9048 | `limit(size)` covers every product of three sums | `poly.rs`, `LIMIT` | already there (replaced by the constant `LIMIT`; nothing relies on it) |
| 6ae1d9048 | A refusal costs at most the limit, or twice it | `poly.rs`, `LIMIT`, `factored` | covered by FIX-poly-limit-comments |
| 6ae1d9048 | `Poly::pow`'s wide branch: the shape check refuses wide exponents | `poly.rs`, `Poly::pow` | covered by FIX-poly-limit-comments |
| 6ae1d9048 | A monomial's power is charged no more than the result's words | `poly.rs`, `Poly::pow` doc | completed: the bit count of `x^n`, coefficients never 0 |
| 6ae1d9048 | A constant below 1 is kept as its reciprocal on the other side | `poly.rs`, `same_factors` | completed: `c != 0`, the exponents swapped |
| 6ae1d9048 | The difference in `compare` is not charged | `poly.rs`, `compare` | completed: each side's words bounded by the work charged; no test measures it |
| 6ae1d9048 | The support product costs at most twice the cheaper method | `poly.rs`, `support_mul` | completed: the steps; about three times when it gives up |
| 6ae1d9048 | `too_wide` gives the smallest node | `poly.rs`, `too_wide` | completed: operands are pushed before the node |
| 6bb9bb93f | Two leaves need no arm in `choose` | `types/bdd.rs`, `Connect::choose` | already there |
| 6bb9bb93f | The `Some(first)` arm of `instance` is not reached | `types/rec/group.rs`, `Group::instance` | already there |
| 6bb9bb93f | `ints` holds only integers | `types/empty/escape.rs`, `Ints` | already there |
| 6bb9bb93f | Every clause has two atoms or more | `types/empty/escape.rs`, `decide_counted` | already there |
| 6ebe63b42 | rustc inlines an unmarked function into other crates only when it calls nothing | `digest.rs`, `Digest::write_u64` | completed: rust-lang/rust PR 116505 (Rust 1.75) cited |
| 6ff237028 | The settled form holds every value of the part | `types/bdd.rs`, `Part::settle` | completed: Shannon expansion step by step |
| 6ff237028 | A tuple part `false` outside its tuple types has every value in one of them | `types/empty.rs`, `Group` kids walk | completed |
| 6ff237028 | Two types in different classes are disjoint | `types/empty.rs`, `overlaps` | Not proved: that the walk places keys, lists or wholes covering every value of a type in every `Parts` case and with lazy `Placing` reads (row PROOF-kernel-overlaps-cover); `split_classes`, `class_rep` not read |
| 86322e10b | `seconds` rounds up, none out of range | `zedc-check/src/check/limits.rs`, `seconds` | already there, see proofdoc4d (moved out of zed-kernel) |
| 86322e10b | `MEMORY_TITLES` lists every title of a memory refusal | `value.rs`, `MEMORY_TITLES` | added: the eight `KernelError` arms named; a new arm must be added by hand and no test fails if it is not |
| 877fc8603 | `fresh_id` never draws an id twice, nor block 0 | `value.rs`, `fresh_id` | completed: blocks from 1, each once; needs fewer than `2^48` blocks, not checked at run time |
| 8878228af | `Field::mul` and `forward` residues stay within `2p` and `4p` | `num/fast.rs`, `Field` | already there |
| 8878228af | Treap priorities are 5-wise independent | `types/bucket.rs`, `priority` | already there |
| 8878228af | A datum's text is linear in its distinct parts | `walk.rs` | already there |
| 8878228af | `canon` costs O(t log t) | `types/print.rs`, `canon` | already there |
| 8878228af | Cole and Vishkin, with the DOI | `text/names.rs` | already there |
| 8c5ccccb9 | Two positions are equal exactly when their paths are | `provenance.rs`, `PartialEq for Position` | added: depth and hash are functions of the path, links never change; test named |
| 8c5ccccb9 | The order of positions is the term's preorder, total, agreeing with `==` | `provenance.rs`, `Ord for Position` | added; test named |
| 8c5ccccb9 | `Held` enters each part once and finds its set before reading it | `provenance.rs`, `Held.seen` | completed: stack order, no cycles in values; test named |
| 8c5ccccb9 | `Held::base` and `family` cost O(\|f\|) | `provenance.rs`, `Held::base`, `Held::family` | already there |
| 8c5ccccb9 | Join and meet cost O(min log n) | `provenance.rs`, `IdSet` | already there |
| 8c5ccccb9 | The meaning of a family's id and `from` | `value.rs`, `Family::extend` | already there |
| 929e7e04a | `m61::inv(a)` is `1/a mod P` for `0 < a < P` | `zed-numtheory/src/lib.rs`, `m61::inv` | already there (doc and `debug_assert!`) |
| 929e7e04a | Callers pass `0 < a < P` | `poly.rs`, `eval`; `value.rs`, `R`, `range_sum` | already there |
| 94b14f925 | A tally's `found` is the union of its entries' sets | `provenance.rs`, `struct Tally` | completed: five invariants, each kept by every operation; tests check only `found` |
| 94b14f925 | Each base is smaller than the set on it, so following bases ends | `provenance.rs`, `Tally::count` | completed |
| 94b14f925 | A meet equal to either set is that set | `provenance.rs`, `Provenance::origins` | added |
| 94b14f925 | A union chain costs O(n log n) | `provenance.rs`, `made_by_difference`, `union` | already there |
| 967100aca | A morphism type is empty only when a key is shown to exist; a representative is in its type | `types/empty.rs`, `no_morphism`, `rep` | already there |
| 967100aca | A type met again on its own path has no value there | `types/empty.rs`, `rep` | already there |
| 967100aca | Two tuples per length, O(c) | `types/empty.rs`, `find_rep` | already there (replaced; COMPLEXITY.md K80, K126) |
| 9778881e0 | A true verdict on the forms is true on the types | `zedc-types/src/ty.rs`, `Forms::level` | already there |
| 9778881e0 | `rewrite_levels` and `rec_kept` keep membership, each node once | `types.rs` | already there |
| 9778881e0 | `map_atoms` keeps the connectives, O(k log k) a block | `types/bdd.rs`, `Part::map_atoms` | already there |
| 9bc1e50d4 | `split` never meets the key itself | `types/bdd/list/treap.rs`, `split` | completed: heap order and search path; test named and what it cannot catch |
| 9bc1e50d4 | A finite atoms map lists no name with no atom (three arms) | `types/empty/shared.rs`, `types/empty/escape.rs` | already there (the `Atoms` invariant, merge 1) |
| 9bc1e50d4 | A part over one atom true at both values is a leaf | `types/empty/shared.rs`, `list_step` | completed: no test reaches the arm; what the `debug_assert!` cannot catch |
| a74161bb4 | `meet_operands` gives one node per operand, in written order | `types/empty/refused.rs`, `meet_operands` | completed: induction; test named |
| a74161bb4 | `meets[v]` exists for every `And` node made from a meet | `types/empty/refused.rs` | already there |
| a74161bb4 | A refused tuple or meet lists two open parts or more | `types/empty/refused.rs`, `refused_site` | completed |
| a74161bb4 | `listed` never gets an empty list | `types/empty/refused.rs`, `refused_site` | already there (replaced by `text::prose::and_list`) |
| a74161bb4 | No other shape reaches the last arm | `types/empty/refused.rs`, `refused_site` | already there |
| b8b284a09 | Every entry is defined when `stalled` is empty | `eval.rs`, `finish_fix` | completed: each caller, why no entry is `Open` or `Busy`; three tests named |
| b8b284a09 | `from_map` gives what `from_leaves` gives | `eval.rs`, `finish_fix` | completed |
| b8b284a09 | The ready positions, sorted, are in key order | `eval.rs`, `next_entry` | already there |
| b8b284a09 | A chain costs O(D) under Rounds and Pull | `eval.rs`, `round`, `pull` | already there |
| b8b284a09 | One hash lookup per read | `eval.rs`, `Definedness::index` | already there |
| b8b284a09 | The outermost pair need not be kept | `value.rs`, `walk_in` | completed |
| b8b284a09 | A thread keeps at most 8 times the last comparison's pairs in slots, or 16 | `value.rs`, `ReadSet::clear` | corrected: false when a comparison keeps no pair after a large one (the early return kept 2048 slots); test `a_comparison_that_keeps_no_pair_does_not_keep_a_large_table` red (2048, not 0), code fixed, green |
| b8b284a09 | 256 bytes a thread for each relation | `value.rs`, `ReadSet` | already there |
| bc75c1615 | `2^w - 1 - x` fits when `w <= 63` | `bits.rs`, `small` | completed |
| bc75c1615 | `x * 2^k` with `k <= 62` fits in an `i128` | `bits.rs`, `small` | completed |
| bc75c1615 | An arithmetic shift is the Euclidean quotient; past 63 places 0 or -1 | `bits.rs`, `small` | completed |
| bc75c1615 | Rotations are exact when `w <= 63` | `bits.rs`, `small` | completed; tests named |
| c5168f1b3 | `loop_heads` is never empty | `types/empty.rs`, `verify_step` | already there (now `groups`) |
| c5168f1b3 | Each group's set of heads is not empty | `types/empty.rs`, `verify_step`, `join` | added |
| c5168f1b3 | A member refused by the group goes back to `Refused(Group)` | `types/empty.rs`, `group_verdicts` | already there |
| c9205d30b | The citation and Algorithm 1 mapped to the code | `refine.rs`, module comment | already there (DOI) |
| c9205d30b | The count over `0..=most[c]` is paid for by the arcs read; `tally` stays in bounds | `refine.rs`, `Refine::split` | added; two tests named |
| c9205d30b | `k` is never waiting when pushed | `refine.rs`, `Refine::split` | already there |
| cb68d7fec | `car_heads` is never empty | `types/empty.rs`, `step_of` | already there |
| cb68d7fec | `chain_rep` gets only `Inhabited` plans | `types/empty.rs`, `chain_rep` | already there (the type enforces it) |
| d18e52a0a | `order::cmp` is a total preorder | `types/print/order.rs`, `cmp` | added; tests named |
| d18e52a0a | `cmp_values` is a total order | `types/print/order.rs`, `cmp_values` | covered by PROOF-value-cmp-total |
| d18e52a0a | An atom at bucket `i` has `cuts[i-1] < name <= cuts[i]`; O(log a) a name | `types.rs`, `Type::print_groups` | completed: `partition_point`; the O(log c) search added to the cost |
| d18e52a0a | `uses[i] -= 1` never goes below 0 | `types/print.rs`, `Printer::print` | added |
| d18e52a0a | The loop in `write_out` ends | `types/print.rs`, `Printer::write_out` | Not proved: no chain of single-`Seg::Node` texts comes back to a node on it (row PROOF-print-write-out-ends) |
| d18e52a0a | O(m log m) for one stable sort | `types/print.rs`, `items` | already there |
| d2bc324d2 | `kids` gives exactly the names `eval.rs` binds | `term/walk.rs`, `kids` | already there |
| d2bc324d2 | `R(body)` depends only on the body | `eval/made.rs`, `reads` | already there |
| d694e2a26 | The ladder encoding allows at most one true atom, three clauses an atom | `types/empty/escape.rs`, the 2-SAT build | added: both directions |
| d694e2a26 | No 2-SAT model means no list escapes | `types/empty/escape.rs`, before `sat.solve()` | added |
| d694e2a26 | Building the list stays within the cost bound | `types/empty/escape.rs`, `depth` | added: `k^2` for `k` distinct atoms at a place, within their written size |
| d694e2a26 | The truncation lemma | `types/empty/escape.rs`, module comment | already there in substance; "not killed" means not killed at a place up to `l0` (the code reads cells only to `target_len`); wording not edited; the rest of the entry not read |

No code claim: 9e3cc1480 (zed-kernel part: an alias, an equivalent `?`, moved tests).

Not read:

- zed-kernel (20, 3 of them in part above): 37148785d (the `no_key`/`no_keys` claims),
  3ffbadf75 40733faeb 465fc2167 570acb0a8 5970a932f 5a5276a82 5dcfdad0a, 6ff237028
  (`split_classes`, `class_rep`), 7d0cc8d9f 8183b743b 81a60d522, d694e2a26 (the `ChainHint`
  fallback, `cells_windows`, `Live`, X34, X35, `forest`), ddc1ec274 e3ee7d064 e60e73504
  e62be00e0 e7b12dd2e f075a1c0b f48ec1bf4 f91eac49c fa271b3f2 fe770de11
- zedc-elab (44): 7fb0c6594 7931d6ed6 8164a8ea9 9b7a17570 e5ff7920a f24b492bf 555863e23
  f0bde0d35 0e329a46e 1286f4779 2b3e706f1 995200322 9d877b65c 068d62e2f 18ea94666 4c75d8f88
  5767fe37a 7d0cc8d9f 86322e10b 875e58597 c50a8965b cf099fcf2 03a4f95f2 0e8df04e7 64d244789
  ac7cafdd0 ac9176a94 cb0137143 d11373afd f240a5462 131d7f7fd 14b96090a 29bf6b297 47d87108b
  480291d0e 4ce8104bb 51ae6534c 650ec1e0a a7dba5382 af7540d08 b6b810dec ea2effe91 eb156f28d
  fbb2b68aa
- zedc-base (39): 30ad62cc4 7fb0c6594 13237878e ba41f402c d6fa0ddbd 25ef78dd1 7d9e078c0
  a02d270c5 eb9d470b5 007a9ebb0 24a43c819 4e6c5bfaa 50b8eea24 5767fe37a c5ed79580 331f39ab5
  726008ee7 8a14a296f 981ec6c8a 995a598b2 bea44d4a5 bfc106d61 d11373afd e6dfb6877 ebd6faee5
  168d440d9 259a46243 3ef2d671a 4ce8104bb 50a4b3789 6a1038700 7634e8afc 835596645 a1740c637
  b6fab1610 c80981f4b cac8265b5 f64572af8 fde51511a

## proofdoc4g: the moved commits, zedc-solvers, zedc-int, the small crates, `type_var_form`

Read so far: the 25 entries in the small crates (zedc, zed-native, zedc-resolve, zedc-zir,
zedc-syntax, zed-numtheory, zed-rt, zed-tools, zedc-lattice) and the `type_var_form` claim of
4e6c5bfaa with zed-kernel print/names.rs, each message and its diff in that crate; the sites
were checked on origin/main e1274cda9. Then zedc-int and zedc-solvers, each entry but the two
crate splits, and 8 of the 39 moved commits, checked on origin/main 8c9dd3cbd. Then 21 more
moved commits (6c2c05101 to a934e9cf8 below), each message and its whole diff, the claims
found at their sites on origin/main 8f447824e; then the last 10 moved commits (e3b9b5c6b to
fec575742) the same way, and the comment lines the two crate splits 87bab4327 (zedc-solvers,
whose live3.rs no list entry reaches) and 6cc6d3efd (zedc-int) moved, read for claims only.
Every line of list g is read.

The entries read count the `type_var_form` claim of 4e6c5bfaa, which is not a line of list g:
list g has 98 lines (39 moved, 18 zedc-solvers, 16 zedc-int, 25 in the small crates), and the
first count of 66 entries read was 65 lines of list g and that claim, so 65 read and 33 not
read made the 98, and the 99 entries of the table below are the 98 lines and that claim.

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zedc | 5 | 5 | 4 | 1 | 0 | 0 |
| zed-native | 5 | 6 | 4 | 1 | 0 | 1 |
| zedc-resolve | 3 | 0 | 0 | 0 | 0 | 0 |
| zedc-zir | 3 | 1 | 1 | 0 | 0 | 0 |
| zedc-syntax | 2 | 3 | 1 | 2 | 0 | 0 |
| zed-numtheory | 2 | 3 | 1 | 1 | 0 | 1 |
| zed-rt | 2 | 1 | 1 | 0 | 0 | 0 |
| zed-tools | 2 | 0 | 0 | 0 | 0 | 0 |
| zedc-lattice | 1 | 1 | 1 | 0 | 0 | 0 |
| `type_var_form` (zedc-resolve, zed-kernel) | 1 | 3 | 1 | 2 | 0 | 0 |
| zedc-int | 16 | 18 | 16 | 2 | 0 | 0 |
| zedc-solvers | 18 | 21 | 13 | 6 | 0 | 2 |
| moved (zedc, zedc-syntax) | 39 | 46 | 40 | 3 | 1 | 2 |
| Total | 99 | 108 | 83 | 18 | 1 | 6 |

| Source | Claim | Code site | Status |
|---|---|---|---|
| 51ae6534c | the status `main` gives is in `0..=255` | zedc run.rs `exit_status`; zedc-check walk.rs `status_in_range` | already there, see proofdoc4 (`status_in_range`) |
| bc75c1615 | the per-word bounds of `bitAnd`, `bitOr`, `bitXor`, `mulHi`, `pext` | zedc-lattice interval.rs `bit_word` (moved from zedc) | completed: why `\|` is at least each operand and `&` at most each, why `mulHi` is below `2^w`, why `pext` is at most its operand |
| bc75c1615 | `pow2` at `2^100` and the `i128` shift | none: the code is gone, every end is exact | already there (no site left) |
| bc75c1615 | a known or text value is read in O(n) | zedc-check mod.rs | already there |
| be476c3a4 | both build modes run one pipeline | zedc build.rs `Mode` | already there |
| 59a32b29b | `sqrt` inline gives the kernel's bits, on 900 random operands | zed-native codegen.rs `Prim::Sqrt` | corrected: the test runs 200 operands from a new seed each run; the count fixed |
| 59a32b29b | `fma` rounds once | zed-native codegen.rs `Prim::Fma` | already there (IEEE 754-2019 DOI, test) |
| 9379f755c | the argument buffer costs O(arguments) at `rt_args` | zed-native hooks.rs `rt_args` | already there |
| 9379f755c | the buffer's address stays valid across `rt_named` | zed-native hooks.rs `rt_named` | completed: `take` and the restore move the `Vec` header only, and `place_named` calls no hook |
| be476c3a4 | `through` runs the one pipeline | zed-native `through` | already there |
| d9d8729bb | held terms are keyed by cell index and generation | zed-native | already there |
| d9d8729bb | the cost of the held values | zedc-zir memory.rs | already there (HELD-cells) |
| 51ae6534c | `Mains` is built in O(k) by one stack | zedc-syntax builder.rs | already there |
| 51ae6534c | `Mains::at` finds the innermost body in O(log k + d) | zedc-syntax builder.rs `Mains::at` | completed: why the walk up `outer` from the last body that starts at or before the place finds the innermost body |
| d18e52a0a | two bounds written in different orders compare equal | zedc-syntax node.rs `carrier_names` | completed: `cmp` on `Member::of_name` is total and equal only for one name |
| 929e7e04a | `m61::inv` is `a^(P - 2)`, which needs `P` prime | zed-numtheory lib.rs `m61::inv`, `m61` | completed: new test `the_mersenne_modulus_is_prime` (`is_prime` and Lucas-Lehmer, Lehmer 1930, doi:10.2307/1968235, with a composite control); the count of squarings and products |
| fad56b903 | the `first_primes(n)` bench ratio is about 8.9 | zed-numtheory bench.rs | corrected: the bound is a power of two, 2^21 at n and 2^24 at 8n, so about 8.4; the formula as written gave 9.2; the two bounds now asserted in `the_first_primes_are_the_primes_in_order` |
| fad56b903 | the costs of the other benches, the controls, Montgomery's borrow, `split`'s `unreachable!`, the `psi_k` | zed-numtheory bench.rs, tests.rs, factor.rs | already there |
| d9d8729bb | `stand_in` keeps a held value's place | zed-rt | already there (the argument at zed-kernel eval.rs `Held::stand_in`) |
| bea44d4a5 | `bit_domains` and `whole_bytes` | zedc-lattice interval.rs | already there, see proofdoc2a |
| 4e6c5bfaa | a type variable is a name `[A-Z][0-9]*` | zedc-resolve `type_var_form` | already there (the code is the rule) |
| 4e6c5bfaa | the variables and the definitions share no name | zed-kernel print/names.rs module doc | completed: every variable has the form and no `Part{k}` does; tests named, and that neither reads a definition back |
| 4e6c5bfaa | `run_ends` is O(k) | zed-kernel print/names.rs `run_ends` | completed: each number starts one run or is skipped in O(1), and is written once; expected time over std's hash |
| 76bb9d4cf | a kept power is not built | zedc-int int.rs | already there |
| 29ab1ba6e | `write_decimal` is O(n log² n) | zedc-int int.rs, through zed-kernel fast.rs `to_decimal` | already there |
| d80e81d08 | `row_bound` gives the ends of `a·x + k >= 0` | zedc-int int.rs `row_bound` | completed: the garbled last sentence replaced by why the ends are `⌈-k / a⌉` and `⌊k / -a⌋`, and why one floor division gives both |
| 25ef78dd1 | `div_floor`, the `i128` divisions and their overflow, nearest zero, `mod_hat`, `ceil_log2`, `pow2`, `row_range` | zedc-int int.rs | already there |
| 2b3e706f1 | `Int` is unbounded for the searches | zedc-int int.rs | already there |
| 878a1bf1b | no prime below `FILTER_BOUND` = 1024 is 1 modulo an index above 511 | zedc-int `FILTER_BOUND` | already there (the indices are odd primes, so `q >= 2p + 1`) |
| fe770de11 | `ROOT_CHECK_PRIMES`, `extended_gcd`, the `unreachable!` of `root` | zedc-int int.rs | already there |
| 22e348bb9 | `mod_hat` cites Pugh 1992 and 1991 | zedc-int int.rs `mod_hat` | already there (DOIs) |
| 47dbe05b9 | `bitAnd` on two's complement | zedc-int int.rs | already there |
| b991293a4 | the citations of the crate | zedc-int int.rs | already there |
| d7e7d86d0 | the remainder tree, depth `⌈lg t⌉` (Bernstein) | zedc-int int.rs | already there |
| e843dda31 | the most one digits in `lo ..= self` | zedc-int int.rs popcount bound | completed: why no value of the range has more ones than the two candidates |
| 6da69df6f | `Int` is unbounded for interval lists | zedc-int int.rs | already there |
| cc5576aea | the gcd costs (Stein) | zedc-int int.rs `gcd` (code rewritten since) | already there |
| e5b5ea82e | the estimate is a cost only | zedc-solvers | already there |
| 475e582ff | the arithmetic of the built test graphs and covers | zedc-solvers negsssp.rs, utvpi.rs tests | already there (each checked by hand) |
| 1ffeb360d | `convex_strip`: with slopes of opposite signs the points are one interval | zedc-solvers twovar.rs `convex_strip` | already there |
| 1ffeb360d | `project_convex` is exact, `Holed` only on a real hole | zedc-solvers twovar.rs `project_convex` | completed: the tip and solid split at `⌈at0⌉`, `⌈at1⌉`, the count of 0 or 1 per `x`, the interval test, the period `d` of parallel lines and why `2d` values with `0 < c < d` hold a hole |
| 1ffeb360d | `project_convex` costs O(m log m) plus O(log M) per count | zedc-solvers twovar.rs `project_convex` | completed: with slopes of one sign two bisections over the counts, O(log w · log M) per strip, O(m log m + m·log w·log M) in all |
| 3e4f866b5 | 400 random graphs miss the odd zero-weight cycle in about 1 run of 400; 4,000 in about `e^-64` | zedc-solvers utvpi.rs tests | already there (since replaced by the built graphs, see d5ae3f504) |
| 25ef78dd1 | `Q` equality is structural, equal to equality of value since `Q::new` reduces | zedc-solvers linear.rs `Q` | completed: the three places that build a `Q`, each in lowest terms with `d > 0`, and why two reduced forms of one value are equal |
| 25ef78dd1 | the next power of two and the narrowing of a range | zedc-solvers | already there (2 claims) |
| 10a4e923a | the arithmetic of the completeness tests of Duong's search (`24·L·1 = 24 <= 66`, `M₀ = 36,886`, `L = 16`, `c = 32`) | zedc-solvers negsssp completeness tests | already there (each checked by hand) |
| b991293a4 | the citations point to lib.rs "References" | zedc-solvers lib.rs | already there |
| f9936c4fe | `ends` costs O(m log m) plus O(log w) floor sums; Eisenbrand and Rote | zedc-solvers twovar.rs `ends` | already there (doi:10.1007/3-540-45535-3_7, checked on Crossref) |
| f9936c4fe | the least `x` is open to the left when no bound closes it | zedc-solvers twovar.rs `least_x` | already there |
| c6969ca91 | the references of the crate (Lenstra, LLL, Megiddo, Goldberg, Thorup, Dinitz and Itzhak, Dijkstra, Bellman) | zedc-solvers lib.rs | already there (DOIs; marked not read where not read) |
| d3608d87b | Duong's paper and its lemmas | zedc-solvers negsssp.rs | already there |
| d5ae3f504 | 400 graphs miss the odd zero-weight cycle in about 1 run of 400 | zedc-solvers utvpi.rs `ANSWERS` | corrected: `0.984^400` is about `e^-6.4`, so about 1 run of 600; not relied on, since the built graphs give each answer |
| 745bf800f | a pass-by write costs one argument's entry, not the call's list | zedc-check check/mod.rs `set`, `Undo::Passes` | already there (a map by call span of maps by argument span) |
| d9495abf6 | phase 2's narrowing keeps a post-fixpoint | zedc-lattice iterate.rs `solve` | completed: `F_v(X) ⊑ X'_v ⊑ X_v` from the contract of `Lattice::narrow`, then monotonicity |
| e275c5f0b | the final Dijkstra on `r + 1` from `-phi` gives paths shortest in `w` | zedc-solvers negsssp.rs `run` | completed: `r = (n + 1)·w + phi(u) - phi(v)`, the label of a path, a tree path of at most `n - 1 < n + 1` edges, so the least label has the least `w`, and why `w` has no negative cycle there |
| 6c2c05101 | `apply_one` and `refuses` read a bound in O(1), not O(v a) | zedc-check walk.rs `apply_one` (the `at_of` map); mod.rs `sig.bounds.get` | already there |
| 6c2c05101 | the denotation of a bounds clause is linear however deeply clauses nest | zedc-check mod.rs `struct Denote` | corrected: the hash map `bound` is O(1) expected, the home's sorted sets O(log k), so O(size · log k) with no factor of the depth, plus the Make and And operations `Denote::ty` states |
| 1dd869737 | a fresh type variable name is tried once | zedc-types ty.rs `Scope` (F68); zed-kernel print/names.rs `fresh_name` | already there |
| fd98fb235 | `holds` costs the smaller of `binds` and `f` | zedc-types ty.rs `holds` | already there |
| fd98fb235 | `bound` copies no `binds` for a need | zedc-check mod.rs `bound` | completed: the three costs, each O(log b) per lookup, insert or removal in the `imbl::OrdMap`, none with a term in `b` alone |
| 15657d994 | remainders read class by class, `G <= 2d + 1` classes, `O(G n log n)` | zedc-preimage preimage.rs `split_residues`, `split_classes` | already there, see proofdoc2a (5b6845336) |
| 174c0f20b | a narrowing costs one origin, words only on a reported rejection | zedc-check mod.rs `Origin` (F80) | already there |
| 585e7f18b | the refused covers: DNF tautology (coNP-complete), Orthogonal Vectors | zedc-types ty.rs `covered` | already there (Frisch, Castagna and Benzaken; Williams; DOIs) |
| 585e7f18b | a bounded variable bound to several carriers fits at one place | zedc-types ty.rs `one_place` | already there |
| 63a6f9c4d | `@exact` enumeration searches only the constraints due, and is exact | zedc-preimage product.rs `enumerate_exactly` | already there, see proofdoc4b (06d34a210) |
| 78e5f708f | `learn` removes `r` disjuncts in `O(log r)` propagations, each removal proved | zedc-presburger presburger.rs `learn` | already there (the bounds without a point are those up to one, so the searches are exact) |
| 78e5f708f | `bounds_refute` is `O(n log n)`, and each `true` is a proof | zedc-presburger presburger.rs `bounds_refute` | already there |
| acc4f3aed | a bounded variable of the expected type is held rigid, for every carrier of its bound | zedc-types ty.rs `Cx::rigid` | already there |
| acc4f3aed | the printer is linear in the depth | zedc-types ty.rs `Ty::write` | already there |
| 0513b158e | `box_empty_in` reads each row once and finds crossing bounds in any order | zedc-presburger presburger.rs `box_empty_in`, `row_box_empty` | already there |
| 64781908f | `meet_within` leaves out a rigid variable each carrier of whose bound another result misses | zedc-types ty.rs `meet_within` | already there |
| 7498c2e7e | `is_perfect_power` doubles the precision at powers of two | zedc-int int.rs `is_perfect_power` | already there |
| 7498c2e7e | `v mod g` is the least class holding the points | zedc-zir canon/domain.rs `least_class` | completed: why `m \| g` for any class holding them, the modulus 0 case, and the fold from 0; two tests named |
| 7498c2e7e | the meet of two classes is an exact CRT | zedc-lattice lattice.rs `Congruence` meet | already there |
| b6d0a2eef | a lambda for a bounded parameter is checked at each carrier | zedc-check walk.rs (the generic route of `fit_lambda`) | already there |
| 16d8ce615 | BF-Dijkstra's round bound shows a negative cycle; the Bellman–Ford reference | zedc-solvers negsssp.rs `bf_dijkstra`, test `bellman_ford` | already there |
| 52e4b51fc | a rat literal is offered only the literals that are the same number exactly | zedc-check mod.rs `rat_forms`, `value_kept` | already there |
| 79885f50d | the index of arrows gives the verdict of every pair | zedc-types ty.rs `ArrowIndex`, `offered_keys` | already there (a closed type holds a scalar or bare atom only if it offers its key) |
| 889d3e94d | a shared row is replaced once, by address | zedc-types ty.rs `Replacer` | already there (the addresses are of rows the input holds, which outlive the walk) |
| 9111fb39d | `twovar` O(m log m) and exact | zedc-solvers twovar.rs | already there, see the 1ffeb360d and f9936c4fe rows above |
| 9111fb39d | the UTVPI test of Lahiri and Musuvathi | zedc-solvers utvpi.rs module doc | already there (DOI) |
| 9111fb39d | the simplex pivots by Dantzig's rule, then Bland's | none: store/simplex.rs became linear.rs in fb4b2f903 and holds no simplex | already there (no site left) |
| 9111fb39d | the Omega test decides exactly, splinters one level deep | zedc-presburger presburger.rs, exact/projection.rs | already there, see proofdoc4a (300df7ed3, 4e48ee579 rows) |
| 961b304c9 | related hubs settle in `O(k)` | zedc-check walk.rs (C26 note) | already there |
| a934e9cf8 | a signature's facts and digest are memoed once | zedc-types ty.rs `Sig::digest`, `Sig::facts`, `Sig::holds_needs` | already there, see proofdoc1b |
| a934e9cf8 | a message settles its type in the time of printing it; a class bound to a class is replaced at each depth | zedc-check mod.rs `settled`; walk.rs (F77) | already there |
| a934e9cf8 | `VarFacts::held` copies each variable O(log n) times over a nest | zedc-types ty.rs `VarFacts::held` | marked unproved: proved where the merged sets are disjoint; with shared variables a set can grow by one per insertion, so the open sub-case is a nest whose facts overlap at every level |
| e3b9b5c6b | a bounded variable no parameter holds stands for the union of its bound's carriers | zedc-types ty.rs `Sig::unheld` | already there |
| 01d71b2ea | disjuncts asked of the base by halves; the exact shadow with unit-equality substitution | zedc-presburger presburger.rs `disjunction_hulls` doc and the substitution doc | already there |
| 53d0c3177 | a cover takes only closed parameter types and costs linear time in the width | zedc-types ty.rs `covered` | already there |
| 63fa169e7 | an arrow that an argument fails by a decided check names no refused cause | zedc-check mod.rs `refused_among` | already there |
| 8f23b02b7 | `function_in` reads each type's functions, rows' memo and payloads once each | zedc-types ty.rs `Ty::function_in` | already there |
| 9147744bd | a leaf of several clean hubs, and a bound on a sum of names, settled where read | zedc-preimage product.rs (eager equivalence; `conjuncts::unit_sum`) | already there (each conjunct test O(log n)) |
| 9b7406051 | `meet_within` intersects results holding a function or a rigid variable, one pass from each end | zedc-types ty.rs `meet_within` (F82) | already there |
| c22a191c9 | a shared `Formula` node is read once per pass, a clone O(1) | zedc-presburger formula.rs, deep.rs module doc (S27, S31) | already there |
| c3044ee83 | rule 6 pass-by per atom: the atoms every arrow omits pass by | zedc-check mod.rs `Ck::refused` | corrected: the doc said "one set difference and one meet per arrow"; the code does at most one set difference per arrow and no meet |
| fec575742 | one bound check over every written type, each node read once | zedc-check mod.rs `Ck::bounds` | already there (the walk pushes each child once; a `Bounded` node is read whole by `kernel_type`) |
| 87bab4327 | live3: the box `24·A²·max(A, K)` keeps every integer point that matters | zedc-solvers live3.rs module doc | already there (Cramer: vertex coordinates at most `6·A²·K`, cone generators at most `2·A²`, Carathéodory three generators; checked by hand) |
| 87bab4327 | live3: the rows lie within `g + 25·(S - g)`, barycentric coordinates at least -6 | zedc-solvers live3.rs `simplex` | completed: the triangular `T`, the extents, the back substitution giving `\|λ1\| <= 4`, `\|λ2\| <= 2`, `\|λ3\| <= 1`, and why -6 gives exactly 25 |
| 87bab4327 | live3: the LLL point misses only when `r < (√7/2)·\|b3*\|`; the width below `75·√7` | zedc-solvers live3.rs `reduce` | completed: the inradius and circumradius in the form, the LLL inequality at `δ = 3/4`, Babai's bound, the dual functional of norm `1 / \|b3*\|` (LLL 1982, Babai 1986, DOIs) |
| 87bab4327 | live3: "fewer than 199" slices | zedc-solvers live3.rs module doc, `slices` | corrected: a width below 198.43 allows up to 199 integer values, so "at most 199"; nothing relied on the count |
| 6cc6d3efd | `odd_root_mod_pow2` is a bijection on odd residues, by Hensel, O(M(k) log p) | zedc-int int.rs `odd_root_mod_pow2` | already there |
| 6cc6d3efd | the bit bounds of `r^p` | zedc-int int.rs, the perfect power test | already there |
| 6cc6d3efd | the group fold: lower terms at most `(b^e/2)·b/(b - 1)`, the quarter bound for `b >= 3` | zedc-int int.rs, the group fold | already there (for `b = 2` the group is in fact at least `2^-(n-1)` of its top term, more than the `2^-n` stated; the stated bound holds) |
| 6cc6d3efd | `root_floor`: at least `2^127` exactly when `x >= 2^(127·k)`, and the bisection invariant | zedc-int int.rs `root_floor` | already there |

No code claim:
- zedc: 181885f72, 8c5ccccb9.
- zed-native: 181885f72.
- zedc-resolve: 51ae6534c, bea44d4a5, d18e52a0a.
- zedc-zir: 51ae6534c, bea44d4a5.
- zed-rt: 181885f72.
- zed-tools: 51ae6534c, bea44d4a5.
- zedc-int: fffe13699.
- moved: 26b4df164 (a doc of the ZIR number text), 2bf39d29e (one comment on a decorated
  literal), 1b531cd56 (the rule that an L1 port is `Lines`; the comment is gone since),
  7433e3145, ce1450451, cf099fcf2 (crate splits with no comment line), 5354b56d7 (the
  position of an unreadable file in its message).
- zedc-solvers: d80e81d08 (a type alias), 2b3e706f1 (searches moved to
  `zed_collections::search`, same contracts), 4c17c8e8f (dev-dependency features), 5168f5a37
  (a type alias), 6da69df6f (the shared interval append).
