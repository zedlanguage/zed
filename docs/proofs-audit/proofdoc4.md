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
to 65, base commit 57ba7215b. For each entry the whole message and the whole diff under
`crates/zedc-presburger` were read, and each claim was checked at the code that relies on it
on main today.

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zedc-presburger | 65 | 68 | 46 | 15 | 3 | 0 |

Of the 68, four are counted in no column: they are no longer relied on, since the code they
described is gone: the race's bound (24981fcda), a research-branch behavior (4033def30), the
foreign-factor rule of `products` (e8fea7860) and the batch and single hulls agreeing
(3e3db6907).

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

No code claim: zedc-presburger 7bfd6bba8 1faf391fd 53b114449 65446a377.

Not read: 8e3867d18 94f38f6d3 96a4e186b 9758548e8
9e786fe17 a1a2a3c63 aa8366a07 ec537c0b1 ed1f1be11 f0186c022 f0ce6ac5e f4c033ccd f548497ad
fb9b82a6a 030a2d36d 136017dd7 28a3d9acb 32acdc5eb 384b173ac 4e48ee579 54ddb1f80 5dfd87a78
6e72af6bd 711b27b81 72d5f383f 7d23ca0c7 7dda7ea0d 7f771ec77 83ebfff6e 8575c70cc 8590c4d2b
889492a23 9f8961b3b a3273dbda a54f1b103 aabf487cc ac67403b3 ace60e16b b2ba71b22 c4964f39a
d73f3c8e1 f060dbed1 f835ff861 (later parts of this section).

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

Not started.

## proofdoc4d: zedc-check

The 153 zedc-check entries of /home/luke/Work/wt/proofdoc4-lists/d.txt, in list order. Each
entry's message and its whole zedc-check diff were read, then each claim's site as it stands
on main; the sites were read on origin/main 1915d2375 and rechecked at each merge's rebase.
Claims in other crates are listed and not counted; they belong to the helper of that crate.

| Crate | Entries read | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|---|
| zedc-check | 75 | 137 | 98 | 27 | 3 | 9 |

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
b991293a4 `zed_graph::UnionFind` (zed-graph).

Claims gone from main, not counted: af8174807 `call_records` (replaced by `record_call`
marking the call placed), 275d434e7 `env_config` and `ZED_DISABLE_D` (E was removed in
f83194447). ee79685e4 `fold_dir_end`'s round bound was not read again: it is known false
(FAIL-fold-rotating-tuple-rounds).

No code claim: b2ba71b22 (test helpers), c50a8965b (message texts), fe770de11 (in zedc-check
only a test helper calls `zed_numtheory::is_prime`), 275d434e7 (its one claim is gone),
97beabefa (its one claim moved to zedc-types), 718e9ecda (message text).

Not read: bad0d2e86 bd3c630e0 bea44d4a5 c289ffeca d11373afd d59b4756e d83518eb5
d9d8729bb da0895a4f df8cea00b e2e0e0612 e6dfb6877 ebd6faee5 ef56f8c84 f240a5462 f38d90beb
f6c6b1f99 f79ee52bf f8f4ddabb f923d44b9 fffe13699 009e52933 00a508032 019b3519b 06d1dc49c
0b05cc8cf 0cbb40ab4 131d7f7fd 19514ef8c 1a19cae20 205591658 2059d260b 256d0fc5d 29bf6b297
30b46ffdb 35f48821c 3b7276f38 3e597380e 3fd923c4a 47681f229 47f742016 480291d0e 4abfd2ae1
4ce8104bb 4e55a11ba 51ae6534c 5a5ef9670 5ccb21f3f 61590f5c5 620307b4c 650ec1e0a 65fe79c41
695a25e74 6a1038700 788205304 7b5ff433f 7efc39992 807ba2009 81f3d8487 8824fb555 893f60ac7
929e7e04a a16eb1e6e a7dba5382 aea083d67 af7540d08 b3c21a87e b5444f558 b6b810dec c8fa18353
d18e52a0a dd8b42f68 e2ef08f39 e36d97342 e8755d8a1 eaef33ced eb156f28d fbb2b68aa

## proofdoc4e: zedc-presburger, last 90 entries

Not started.

## proofdoc4f: zed-kernel, zedc-elab, zedc-base

Not started.

## proofdoc4g: the moved commits, zedc-solvers, zedc-int, the small crates, `type_var_form`

Not started.
