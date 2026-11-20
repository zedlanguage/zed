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

Not started.

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
