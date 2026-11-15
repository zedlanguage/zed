# PRES-pugh-exact-projection-research: findings

Branch `wt/pugh-research`, worktree `/home/luke/Work/wt/pres-exact`. Research only: not for
merge. The `TMPDBG` lines, `ZED_EXACT_TRACE`, `ZED_EXACT_OFF` and `ZED_EXACT_METHOD` in
`crates/zedc-presburger/src/presburger/exact.rs` are debug switches and must go before any merge.

## What was built

The cover of `exact.rs` (from `PRES-exact-cover-wip.md`) asks the solver, for each value range
of the projected name not yet confirmed, whether it has a point, and answers inside a cell
around each point found. Three in-cell methods were compared, picked by `ZED_EXACT_METHOD`:

- **old**: the in-cell step of the WIP branch.
- **pugh**: Pugh's exact projection of each implicant (Pugh 1992, "A practical algorithm for
  exact array dependence analysis"): equalities removed by the mod-hat step, then the dark
  shadow plus the splinters for each inexact elimination; the strides that remain are kept as
  residue sets of the projected name.
- **rays**: the recession directions of the cell. Where the cell has a ray along the projected
  name, the values along it are taken by their stride without further questions.

Each method was run first with no fallback (a refused question refuses the whole projection),
then with the **fallback**: a refused question, a tail of holes with no end, or the work limit
keeps that piece unconfirmed, so the answer is the solver's set narrowed by the pieces proved
empty. With the fallback the answer is never wider than main's, and is marked exact only when
nothing was kept.

## Scored table

Measured on the 82 failing pieces of `PRES-exact-cover-wip.md` (83 less
`l01_21_test_runner`, which also fails on main), with `tools/run_tests.sh --only` at the load
of the day (load average 50 to 78 on 32 cores); time-out is the per-piece limit of run_tests.

| Method | Measured result (82 pieces) | Score 0–10 | Reasoning |
|---|---|---|---|
| pugh with fallback | 52 pass, 27 fail, 3 time out (rerun with the pins updated: 59 pass, 20 fail, 3 time out, every failure in a kind triaged below) | 7 | Most passes. No refusal where main answered. The remaining failures are finer answers pinned to the old ones, and time-outs caused by solver questions, not by the method. Scaling 5.0x and 8.1x (limit 10.5, goal 9). |
| rays with fallback | 48 pass, 27 fail, 7 time out | 5 | Same fallback, fewer passes, more time-outs. Fails the unit test `an_unbounded_conjunction_needs_one_cell` (needs more than one cell where Pugh needs one). Scaling 5.8x and 8.0x. |
| pugh, no fallback | 38 pass, 41 fail, 3 time out | 3 | Every refused solver question refuses the projection, where main answered with its hull: 14 more failures than with the fallback (kind 2 below). |
| old (WIP step) | 3 pass, 31 fail, 48 time out | 1 | Most pieces time out; it takes more than 60 s on `an_unbounded_conjunction_needs_one_cell`. Scaling 6.0x and 8.1x where it finishes. |
| baseline (WIP branch as found, on3) | 0 pass, 33 fail, 50 time out | 0 | The state the row started from. |

No method passes all 82 pieces, so the stop rule of the row (one method passes the 83 pieces
and the scaling limits) is not met. Pugh's projection with the fallback is the best of the
three; what blocks it is the cost of single solver questions (below), not the in-cell method.

## The stuck pendants case

All three methods answer `b` in `[-4, 15]`. Listing the points shows that every `b` in
`-4..=15` has a point, so `[-4, 15]` is the exact set. None of the methods proves it: the
solver refuses (`Growth`) the question for the piece `-4..=0`, and the fallback keeps that piece
unconfirmed, so the answer is exact in value but not marked exact. Questions asked: pugh 2,
rays 10, old 4; each a few milliseconds. The unit test
`the_pendants_part_of_row_3_projects_b_to_at_most_15` asserts the set `[-4, 15]`.

## Triage of the three failure kinds

### Kind 1: finer answers that tests pin to the old answer

Each was checked by hand or by listing points before the test was changed.

Changed on the branch (all pass now):

- `l01_25_preimage_catalog::exact`, `x * 7 mod 10 == 3`: `{9, 19, 29}` (7x ≡ 3 mod 10 gives
  x ≡ 9).
- `l01_38_omega_test::completeness`: `x = 2y` with its bounds gives the even values of `0..=6`.
- `l01_38_omega_test::omega::a_sum_of_forms_with_gaps_is_not_read`: `[0..=5]` (`x + y` is never 1).
- `omega::twin_definitions_are_merged_before_a_tied_projection`, case 1185: `{-9}`. Listing
  `i` over `-40..40` gives only -9; below -40 this rests on the cover's own proof.
- `l01_39_scope_relations::deep_condition::a_branch_with_no_point`: the second branch is empty.
- `l01_39_scope_relations::families::projection_shortcut_cases`, C4: `x` in `{1, 4, 7}`.
- `l01_25_preimage_catalog::s22::meeting_a_demand_with_the_hull_may_narrow_a_box_the_map2_cap_widened`:
  `{-10} | [1, 3] | {10}` (both arms are `2x`; worked by hand).
- `s22::a_split_by_remainders_is_given_up_where_it_cannot_be_exact`, the wide case: every even
  value of `10..=1000` (an odd `i` gives 0, outside the demand `10..=2000`).

Finer, confirmed or partly confirmed, test not yet changed:

- `ref_memo` (5 tests) and `shared::a_shared_part`: counts of cases made exact change.
- `s22::remainder_cases` (6) and `remainder_reads_outside_...have_their_preimages`: fewer
  points, holes kept.
- `split_pieces` "ten true": `(-inf, -212] | {-207} | {-202}` where it was `(-inf, -202]`,
  confirmed with floor mod; needs `touched_cases.txt` regenerated.
- `two_eq_case`: finer than before, still wider than the oracle.

Not confirmed:

- `m0_12_refusal_census::programs_11`: one warning fewer, "Cannot find exactly which values
  meet one side of a `||` here" in `a_refused_projection_onto_one_name_names_its_bounds`,
  while the `z1` and `z2` warnings of the same program remain. The test of those warnings
  passes. Whether dropping the `||` warning is right is not checked; the snapshot is left
  failing.

Test design questions (the cover removes what these tests measure):

- The two s22 tests above compare the transfer with the transfer before. The cover runs under
  both, so both are exact and the contrast is gone; `split_relation_exact` needs an inexact
  answer and was dropped for the wide case, and `Diffs` now counts no case made exact. If the
  cover stays, these tests need a new purpose or a switch that runs the transfer without it.
- `stay_linear` (2 tests) panic with "a relation": the box is now exact, so no relation exists
  for the test to time.

### Kind 2: questions refused where the hull had answered

Gone with the fallback. Now passing: pendants (7), refused (2), scaling, disj_groups (2),
linked_nest, `l01_25_preimage_catalog::completeness`.

### Kind 3: time-outs

All measured ones are caused by single solver questions, not by the in-cell method:

| Piece | Cover off | Cover on |
|---|---|---|
| `chains_on_two_inputs_50_51` | 0.6 s | more than 60 s; one question runs more than 25 s |
| `remainder_reads_outside_a_split_at_their_corners` | 0.9 s | more than 60 s |
| `zedc_preimage` `summaries_read_again`, seed 7776978274844439420 | 9.1 s | 30 s pugh, 38 s old (limit 20 s): 24 covers, 183 questions, about 160 ms each on formulas of about 97 constraints |
| `deep_condition::the_search_for_a_point_tests_each_part_...` (a count, not a time) | heavy d=5: 79 parts, d=60: 849 | d=5: 284, d=60: 3089 (limit 48 per level) |

The `deep_condition` count rises because each cover question runs the solver's point search
again, and `parts_tested` counts every search. Whether those searches should count against the
bound of that test is a question for the test, not for the method.

## The cost of one solver question (the main finding)

The cover charges each question `size + 2` work units against `EXACT_LIMIT` (20M), but one call
of the solver's `satisfiable` has no counted bound. One question takes from 40 ms to more than
25 s. The gdb stack of the long one: `exact::cover → satisfiable → satisfiable_written →
or_old → satisfiable_named → satisfiable_inner → probe_to → probe_kept_status →
search_by_halves → pick_taking → pick_by → by_halves → Linked::of / canonical /
stable_colors`. So the A99 bound (refuse past 250 ms of predicted work) does not hold for a
whole cover today.

Proposed fix: give the solver a counted work budget, charged in `search_by_halves` and the
probe code, and pass the cover's remaining work into each question. A question that runs past
it refuses with `Refusal::Work`, and the fallback keeps the piece. This turns every kind 3
time-out into a kept piece (main's answer for that piece) at a bounded cost.

## Question for the author (A99)

With the fallback, a refused or over-budget question no longer refuses the projection: the
answer is main's set narrowed by the pieces proved empty, marked inexact. Is it right under
A99 for the cover to give up silently on a piece and keep main's answer, or should the work
limit of the cover be reported to the user as a refusal?

## Scaling

Bench `tests/steps/l01_38_omega_test/bench/exact_cover.rs`
(`the_cover_is_of_order_n_in_its_answer_and_in_its_questions`), T(8n)/T(n):

| Method | evens, n = 250 to 2000 | padding, n = 25 to 200 |
|---|---|---|
| pugh | 5.0x | 8.1x |
| rays | 5.8x | 8.0x |
| old | 6.0x | 8.1x |

All under 9.

## Next steps, in order

1. The solver work budget above; then rerun the 82 pieces.
2. Regenerate or repin the kind 1 tests not yet changed, each after checking it.
3. Decide the s22 and `stay_linear` test design questions.
4. Check the `programs_11` census change.
5. Remove the debug switches; cross-review (hard-algorithm rule) before any merge.
