# PRES-exact-cover: work in progress (2026-11-14)

Branch `wt/pres-exact`, based on 07f18406f. Starting point for PRES-pugh-exact-projection-research.
Logs of the runs below: /home/luke/Work/wt/pres-exact-logs (not in git).

## What the branch holds

- `crates/zedc-presburger/src/presburger/exact.rs` (new): `exact_each`, called from
  `project_each` on the solver's answer. It makes the projection exact by a model-guided cover
  (Monniaux 2010; Bjorner and Janota 2015): ask the solver for a value of the projected symbol
  `s` outside the answer so far; take a point; build a cell around it from the implicant of the
  formula at that point; add the cell's projection; repeat until no value is left.
  The cell is built from, in order: `along` lines; the implicant projected by `eliminated`, then
  `eliminated_whole` (every exact Fourier-Motzkin/Omega step, rows charged to the work count);
  `runs` (one stride atom, each value of it); the `fixed` fallback (8 values per question);
  `directions` (pairs of `s` with one other atom); `progression`; `joined` (keeps only rows
  connected to `s`). Residue questions cover strides; a refused question is skipped
  (`Err(_) => {}`).
- Temporary lines to remove before any merge: the `ZED_EXACT_OFF` check (exact.rs, about line
  108) and the `TMPDBG` timing trace (about lines 121-124). `EXACT_LIMIT = 20_000_000` is not
  calibrated against A99 (250 ms of predicted work, counted).
- `presburger.rs`: `eliminated_whole`; the `mod exact` wiring in `project_each`. The Omega
  flush-loop fix and its test `loose_pair_tests` are also here; they were merged to main alone
  (branch wt/omega-flush).
- `zedc-preimage/src/preimage.rs`: test `or_if_projections_keep_the_gaps_the_if_reading_shows`
  (FAIL-or-if-projection-not-exact). The "no longer exact, wider box" class (about lines
  14190-14224) is still there; it goes once the projection is exact.
- `tests/steps/l01_38_omega_test/bench/exact_cover.rs`: a benchmark, not yet compiled.
- exact.rs tests: 7 pass; `an_unbounded_conjunction_needs_one_cell` hangs (the blocker below).

## The blocker

On an unbounded set the cover does not end when no cell can cover a ray. Example (the
pendants formula, test `an_unbounded_conjunction_needs_one_cell`): `w == 2a - b`, `a <= -14`,
`w <= -29`, with strides. `eliminated` and `eliminated_whole` fail (coefficient 2 on `a`, the
step is not exact); `runs` gives None on an infinite range of the stride atom; `fixed` adds 8
values per question, so the loop never ends. The only direction that keeps the formula true
moves several atoms together, for example (w: -2, a: -1, c: +1); `directions` pairs `s` with
one atom only. Stacks sampled with gdb under zrun (gdbs.sh, gdbs2.sh, gdbs.out) show the loop
in the cover, not in the solver; perf is blocked (perf_event_paranoid = 2).

Two candidate in-cell steps (row PRES-pugh-exact-projection-research):
1. Pugh's exact projection of each implicant, with splinters and strides (Pugh 1991, 1992):
   the cell's projection is exact for any implicant, bounded or not, so one cell covers a ray.
2. A recession-direction step: integer directions in the kernel of the equations that keep
   every inequality (the recession cone of the implicant's integer hull), which extend a cell
   along the ray.

## The cover-on run (logsOn3, on3.log)

877 pieces of `zedc_presburger|zedc_preimage|l01_|m0_12`: 795 pass, 33 fail (rc 101), 50 time
out (rc 124). Three kinds:

1. Finer answers that tests pin to the old answer (update the test once the new answer is
   checked against the interpreter): l01_25 `exact` (`x*7 mod 10 == 3` now {9, 19, 29} exact);
   `ref_memo::*made_exact*` and `the_changed_answers_*_0`, `_3`; s22 `remainder_cases_*`
   (the box is now exact, a product of an x-set and a y-set, so `relation` is None and
   `stay_linear` panics with "a relation"); s22
   `a_split_by_remainders_is_given_up_where_it_cannot_be_exact`,
   `meeting_a_demand_with_the_hull_may_narrow_a_box_the_map2_cap_widened`,
   `remainder_reads_outside_a_split_have_their_preimages`; l01_38 `completeness` (likely
   {0, 2, 4, 6}), `omega::a_sum_of_forms_with_gaps_is_not_read`,
   `twin_definitions_are_merged_before_a_tied_projection`, `linked_nest`, `shared::a_shared_part_taken_out_narrows_a_projection`;
   l01_39 `scope_relations::deep_condition`, `families::projection_shortcut_cases`.
   Each needs checking one by one; some may be wrong answers, not finer ones.
2. A cover question refused where the hull had answered: l01_38
   `disj_groups::an_end_that_cases_bound_at_a_value_no_disjunct_gives_is_left_open`,
   `row_sums::the_sums_of_the_benchmarks_are_answered_at_small_sizes`; l01_39
   `refused::the_cause_of_a_refused_disjunct_is_returned`, `pendants::refused_projections_keep_the_box_*`
   (the refusal or its cause changes).
3. Time-outs (50): the pendants and random groups of l01_39, s22 chains and random terms,
   l01_25 `random`, `completeness`, `exact_oracle::*`, l01_39 `controls`, `scaling`, `nests`,
   `l01_39a_bit_words::shapes`, `m0_12_refusal_census::programs_11`, the zedc_preimage unit
   piece. The ones traced are the blocker above.

Unrelated: `l01_21_test_runner` fails on `rows::no_message_names_a_kernel_rule` (l08_02
COMPLETENESS.md) on main too.

Full list: `grep -E "rc=(101|124)" /home/luke/Work/wt/pres-exact-logs/on3.log`; each failed
piece's output is in /home/luke/Work/wt/pres-exact-logs/logsOn3/.
