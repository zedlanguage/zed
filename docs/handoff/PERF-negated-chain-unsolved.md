# PERF-negated-chain: cases not yet solved (handoff)

Written 2026-11-11 by the coordinator of PERF-negated-chain-xr, after the author stopped the
cross-review during round 7 (order of 2026-11-11 16:50). This file lists every case the
review did not solve, what was measured, what was tried and why it failed, and the methods
still open. The merge candidate is the branch this file is committed on
(`wt/perf-negated-chain`); everything below is about what that candidate does not do.

Status words: **confirmed** means the coordinator reran it (the file holding the output is
named); **seat only** means a reviewer measured it and the coordinator did not rerun it;
**inferred** means it follows from reading code, not from a run.

## 1. Where everything is

- Review records, copied to disk (the scratch directory was on tmpfs):
  `/home/luke/Work/wt/pncx-scratch/xr-archive/`.
  - `HISTORY.md`: issue table I1.1 to I6.17, one line per round, reviewer settings.
  - `ERRORS_CLAUDE.md`, `ERRORS_CODEX.md`, `ERRORS_GEMINI.md`: reviewer errors per round.
  - `archive/r1/` to `archive/r6/`: `BRIEFn.md`, `METAn.md` (coordinator's check of each
    claim), each seat's report `Rn_<SEAT>.md` and diff `Rn_<SEAT>.diff`.
  - `archive/r7/`: `BRIEF7.md`, both seat directories as left when stopped
    (`seat-claude/`, `seat-codex/`, with `R7_CLAUDE.md`, `R7_CODEX.md`, `R7_CODEX.log`,
    `logs/`, scripts, controls), and both tree diffs `tree-pncx-<seat>-end.diff`.
  - `library/`: probe sources (`easy_variants.zed`, `seed15.zed.txt`, `sign12.zed`,
    `r6-end/{k33,prism,wheel,remainder-a,remainder-z,n1-p40}.zed`, `r5-end/case56-bare.zed`,
    `r5-end/rename-grid.zed`, `big-literal/`), answer-log tools (`cmplog.awk`,
    `cmplog-fn.awk`, `pncx-log-patch-r6.diff`) and fetched papers (`papers/r4-*`, `r5-codex`,
    `r6-*`; round-7 seats' papers under `archive/r7/seat-*/library/papers`).
  - `verify/`: the coordinator's reruns per round.
  - `LEFT-OUT-over-20MB.txt`: the 120 files not copied (answer logs and raw test dumps over
    20 MB; all reproducible with the commands in `HISTORY.md` and `METAn.md`).
- Local branches (not pushed) holding seat trees for porting:
  - `pncx-r7-codex` (ab0c8ceb5, on c803059a): Codex's round-7 tree as stopped: the same port
    as the candidate, plus cycle-square witness (R7-CODEX-3), independent check of unit
    affine images (R7-CODEX-5), compressing `UnitUf::get` (R7-CODEX-1), the 46 s test split
    into nine (R7-CODEX-4), and the wide-alias test (R7-CODEX-6).
  - `pncx-r7-claude` (aeb9dcacd, on c803059a): Claude's round-7 tree as stopped, before
    formatting; candidate commit 24eb89090 is this tree formatted, and 4b98f90de follows it.
  - `pncx-r6-codex` (3cb55ee5a), `pncx-r5-codex`, `pncx-r4-codex`: earlier Codex trees.

## 2. What the merge candidate holds

Branch `wt/perf-negated-chain`, on origin/main 72fd42085, not pushed or merged. Commits, oldest
first:

| commit | content |
|---|---|
| bd990e301 | Claude's round-3 method (the one-variable modular path) |
| 37d389e74, 451acbc22, deb759422 | Claude's round-4, -5 and -6 changes, each checked by the coordinator (`archive/r4..r6/METAn.md`) |
| 24eb89090 | Claude's round-7 tree as stopped, formatted: port of Codex's round-6 parts (Bernstein coprime base, half-GCD coefficients, prime-power consolidation, bipartite / Brooks / universal-vertex / preferred-value graph witnesses in `modular/brooks.rs`, empty shared bound); I6.3 span-key remainder choice with a second run on a tie; I6.11 path compression in `UnitUf::find` and `flatten`; the step-1 worklist (R7-CLAUDE-1); tests `modular/r6_tests.rs`, `modular/r7_tests.rs` |
| 4b98f90de | coordinator: a last run with the round-6 remainder choice when the others refuse (U4) |
| f7b33ab90 | coordinator: clippy -D warnings clean (no behavior change) |
| (this file) | the handoff |

Tests (all by the coordinator, `tools/run_tests.sh --no-doc`, each piece under `timeout 60` in
`zedtests.slice`, groups `l01_38_presburger`, `zedc_presburger`, `l01_39_reduced_product`,
`l01_25_preimage_catalog`, `zedc_preimage`; outputs in `verify/r7/<dir>/groups/run.txt`):

| tree | pieces | failed | load | dir |
|---|---|---|---|---|
| origin/main 72fd42085 (baseline) | 698 | 0 | 15.85 to 41.83 | `main` |
| 24eb89090 | 732 | 1: `one_scope::one_variable_modular_formulas_match_enumeration`, 70 refused, limit 64 (U4) | 9.6 to 41.83 | `review` |
| 4b98f90de | 732 | 0 | 6.16 to 8.81 | `review2` |
| f7b33ab90 | 732 | 0 | 3.47 to 10.81 | `review3` |

The 34 pieces more than main are the tests this branch adds. `cargo fmt --all --check` passes;
`cargo clippy -p zedc-presburger -p zed-tests --all-targets -- -D warnings` passes on f7b33ab90
(24eb89090 had 35 clippy errors, which f7b33ab90 fixes). No doc comments were added by the
wrap-up commits, so the doc check was not run.

Negative controls on 24eb89090, each run once (`verify/r7/control/`):

- I6.3: the remainder choice reverted to round 6's `Atom` order: `remainder_alias_answers_do_not_depend_on_names`
  fails, rc 101, 877 answered, 696 differ; `remainder_alias_names_keep_the_same_answers` fails,
  rc 101 (17:00, load 36.7).
- I6.11: the two path-compression lines removed from `UnitUf::find`:
  `r6_tests::pncx_affine_alias_chain_scale` fails, rc 101 (17:01, load 32.5; the ratio was not
  captured).

Tests left `#[ignore]` as open, with the reason in the source: `pncx_common_factor_scale`
(U1), `pncx_fibonacci_scale` (U2), `remainder_alias_answers_do_not_depend_on_names` (U4).

Not done for round 7: the answer log (`library/pncx-log-patch-r6.diff`, compared with
`cmplog.awk` against `library/r6-end/answers-c803059a.log`). Rounds 4 to 6 each had 0 lost and 0
changed answers. Round 7 and the wrap-up commits have no answer log, so a lost or changed
answer outside the five groups would go unseen. Run it first in the next round.

## 3. Unsolved cases

Each case: the input, the measurements, every method tried, the methods still open, and the
reviewers' disagreements. "Limit" is the scaling test's bound for 8x input.

### U1. Shared-factor preparation (coprime base) is above the limit

- Input: test `presburger::modular::r4_tests::pncx_common_factor_scale` (modular.rs, ignored
  with "open: R7-CLAUDE-3"): moduli sharing factors, 512 to 4,096 moduli.
- Measured: 21.7x instructions for 8x moduli, limit 11.7 (round 7, Claude, seat only, load
  11.5); 21.5x (round 6, Codex, confirmed failing in verify/r6/codex/groups), 21.81x
  ("preparation" axis, round 7, Codex, seat only). The whole-formula axes pass after the
  port: crtshared 11.4x (Claude r7) and 10.42x (Codex r7), shared formula 11.1x and 11.03x
  (seat only; the coordinator's round-6 rerun on Codex's branch gave 11.5x and 11.4x).
- Cause (round 7, Claude, seat only, `archive/r7/seat-claude/logs/t1-common-parts2.txt`): at
  n = 512 to 4,096 the input has 5,962 to 61,938 bits (10.4x for 8x moduli, so the axis in
  moduli is not the axis in bits). Remainder tree 1.72M to 63.7M instructions (37x), product
  tree 0.17M to 3.4M (20x), running gcd 0.09M to 0.78M (8.8x). One product of the two top
  nodes: 19.4k to 850k instructions (44x for 10.4x bits). The kernel's product (num-bigint
  below its transform crossover) and the division built on it are near quadratic at 500 to
  1,000 words.
- Tried:
  - pairwise gcd, k(k-1)/2 calls (round 2, all seats): quadratic (I2.6).
  - pairwise-coprime fast path (round 3, Claude): 8.25x when the moduli are coprime; shared
    factors still quadratic (I3.4).
  - Bernstein 2005 coprime base (round 3 Codex 19.5x; round 3 Gemini 20.3x; round 6 Codex
    11.5x on crtshared, 21.5x on preparation alone; ported in round 7).
  - half-GCD coefficients and prime-power consolidation (round 6, Codex; ported in round 7).
- Open methods:
  - (a) a kernel product of O(M(N)) = O(N log N) at these widths (transform product with a
    lower crossover, or Toom-3 with scratch allocated once); then the base costs
    O(M(N) log k), about 17x for 10.4x bits by Claude's estimate: still above 11.7 if the
    axis stays in moduli.
  - (b) state the axis in input bits and accept N log² N for this preparation. Needs the
    author: it changes the rule the test encodes.
  - (c) skip the coprime base when every modulus fits in a word. Claude calls this a size
    switch, which the standing rules ban; whether "fits in a word" is a structural fast path
    (allowed) or a size switch (banned) is an open question for the author.
- Disagreement: none on the cause. Claude (round 7) argues no product-tree method can meet
  11.7 on this axis at these sizes because Bernstein's bound is N (log N)^O(1); Codex
  (round 7) reports the same numbers without that argument.

### U2. Fibonacci CRT bits: allocation and work above the limit

- Input: test `presburger::modular::r6_tests::pncx_fibonacci_scale` (ignored, "open:
  R7-CLAUDE-4"), and the axis `crt_bit_axis` of the hand-run binary `pncx_probe` (zed-benches,
  `PNCX_SIZES=... pncx_probe crt_bit_axis`; moduli of 2,844 to 22,750 bits, 5,000 to 40,000
  steps).
- Measured: 18.5x instructions and 18.3x bytes for 8x steps (round 7, Claude and Codex, seat
  only, load 11.5 and 15); round 6 rerun by the coordinator: 22.3x (Claude's tree), 18.4x
  (Codex's), `library/r6-end/axes.txt`.
- Cause (round 7, Claude, seat only, `logs/t7-mul.txt`): one num-bigint product of two
  w-word numbers allocates 1,472 to 63,456 bytes for w = 44 to 355 (43x for 8x width, about
  w^1.8) and costs 16.8k to 366k instructions (21.7x). The half-GCD makes O(log n) levels of
  products, so the product's growth is the whole growth.
- Tried: Stein's binary gcd (num-bigint 0.4.8, round 5 reading); Euclid with explicit
  coefficients (round 6, Claude, 22.3x); Stehlé–Zimmermann binary recursive half-GCD (round
  6, Codex, 18.4x; ported in round 7).
- Open methods: the same kernel product as U1(a), with scratch allocated once per call;
  expected O(M(B) log B) for B bits. Codex (round 7) notes this is not O(B log B) and makes
  no claim that it would meet the limit.

### U3. Affine alias chain with one wide written offset (bit cost of path compression)

- Input: test `pncx_wide_affine_alias_scale` and axis `pncx_wide_alias_axis` on branch
  `pncx-r7-codex` (`modular/r6_tests.rs`, about line 944): n aliases with small offsets and
  one offset `2^(64n)`; input O(n log n + n) bits.
- Measured (round 7, Codex, seat only, load about 15): n = 128 to 1,024: 18.11M to 248.47M
  instructions (13.72x) and 7.96M to 371.64M bytes (46.66x); limit 12.6.
- Cause (Codex, proved by a storage argument): compression writes each atom's offset to its
  root; with the wide edge last, n offsets of about 64n bits are materialized, Ω(n²) bits
  even when only a Boolean is wanted.
- On the candidate: confirmed by the coordinator at 17:02 on 24eb89090 (load 24.3), with Codex's `wide_alias_chain` generator and `pncx_wide_alias_axis` test appended for the run only (not in the candidate): n = 128, 256, 512, 1024 (offset 8,193 to 65,537 bits) gives work 17.08M, 40.23M, 95.40M, 245.52M (14.4x over 8x n) and bytes 7.74M, 27.23M, 101.60M, 391.91M (50.6x over 8x n, about n^1.9). The defect is present on the candidate. Output: verify/r7/control/wide-alias-candidate.txt; test text: verify/r7/control/wide-alias-tests.rs.
- Tried: path compression in `get` (Codex r7) and `flatten` plus a compressing `find`
  (Claude r7) both fix the parent-visit cost (I6.11: 61x to 8.0x) and both keep this defect
  (inferred for Claude's from the same compression of offsets). Union by size alone does not
  avoid it (Codex, argued).
- Open methods: keep offsets relative to the parent and never write a composed offset to a
  node (union by size, depth O(log n), offsets summed on demand), and rewrite rows by
  differences of potentials rather than per-atom absolute potentials; expected cost
  O(n log n) parent visits and O(B log n) bits per row read, B the widest written offset.
  Not designed in detail by either seat.

### U4. Remainder choice reads names (I6.3): name-independence and answers conflict

The case: a row `x = m q + r` whose two unit terms are both bounded to less than a period, so
either can be read as the remainder. Minimal program pair (I6.3, round 6,
`library/r6-end/remainder-{a,z}.zed`): `ra(x, a) = a == x mod 101 && C(x)` gave `Err("refused")`
while the same with `z` for `a` gave `Ok(true)`. The family is generated by
`remainder_alias_case` in `tests/steps/l01_38_presburger/one_scope.rs` (1,000 cases, every
second one tied, eight namings, both question orders).

Measured on the candidate base 24eb89090 (round 7 as committed), all by the coordinator,
outputs under `verify/r7/` of the archive:

| remainder choice | 5,000-formula enumeration (sat / empty / refused) | name test: answered, differ | file |
|---|---|---|---|
| round 6: larger `Atom` is `r` | 4277 / 712 / 11 | 877, 696 | `refused/i63-old-rule-full.txt` (17:17, load 9.4), `control/i63-control.txt` (17:00, load 36.7) |
| Claude r7: span of exactly one period, else wider; tie flipped in a second run | 4245 / 685 / 70 (limit 64: the test fails) | 908, 0 (seat only); the name test passed in the 24eb89090 group run | `refused/candidate.txt` (17:13) |
| **candidate (4b98f90de)**: Claude r7, then a third run by `Atom` order when the first runs refuse | 4277 / 712 / 11 | 911, 476 | `fallback/*.txt` (17:18, load 13.1) |

- "Differ" means answered under one naming and refused under another; no case gave two
  different answers (the test's own assertion on wrong points did not fire).
- The 70 refusals of Claude's rule alone are the 11 of round 6 plus 59 more (case numbers in
  `refused/candidate.txt`; round 6's 11 in `refused/r6.txt`: 292, 371, 974, 1965, 2209, 2937,
  3205, 3595, 4427, 4584, 4949). Claude's round-7 seat never ran this test; the coordinator found
  the failure in the wrap-up group run (one piece of 732 failed, `review/groups/run.txt`) and
  confirmed the cause by restoring the round-6 rule alone (11 refused, the same 11).
- Codex found the same conflict in round 7 (R7-CODEX-2): its structural-only rule gave 118
  refusals (`archive/r7/seat-codex/logs/enum-initial.txt`); its fallback to the previous rewrite
  gave 11 (`enum-fallback.txt`). Its name test is a different, smaller grid (90 functions) and
  passes; whether its fallback keeps Claude's 1,000-case test at 0 differ was not measured.
- The candidate takes the fallback because it is no worse than round 6 on either count and
  better on names (476 against 696 differ). `remainder_alias_answers_do_not_depend_on_names` is
  marked `#[ignore]` with this explanation; `remainder_alias_names_keep_the_same_answers` passes.
- Left (Claude r7, Codex r7, by reading): with several tied rows the second run flips all ties
  together, so not every combination is tried; `rem_defs` keeps whichever row comes first when
  two rows define the same root (R7-CLAUDE-2, not finished).
- The real question for the next round: why does the span-key reading lose 59 answers that the
  `Atom`-order reading finds? Both readings are exact, so the loss is in a later step that
  handles one orientation of `x = m q + r` better than the other. Find that step on a few of the
  59 cases (start with case 101: `x >= -8 && x <= -1 && ...`, brute point -2) and make it
  orientation-free; then the name-free choice needs no fallback and both tests pass.
- Open methods: (1) the above; (2) a choice from a name-free key per row (coefficients and
  bounds, sorted), ties broken by a canonical order of the formula's rows, with the second run
  per tied component instead of all ties at once; expected O(n log n). (3) Try both readings of
  every both-bounded row (exact, but 2^k runs for k rows: refused as a method by the no-threshold
  rule unless k is bounded by structure).

### U5. Easy inputs still refused

All are answered by the general path or refused by it; no wrong answer has been found.

| input (source) | truth | status on the candidate | tried |
|---|---|---|---|
| e4, e5 (`library/easy_variants.zed`) | empty (Codex r6 count, Claude r6 agrees) | `holds` refused both orders, `fails` true (Codex r7, seat only, 486.7 ms and 76 ms) | separate-pair witness (r2 Codex), graph witnesses (r5, r6 Codex): do not apply; a short bound couples otherwise independent CRT components |
| seed 15 p4 (`library/seed15.zed.txt`) | true/true by bounded enumeration | refused (Codex r7, seat only) | lower-bound witness (r4 Codex) answers q and p3, not p4; residue interval projection incomplete |
| 11 enumeration cases of `one_scope::one_variable_modular_formulas_match_enumeration`: 292, 371, 974, 1965, 2209, 2937, 3205, 3595, 4427, 4584, 4949 (I5.14) | per case in the test | refused (Codex r7, `archive/r7/seat-codex/logs/enum-fallback.txt`) | 974 and 4949 were answered only under the base names before I5.1 and are now refused under every naming (cost of name independence, I5.14) |
| planted 3-SAT image, v = 7, c = 30 seeds 2, 5; c = 60 seed 1 (I4.14; generator in `archive/r4/R4_CLAUDE.md` T5) | true (c = 30), false (c = 60) | refused (round 4 rerun; not rerun since) | none; I4.21 shows the general family is NP-hard |
| n1-p40: `x < 2^(2^40) && x >= 0` (`library/r6-end/n1-p40.zed`) | true for every x >= 0 | refused (I6.4, confirmed r6) | building the power (Claude r6) runs out; Codex r6 reports powers unbuilt but does not decide |
| 77 shift cases (I6.2, Claude r6 T1): a shift or reflection written into the formula moves the coordinate | answered under one writing, refused under another | seat only | needs a coordinate invariant under every shift (a canonical rotation per coprime base); Claude found no O(n log n) one when the per-base data has symmetries |
| square of a cycle on 3n vertices (I6.8) | colorable when 3 divides the length | refused on the candidate; answered on `pncx-r7-codex` (R7-CODEX-3: 8.35x at 4 to 64, seat only) | Codex's recognition from one degree-4 vertex's triangles, O(v + e) |
| random 3-SAT image v = 200, c = 800 (I4.12) | unknown | no answer in 60 s, no message (r4); Codex r5: the time is in the probe's residue search, `decide` returns Shadows in 2.86 s (seat only) | Euclidean inverses in the probe (Codex r5, branch) |

Open methods: bit-length comparison of a kept power against every other bound in the
formula (n1-p40), expected O(written size); a witness that searches one CRT component under a
short bound by the bound's own period (e4, e5); the cycle-square port from `pncx-r7-codex`.

### U6. Empty answers are not checked in production

- An Empty (unsatisfiable) answer from `solve_modular` is checked only in tests (I2.12,
  I3.8, I4.13, I5.12, I6.13). With the I2.1 bug reintroduced, production returns a wrong
  answer with exit 0 (Claude r6, R6-CLAUDE-5, seat only).
- Tried: Gemini r3 `cert_check` for every Empty answer (accepted: catches I2.1 where other
  tests miss it), but it stops the compiler with `assert!` (I3.18, against the author's
  decision that the compiler is free of stops); Codex r7 (branch `pncx-r7-codex`,
  R7-CODEX-5) checks unit affine images independently and returns None on failure, which
  catches I2.1 in production (seat only), O(S log S); other Empty derivations unchecked.
- Open: a certificate per Empty derivation (residue-set images, CRT merges, bound
  intersections), each checked by a primitive that does not call the code it checks, and a
  None on failure. Claude's r6 design (walk-level certificate, `archive/r6/R6_CLAUDE.md`) and
  Codex's per-primitive check differ in where the check sits; not settled.

### U7. No definition of the refused class

- Graph 3-coloring and 3-SAT reduce to one-variable residue formulas (I4.21; Deppert, Jansen
  and Klein, arXiv:2002.07746: plain conjunctions of interval residue conditions with
  1 <= x <= N are NP-hard). Small easy members exist in every syntactic class found so far
  (kc, planted v = 7, K3,3), so a syntactic refused class also refuses easy inputs (I5.9).
- Disagreement: Claude (r5) says no polynomial structural test can separate them; Codex (r5,
  r7) says this is not proved without a definition of individual hardness. Not settled.
- Open: the user message for a refused input names the moduli read (I5.10, done for one
  variable); a precise class is still needed for the "refusal only for pathological cases"
  standard.

### U8. Older items not rechecked in round 7

Open in `HISTORY.md` and not rerun after round 6: I3.3 (segment walk worst case O(R n),
Stage C up to O(n² log n) at one node, by reading), I3.12 (Step 8 intersects bounds Ω(k²)
times, by reading), I4.9 (crt bytes 4.96x per doubling at 16,384), I1.4/I1.9 (class handed
to main). I4.2 (main itself became coarser between 4777a33e and 9bbeb1ff) is outside this
review and was reported to the author.

## 4. Literature collected

Papers are in `xr-archive/library/papers/` (and `archive/r7/seat-*/library/papers`):
Bernstein 2005 (coprime base); Stehlé and Zimmermann 2004 (binary recursive gcd);
Möller 2008 (half-GCD); Deppert, Jansen and Klein 2020 (NP-hardness, divisor chains in
O(n²)); Garey, Johnson and Stockmeyer 1976; Freuder 1990 (k-tree CSPs); Brooks' theorem;
Conforti, Di Summa and Wolsey 2008; Eisenbrand and Rothvoß 2009; Zhao and de Farias 2008;
Conforti and Zambelli 2009; Klaedtke 2005; Pugh 1991/1992 (Omega test); To 2008; Brent and
Zimmermann 2010; van der Hoeven 2022. Each round's `METAn.md` §2 says which were used.

## 5. How to continue

0. Run the answer log on the candidate (none exists for round 7 or the wrap-up commits; see
   section 2) and compare it with `library/r6-end/answers-c803059a.log`.
1. Port from `pncx-r7-codex`: cycle squares, the unit-image check, the nine-way test split,
   and the wide-alias test (ignored, open), keeping the candidate's I6.3 and I6.11 fixes.
2. U1 and U2 share one fix in zed-kernel (the product); measure it with
   `r7_tests::pncx_common_factor_parts_axis` (a probe built with `--cfg zed_probes`) and the `crt_bit_axis` command of
   `benches/src/bin/pncx_probe.rs`.
3. U3: offsets relative to the parent, never composed into a node.
3a. U4: find the step that answers one orientation of `x = m q + r` and refuses the other on
   the 59 cases (section U4), make it orientation-free, then drop the `Atom`-order run and
   un-ignore `remainder_alias_answers_do_not_depend_on_names`.
4. Run the five groups (l01_38_presburger, zedc_presburger, l01_39_reduced_product,
   l01_25_preimage_catalog, zedc_preimage) and the answer log against the last one
   (`pncx-log-patch-r6.diff`, compare with `cmplog.awk`).
