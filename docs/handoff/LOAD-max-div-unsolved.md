# LOAD-max-div: the cases not yet solved (handoff)

Written 2026-11-11 by the coordinator of the LOAD-max-div-xr cross-review, on the author's order to stop
after round 7 and hand off. This file is the starting point for the next cross-review
(ledger id LOAD-max-div-unsolved). It holds every unsolved case with its exact input, the
measurements (with the load average where it was recorded), every method tried and why it
failed, the open candidates, and where the full records are.

## 0. Where things are

- Branch `wt/load-max-div-xr` (worktree /home/luke/Work/wt/load-max-div-xr). It holds the merge
  candidate (rounds 1 to 6, commits listed in the ledger "ready" line) and this file. Nothing
  from round 7 is on it: both round-7 repairs were built by one seat each and never reviewed.
- Full records: /home/luke/Work/wt/xr-handoff/lmd-xr/ (copied from the coordinator's /tmp
  scratch, which will not survive). Inside it:
  - `HISTORY.md`: the issue table I1 to I35 with every decision, and per-round notes to round 7.
  - `META4.md`, `META5.md`, `META6.md`: the coordinator's per-round reviews and reruns.
  - `BRIEF1.md` to `BRIEF7.md`: what each round asked; `BRIEF7.md` lists the open issues as of round 7.
  - `ERRORS_{CLAUDE,CODEX,GEMINI}.md`: the seats' process errors.
  - `archive/r1` to `archive/r7`: each round's reports (`R<n>_<SEAT>.md`), diffs, logs and the
    coordinator's check files.
  - `library/r5-*`, `library/r6-*`, `library/r7-*`: every paper the seats fetched, with search logs.
- Seat scratch on /home (measurement outputs, scripts, candidate source files):
  /home/luke/Work/wt/lmd-scratch/claude/ and /home/luke/Work/wt/lmd-scratch/codex/.
- Seat worktrees with the round-7 code still uncommitted in them: /home/luke/Work/wt/lmd-claude
  and /home/luke/Work/wt/lmd-codex. Their diffs are saved as
  `archive/r7/tree_R7_CLAUDE.diff` and `archive/r7/tree_R7_CODEX.diff`
  (each is the whole round-7 base `archive/r7/change7.patch` plus the seat's own change).

Seats: round 1 to 4 had three (Claude Opus 5.5, Codex gpt-6.1-sol, Gemini). From round 5 on the
Gemini seat was missing (agy quota, reset about 2026-11-14 21:40 UTC); the author decided to
continue with two seats. Round 7 was stopped by the author at about 16:55 MST after 76 minutes;
both reports are partial (`archive/r7/claude/R7_CLAUDE.md`, `archive/r7/codex/R7_CODEX.md`).

How to measure (from BRIEF7.md section 4): the ignored probe `one_scope::lmd_probe` (in
`review-probe-r7.patch` in the records directory; not committed) takes `LMD_STEP` (the link
step, reading `H` for the link below and `x`), `LMD_TEST` (the question asked of each link) and
`LMD_SIZES`, and prints instructions, bytes, seconds, refusals and the exponent. Chain:
`h0 = x`, `h_i = step(h_{i-1})`, `t_i = test(h_i)`. Compare instruction counts, not seconds; the
machine is shared (load 15 to 80 during these rounds).

The author's rules that decide every case below: no cost above O(n log n) in general; no
thresholds, caps, budgets, size switches or fixed pass counts; a case may stay slow or be
refused only as a structural class proved pathological, detected in O(n log n), with its own
message; no answer may change or coarsen; batch and single checking agree; a scaling test at n
and 8n with a negative control the old code fails.

## 1. Summary table

| case | what is unsolved | best open candidate | status of that candidate |
|---|---|---|---|
| I49 | near shapes of translation-equivariant steps (`h + φ(h mod M)`) are superlinear to over 300 s | Claude R7 affine + one-exception images; Codex R7 modular-affine + redirected-rotation images | both built and measured on one seat each, never reviewed; neither covers 2+ guards |
| I50 | constant leaf read by two chains: refusal where the whole answers | none working | Codex R7: all alias variants rejected; `decided` retry fixes only the constant-leaf part |
| I55 | chains meeting at one base: refusals (abs leaf; product-base equality) | Claude R6 separator, ported by Codex R7 | port built, not reviewed; premise proved by both seats in R7 |
| I52 | separator makes new-symbol chains 32.1x bytes | Codex R7 port keeps 7.9x | not reviewed |
| I53 | ladder cone unions Θ(n²) bytes (28.2x) | hash-consed canonical sets (Codex R7) | rejected by its builder: +57% on the nested-rung control, and 22x on a new sparse-DAG adversary |
| I41 | unshared equal contents in persistent unions (40x to 67x for 8n) | same canonical sets | same rejection |
| I31 | fixed refiner pass `for unary_pass in [true, false]` | Codex R7 `refine_offset_bounds` (difference rows closed by Dijkstra, other rows one order-free relaxation) | built, not reviewed; exact general closure is out of reach (Max-Atom) |
| I27 | cross-rest merges grow rests outside convex runs | none | all five measured families are about 8x; no general method |
| I37 | prefix family: questions other than sign over two chains | separator (I55) | as I55 |
| I12/I26 | `H mod M + H` periodic summaries; one-atom link values not built | images (I42) answer equality; periodic summaries n^1.02 | recorded |
| I13 | bit lower bound for explicit per-link summaries of the mixed family | outside that class (folds, certificates) | recorded, not a defect |
| I56-codex | the whole-vs-parts test helper skips a comparison when both refuse | fixed-witness test (Codex R7) | test written, red until I50 is fixed; not reviewed |

## 2. The cases

### I49: near shapes of translation-equivariant steps

**Input.** A chain `h0 = x`, `h_i = step(h_{i-1})`, question `t_i = (h_i == c)` (c = 9 or 0),
at moduli M = 7, 1000, 10^9 + 7:

| name | step |
|---|---|
| v1 | `H mod M + H + 1` |
| v2 | `H mod M + H - 3` |
| v3 | `if H mod M == 0 { H + 1 } else { H + 3 }` |
| v4 | `if H mod M == 7 { H + 1 } else { H + 2 }` |
| v5 | `if H mod M == 0 { H + 2 } else { H + 1 }` |

Every one has g(h + M) = g(h) + M. The base (Codex R6 `extend/images.rs`) answers only the exact
shapes `H mod M + H` (I42) and `if H mod M == 0 { H + 1 } else { H + 2 }` (I34) and the mixed
family; every near shape falls back to the exact path.

**Measurements on the base.**
- Coordinator, round 6 (archive/r6/check6-codex-variants/v1..v8.txt, sizes 11 to 81, load 33 to
  40): v1 at M = 1000 `H == 9` n^2.42, 8.0 G at 81 links; v2 n^2.43; v3 n^2.04, 137.7 G at 81;
  v4 n^2.04, 128.9 G; v5 linear but 6.47 G (70x the matched shape).
- Claude, round 7 (archive/r7/claude/R7_CLAUDE.md Q2 table; lmd-scratch/claude/out/perf/base-all.txt,
  load 14 to 38), instructions at 80 links: v1 10.9 G (M = 7), 7.8 G (M = 1000), over 300 s
  (M = 10^9 + 7, rc 124); v2 the same; v3 9.0 G, 134.2 G, 134.4 G; v4 9.1 G, 125.7 G, 125.8 G;
  v5 5.8 G, 6.4 G, 6.4 G. Same on `H == 0`.

**Methods tried.**
1. Round 6, Codex: shape matchers for I34 and I42 (in the base). Exact, linear, but only the
   exact shapes (the coordinator found I49 on them).
2. Round 6, Claude: monotone pullback, class C (|b0 − b1| ≤ 1). Proof complete, never built.
3. Round 7, Claude (built, not reviewed; `archive/r7/claude/R7_CLAUDE-own.diff`, only
   `extend/images.rs` and one ignored probe): two rules after Codex's matchers.
   - Affine remainder steps `g(h) = ±h + w·(h mod M) + C` (w ≠ 0, any C, any M ≠ 0): the image of a
     coset c + dZ with d | M is ((p + w)c + C) + gcd((p + w)d, M)Z.
   - One-exception steps `if h mod M == s { h + b1 } else { h + b2 }` (and `!=`): in the
     frame u = r − t·b2 the missing residues after k steps are the first min(k, L) orbit points
     (δ = b1 − b2 not in ⟨b2⟩) or the last min(k, e) (δ ≡ e·b2), L = M / gcd(b2, M).
   - Joint questions `R mod M == s && V == c` by two linear congruences.
   - Results: v1 to v5 at every M and both questions 73.5 M to 115.5 M instructions at 80 links,
     8.08x to 8.16x for 8x links, independent of M. 50x to 1168x below the base.
   - Checks: closed forms checked by brute force on 51.4 M cases, 0 failures. Agreement with the whole on
     182 shapes. Negative control (new answers negated) turned 118 of 118 variant runs red.
   - Scale table of one_scope.rs: −0.22% to +0.17%, the same as the noise between two runs.
   - The l01_38 group passed (317 pieces); the other six groups were not run.
   - Claude's own "most likely wrong" claims: the window rule past M = 29, and whether the language's `mod` with a negative divisor is Euclidean.
4. Round 7, Codex (built, not reviewed; in `archive/r7/tree_R7_CODEX.diff` and
   lmd-scratch/codex/r7, file `candidate-q2-images.rs`):
   - A modular-affine image `h + A(h mod M) + C`, with the same coset proof as Claude's.
   - One redirected rotation edge `h + B + δ·[h mod M = R]`: modulo M the map is a rotation by B whose
     edge out of R is redirected. The result is one tail plus one cycle, from which it gets the
     absent residues and the visit count for orbits.
   - Native checks: 3.06 M finite-map comparisons, a negative control giving 403,465 counterexamples,
     99,840 affine cases.
   - Matrix of 48 cases at 80 and 640 links (5 variants and 3 old shapes, 2 targets, 3 moduli): 0 refusals,
     7.93x to 8.03x.
   - Codex's first scale comparison showed up to +2.36% (divisions by a parameter) and +1.97% (abs chains).
     This was not explained when the round stopped.

**Disagreement / open points.**
- The two round-7 rules cover the same classes by different proofs (Claude's moving frame and
  windows; Codex's tail-and-cycle of a rotation). Neither has been read by the other seat. A review should
  check the two against each other on the same brute-force harness.
- Claude's final build drops the joint map for a chain mixing Codex's `h + h mod M` step with
  another affine step of the same modulus (to avoid a 0.7% to 1.2% slowdown). Such chains take the
  exact path for joint questions.
- Codex's +2.36% is unexplained. Claude's build shows no change measurable above noise.

**Still uncovered by either rule (Claude's outside-class runs, load 15 to 20,
lmd-scratch/claude/out/perf/outside.txt, M = 7, `H == 9`):**

| step | 10 links | 40 links |
|---|---|---|
| two guards `if H mod 7 == 0 {H+1} else {if H mod 7 == 3 {H+2} else {H+3}}` | 1.35 G | 6.66 G |
| `H mod 7 + 2 * H` (coefficient 2 on h) | 1.05 G | 5.34 G |
| `if H mod 7 == 0 {H+1} else {2 * H}` (non-constant branch) | 0.98 G | over 300 s |
| compositions of steps of different moduli or kinds | not measured | |

**Open candidates.**
- φ piecewise constant on g residue intervals. Represent the image in the moving frame as a
  union of O(g·k) progressions; each step moves at most g intervals. Expected O(g·n) per chain,
  independent of M (Claude R7, conjectured). Open question: whether this stays polynomial in g
  when offsets differ by non-multiples of the orbit generator, where the windows can interleave.
- Literature: Bozga, Iosif, Konečný (arXiv 1307.5321, `library/r5-claude`). Powers of octagonal
  relations are periodic with an exponential prefix and period, and reachability of flat systems is NP-complete. So a
  general closed form for arbitrary guarded affine steps cannot be cheap in general. The classes
  above are much smaller.
- Coefficient ≠ ±1 on h (`H mod 7 + 2 * H`): no candidate yet. I15 shows `(3 * H + 1) div 2` and
  its relatives need exponentially many pieces, so a non-unit coefficient may fall in a
  pathological class. That needs a proof for this shape.

### I50: a constant leaf read by two chains

**Input** (Claude R6 test
`r6_questions_over_constant_leaves_products_and_both_outputs_are_those_of_the_whole`, first family,
in `archive/r6/R6_CLAUDE-own.diff` lines 859 to 950):

```
k(x: int) = 7;
b0(x: int) = x;
b(x: int) = max(b0(x: x) div 2, x - 9);
c0l0(x: int) = b(x: x) + 0;
c1l0(x: int) = b(x: x) + 1;
c0l{i}(x: int) = c0l{i-1}(x: x) div 2 + k(x: x);     for i = 1..5
c1l{i}(x: int) = c1l{i-1}(x: x) div 2 - k(x: x);
t{i}n0(x: int) = c0l{i}(x: x) + c1l{i}(x: x) > 0;
t{i}n1(x: int) = c0l{i}(x: x) - c1l{i}(x: x) == 14;
t{i}n2(x: int) = c0l{i}(x: x) - c1l{i}(x: x) == 16;
```

`t4n1` gives Err(Growth) from parts. The whole gives Ok(true); x = 0 satisfies it (Codex R7 test
`i50_two_output_answers_keep_frozen_concrete_witnesses`: x = 0 satisfies, x = 6 falsifies). The
same refusal occurs on the round-6 base, the Codex tree and Claude's tree, so no seat's change caused it.

**Methods tried (all round 7, Codex; runs in lmd-scratch/codex/r7/runs/):**
1. Exact `decided` binding retry on summarized systems (kept in Codex's candidate). It answers the
   constant-leaf family. The next family in the same test (two outputs of one division,
   `P div 3 + P mod 3`, `P div 2 - P mod 2`) still fails. The instantiated calls return a
   multi-term linear value with no node of its own, so the unary call interface is hidden.
2. Broad return-value alias in preimage.rs (`experiment-broad-alias-preimage.rs`): Claude's
   whole test passed, but the full l01_38 run had two regressions (a written-relation shape
   mismatch; Err(Shadows) against Err(Growth) on the projection-against-bodies oracle). Rejected.
   Codex's later diagnosis: all 15 multi-term return blocks came from the closed/reference
   translator, not the scoped path. The "pass" came from the reference whole turning into a
   refusal, which the test helper then skips (I56-codex). So it never fixed I50.
3. Narrow alias (only when all terms are the two outputs of one division, only in the shared
   scope), normalized and scoped variants: none fixed I50 (`narrow-oracles-driver.txt`,
   `normalized-oracles-driver.txt`, `scopednormalized-oracles-driver.txt`). Rejected.

**Open candidate:** give an instantiated call's multi-term linear return value a node of its own
in the scoped path, so the separator and the buckets see the unary interface. No complexity
estimate yet. Codex's narrow attempts show the representation change has to reach the scoped
translator, not the reference one.

### I55 (with I37 and I52): chains meeting at one base

**Input** (Claude R6 `r6_questions_over_chains_meeting_at_one_base_are_those_of_the_whole`, and
`r6_the_questions_of_chains_meeting_at_one_base_scale`; helper `chains_over_a_base` in the same
diff, lines 513 to 533: `b0 = x`, `b = <base>`, chain k starts at `b + k`, each link applies its
step to the link below, a test per depth).
- Abs leaf: `l(x) = if x > 0 { x } else { 0 - x }`, base `max(b0 div 2, x - 9)`, steps
  `P div 2 + l(x)` and `P div 2 - l(x)`, tests `P0 + P1 > 0`, `P0 - P1 == 4`, 6 links. On the
  round-7 base `t4n0` gives Err(Shadows) where the whole gives Ok(true) (Codex R7 rerun,
  `runs/base-peer-driver.txt`).
- Product base: base `x * x div 2`, steps `P div 2 + 1`, `P div 2 - 1`, tests `P0 + P1 > 0`,
  `P0 - P1 == 2`, scale 20 / 160 links: refused at `t3n1`.
- I37 prefix family (base `max(b0 div 2, x - 9)`, steps `P div 2 ± 1`, test `P0 + P1 > 0`):
  round-5 base 0.355 to 71.5 G at n = 20 to 160 (n^2.55). Round 6, Codex common-ray sign sums
  (in the merge candidate) make sign questions linear: 141.9 M / 1133.7 M at 81 / 641. Other
  questions (`P0 - P1 == 2`, ranges) are not covered.

**Methods tried.**
1. Round 6, Claude separator (`Summaries::lift`, `star_separator`, `ancestor`, `meet`, owner
   routing): answers both I55 families; prefix 351.8 M / 3061.0 M at 80 / 640 (8.70x). But I52
   (new symbols above the separator) went to 32.1x bytes, and exactness rested on an unchecked
   premise.
2. Round 6, Codex functional-cone separator: rejected by Codex itself. It coarsened
   `H div 2 - H div 3` to Err(Shadows).
3. Round 7, premise "a functional leaf is a function of its symbols": proved by both seats
   independently from `is_func_sym_leaf` (extend.rs about line 4007) and `roots()` (about 3826).
   Only two leaf shapes are accepted: one unit equation, or an exact division pair. Each determines its atoms.
4. Round 7, Codex port of the separator onto the round-7 base (built, not reviewed), with the
   round-6 anchors and product buckets kept, a retry of the old local plan where a separator
   summary is unavailable, and binary lifting for ancestor and meet. `runs/candidate-peer-driver.txt`:
   both I55 families pass, I52 stays 7.9x, I50 still red.

**Open:** review Codex's port. Its first scale comparison showed up to +2.36%, not yet
explained. Then measure the I37 equality and range questions at n and 8n.

### I53 and I41: cone unions

**Inputs.**
- I53 ladder (Claude R6 `r6_ladder`, `archive/r6/R6_CLAUDE-own.diff` lines 413 to 460): `a_0 = x`,
  `a_i = a_{i-1} + 1`, `b_i = b_{i-1} - 1`, rungs `d_i = a_i + b_i`; `Summaries::syms` on every
  rung. The two chains share only the base, so rung i's cone adds i entries: about n²/2 in all.
  Control: rungs `d_i = a_i + a_{i-1}` (cones nest).
- I41 (Codex R6): unshared twins, equal contents built separately so the persistent unions do not
  share nodes.

**Measurements.**
- Ladder at 100 / 800: 28.2x bytes (limit 12.8), on the round-6 base and the Codex tree
  (archive/r6/check6-base-ladder.txt, load 35; check6-codex-ladder.txt, load 39). Control 9.5x
  instructions, 9.2x bytes (80.6 M instructions at 800).
- I41 on the round-7 base (Codex R7 `runs/base-metadata.txt`): 23.4 M / 938.8 M / 63.1 G
  instructions at 100 / 800 / 6400 (40.06x, 67.25x); bytes 2.3 M / 58.8 M / 2.93 G.

**Methods tried.**
1. Round 7, Claude (analysis only, scored): hash-consed persistent set nodes 7/10, cones as DFS
   intervals 4/10 (a ladder's cones are not intervals of one DFS order), union by rank with a
   per-query visited set 5/10 (changes the cost model of every caller).
2. Round 7, Codex: canonical Patricia sets with exact collision buckets and memoized union pairs
   (`extend/sets.rs`; `R7_CANONICAL_EXPERIMENT.diff`, `candidate-sets.rs` in lmd-scratch/codex/r7).
   - I41: 9.15x / 9.35x instructions, 8.39x / 8.76x bytes.
   - Ladder: 10.5x instructions, 10.4x bytes.
   - But the nested-rung control went from 80.6 M to 126.6 M instructions at 800 (+57%).
   - A new sparse-DAG adversary (prefixes A_i joined with B_{bitreverse(i)}, O(n) nodes) costs 9.5 M /
     204.4 M / 4.59 G at n = 128 / 1024 / 8192 (21.5x, 22.5x), with 24x new cached node pairs
     (`runs/permuted-prefixes.txt`).
   - Codex rejected it for general adoption: there is no proof that the union pairs are bounded by
     O(n log n) on general DAGs.

**Open candidates.**
- Canonical sets with a proved bound on the number of union pairs P for the DAG shapes that occur.
  Or show the bit-reversed adversary is a structural class that cannot arise from definitions
  (it can: any two chains joined in permuted order).
- Store cones implicitly: answer "is atom a in cone(d)" by a reachability index (for example
  2-hop labels, or chain decompositions of width w, with O(w) labels per node) instead of
  materializing unions. The cost depends on the DAG width; this was not studied.
- Literature not obtained in round 7: Filliâtre and Conchon (hash-consing, doi
  10.1145/1159876.1159880; 404 at the publisher and Sci-Hub), Appel's hash-consed tries.
  Braibant, Jourdan and Monniaux (hash-consing in a verified setting) is in the corpus, unread.

### I31: the fixed refiner pass

**Site.** `quotient_offsets` in extend.rs (about line 5076; the pass loop
`for unary_pass in [true, false]` about line 5191; its only caller about line 3178).
`rem_bounds` (from `def_bounds`, the ranges 0 ≤ r ≤ m − 1 of the remainders) is used to (a)
return no branches when a range empties or a unary equation has no integer solution; (b) leave
bounded atoms out of candidate quotient forms; (c) bound the offset of a quotient Q, refuse a
candidate whose atom range is ≥ m, and split on `Q == d` for d in [lo, hi] (Claude R7 Q5,
by reading).

**What is proved (round 7, both seats independently).** Stopping early never changes or
coarsens an answer. Every tightening is implied by the rows. Every branch copies all
original rows and adds only `Q == d`, so the branches' union is exactly the original system.
Looser bounds give more (empty) branches or a refused candidate. So the only effects are cost and
decided-to-refused, never a different answer.

**Not settled.**
- Can two passes be too few on this family? Claude sketched (not built) a chain of multi-term
  rows r1(a, b), r2(b, c), r3(c, d) listed in an order that needs three visits. Codex built a three-edge
  difference chain that defeats the old single multi-row sweep (in its candidate's tests). Neither
  showed an input from source where the answer goes from decided to refused.
- The rule against fixed pass counts is not met.

**Hardness (literature, read).**
- Bordeaux et al. 2011 (JAIR 40; library/r6-codex), read by the coordinator:
  - Prop. 1: the bounds fixpoint of linear constraints is NP-complete.
  - Prop. 2: with unit coefficients it is given by LP.
  - Prop. 4: unit linear plus `max` is polynomial only if Max-Atom is.
- Bezem, Nieuwenhuis, Rodríguez-Carbonell 2008 (LPAR; library/r7-claude, `bezem-lpar08a.txt`):
  Max-Atom is in NP ∩ co-NP, with no polynomial algorithm and no NP-hardness known.
- So an exact closure for every input of this family (it contains `max`) is not a reasonable target.

**Methods tried.**
1. Round 6, Claude: a complete refiner is NP-hard (subset sum); closure takes Θ(M) rounds;
   proposed Bellman–Ford on difference rows.
2. Round 7, Codex `refine_offset_bounds` (built, not reviewed; `q5_refiner.rs` in
   lmd-scratch/codex/r7):
   - Unary rows are intersected.
   - Every other row contributes interval consequences from the same unary bounds, independent of order.
   - A network of `x − y + c ≥ 0` (c ≥ 0) and zero-offset equalities is closed exactly by two
     multi-source Dijkstra runs, O((V + E) log V).
   - It reaches the exact bounds on that class; other rows stay a conservative relaxation.
   - Tests: all row reversals and 200 complete finite-box difference networks.
   - Not measured on the scale table.
3. Round 7, Claude (proposed, not built): Bellman–Ford, or incremental difference propagation
   (Cotton and Maler 2006: O(m + n log n) per added constraint; library/r7-claude,
   `cottonmaler-fulltext.txt`), for unit two-variable rows. Keep a fixed or SCC-ordered schedule
   for rows of three or more terms, which by the proof above can only refuse.

**Disagreement.** Codex uses Dijkstra only for nonnegative-offset difference edges. Claude
proposes the full unit two-variable-per-inequality (UTVPI) class (sum rows by doubling, Bellman–Ford). The UTVPI class is wider; its cost
is O(nm) with Bellman–Ford, or O(m + n log n) incremental per Cotton and Maler.

**Open:** decide the class (difference rows only, or UTVPI); build it with a test that fails
under two passes and a scale test; prove the rest of the rows can only refuse; then the author
must accept the remaining relaxation (rows with 3+ terms) as an approximation that cannot widen.

### I27: cross-rest merges outside convex runs

**Inputs and measurements** (Codex R7 rerun of Claude's measurement code, `runs/cross-rest-80-640.txt`,
p = 80 / 640): convex 0.56 / 4.45 M (1 piece); concave 0.76 / 6.09 M (40 / 320 pieces); gapped
0.98 / 7.81 M (80 / 640 pieces); two coordinates 36.6 / 296.4 M (80 / 640); mixed orientations
0.96 / 7.81 M. All about 8x.

**History.** Round 4, Codex: tangents of a parabola, `x = i and y ≥ 2ix − i²`, merge to one piece of
p + 2 rows, each necessary; `lean` cannot remove them. Round 5: convex integer-slice batch join
(5.7x). Round 6: convex runs with gaps, both orientations (Codex, in the merge candidate).
Claude R6: a p/2 lower bound on pieces for concave runs. Codex R7 confirmed it for representations
without existentials or congruences.

**Open:** a general method for growing rests (shared or batched rest), or a family that is
superlinear. None of the measured families is superlinear.

### I12/I26 and I13 (recorded, not defects in the candidate)

- I12/I26: `H mod 7 + H`. The equality questions are answered by the I42 image (in the
  candidate). The periodic summaries (Gemini R3/R4 `quotient_offsets`) are n^1.02 to 1.05. Claude's
  R3 one-atom link value (7 pieces of O(log k)-bit constants) was never built.
  I34 (`if H mod M == 0 ...`) at large M is answered by the R6 images for equality and joint
  residue; other questions at large M take `quotient_offsets` with hi − lo + 1 branches (bounded
  only through I31).
- I13: Claude R2 proved Ω(k / log k) bits per link for any explicit per-link polyhedral summary
  of the mixed family; Codex R3 repaired the statement. The candidate escapes the class by folds
  (I28) and certificates (I29); mixed `H == 9` 93.3 M / 749.6 M at 81 / 641.

### I56-codex: a test gap

The whole-against-parts helpers skip a comparison when both sides refuse. A change that makes the
reference whole refuse can hide a refusal of the parts. Codex R7 wrote
`i50_two_output_answers_keep_frozen_concrete_witnesses` (fixed witnesses x = 0 and x = 6,
computed in Rust); it is red until I50 is fixed. It is in Codex's uncommitted tree, not reviewed.

## 3. What the next round should do first

1. Review both I49 rule sets against each other on one brute-force harness. Keep one (or merge
   them), run all seven groups, the scale table and a negative control. Explain Codex's +2.36%.
2. Review Codex's separator port (I55, I52) and its `decided` retry (part of I50).
3. Decide the I31 class (difference rows or UTVPI) and build it with a three-pass red test.
4. I53/I41: find a cone representation with a proved bound, or prove the bit-reversed adversary
   arises only from a class that can be refused.
5. I50: give scoped multi-term call returns a node of their own.
6. I49 beyond one guard: piecewise-constant φ, or a proof that it is pathological.
