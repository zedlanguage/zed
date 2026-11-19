# REFUSAL-front: unsolved cases after round 11

Handoff for the item REFUSAL-front-unsolved. The cross-review REFUSAL-front-xr ran 11 rounds
(rounds 1 to 8 with three seats; rounds 9 to 11 with Claude claude-opus-5-5 and Codex
gpt-6.1-sol only, the Gemini seat missing by the author's decision of 2026-11-11 on a quota
error). The author stopped it on 2026-11-11 at 16:50 MST, after round 11. Everything verified
so far is committed on the branch wt/refusal-front-xr as a merge candidate. This file holds
only what is not solved.

Each claim is marked: **confirmed** (the orchestrator ran it or read the cited source),
**computed by a seat** (the seat's run, not rerun by the orchestrator), **argued** (a proof or
a reading, not a run), or **open**.

## Where the record is

All paths are on this machine. Nothing below has been deleted.

| what | path |
|---|---|
| review branch (merge candidate) | /home/luke/Work/wt/refusal-front-xr, branch wt/refusal-front-xr |
| accepted round-8 head (fixed ref) | 0e120081a on main (rebased from 6fc19f7a; the branch wt/refusal-front-accept was deleted 2026-11-19) |
| the whole review record: briefs BRIEF1..11, META5..10, HISTORY.md (issue table X1..X47 and per-round notes), ERRORS_{CLAUDE,CODEX,GEMINI}.md, library/ with bib.md, archive/r1..r10 (each round's brief, reports, diffs, measurements), r11/ (round 11 reports, diffs, logs, sources) | /home/luke/Work/wt/rfx-scratch/review-record (copied from the session scratchpad rfx-xr, which lives under /tmp) |
| orchestrator's measurements and scratch per round | /home/luke/Work/wt/rfx-scratch/orch (r9x, r10x, r11x; r11x/variants.txt is the three-way fields() table below) |
| seats' large outputs | /home/luke/Work/wt/rfx-scratch/claude, /home/luke/Work/wt/rfx-scratch/codex, /home/luke/Work/wt/rfx-scratch/gemini; the raw refusal dumps (codex/dump-*, codex/r10/dump-*) were deleted on 2026-11-14 and can be rebuilt from their commits; the comparisons drawn from them stay in codex/r10/accepted-v-*.json and accepted-map.tsv |
| round 11 seat changes | review-record/r11/claude/R11_CLAUDE.diff and review-record/r11/codex/R11_CODEX.diff, both against base f9ada7ca2 (the seat worktrees rfx-claude, rfx-codex and rfx-gemini were removed on 2026-11-14; their diffs were byte-identical to these files) |
| test-group logs per run | /home/luke/Work/wt/refusal-front-xr/build/r9c-logs, r9c2-logs, r9d-logs, r9rb-logs, r9x-logs, r9x2-logs, r9x3-logs, r10c-logs, r10m-logs, r10r-logs, r11c-logs, r11m-logs, r11f-logs |
| round 11 seat reports | review-record/r11/claude/R11_CLAUDE.md and .diff; review-record/r11/codex/R11_CODEX.md and .diff, with meas/ and sources/fetched/ |

Test builders named below are in tests/steps/l01_23_subtyping/refusals.rs on the branch (now
tests/steps/l01_23_groups_and_refusals/refusals.rs); the probe families are built by
`rfx_case(name, n, tag)` in the same file. `r9_wide_literal_probe` is the binary
`r9_wide_literal` of zed-benches.

## State after REFUSAL-front-rest (agent front1, 2026-11-19, from main 2eb9353cc)

| item | on main before | now |
|---|---|---|
| U2 | fixed: `r10_answer_preservation_nine_node_list_regression` passes (Inhabited, witness `[0, 2]`; 1.060 at 8 and 64) | unchanged |
| U3 | fixed: the two probes printed 21.8M and 11.6M units at 1024 (1.189G and 594M at the round-11 merge), 3.9 times per 4 times n | pinned: `bench::r11_tagged_payloads_must_scale` 7.994 and `r11_named_payloads_must_scale` 8.027 (16384 and 131072), replacing the two probes |
| U4 | fixed: `r11_payload_name_prefixes_must_scale` 7.891 | a neighbor found and fixed: one bare name after n payload names, 14.05 times, now 7.852 (`front_bare_name_after_payload_prefixes_must_scale`; `Atoms::bare`, COMPLEXITY) |
| U5 | open: 15.9 times from 512 to 4096 | fixed: `sweep::lits_ok` walked every listed integer once per head read; it reads the set's class union now (COMPLEXITY); 8.04 times, bench resized to 4096 and 32768, 8.143 |
| U6 | open | done: dumps of 19bc4e25 and the round-11 head on 19bc4e25's own tests, keyed by printed type; 737 changes in l01_23, no Inhabited/Empty flip; all 223 narrowings vanish with 5d72f0689's `open_fork` term switched off (U6 below). The current kernel has 22 more fork narrowings, filed as REFUSAL-front-post-r11-forks |
| U7 | open | done: Case A read a second time and Mutant 2 argued at the code (comment above the narrowing in `find_prefix_chains`); the mutation run survived 18 firings in two exact-oracle tests (U7 below) |

The deferred file /home/luke/Work/wt/scratch/deferred-tests/REFUSAL-front-rest.rs is deleted.
Its parts: the three tests of part (a) were on main already, identical, and pass;
`r11_ternary_alignment_probe` (4096 alone took past 60 s with its membership check) is now the
bench `r11_ternary_alignment_scales` (1024 and 8192, 8.146); the zed-kernel escape-cells bench
of 6817c6740 and the probes `rfx_probe` and `r9_escape_probe` were dropped, not brought back.
The escape bench timed `cells_sweep` (the Θ(n²) method `cells_windows` replaced, about 350
lines) against `cells_windows` on dumps that no longer exist; the answers of `cells_windows`
are checked against the definition by `escape::windows_tests::windows_agree_with_the_walk`
(600 random forests) and its cost by the three `escape_cells_of_*` benches, so bringing it back
would restore only dead code. The two probes printed work and asserted nothing; every family
they printed can be measured by a `scaling::check` over `rfx_case`, as `escape_cells_scale`
does.

## U1. X38: the escape's cell discovery reads super-linearly many empty cells

**Solved (2026-11-12, hybrid cross-review round 3):** `cells_windows` reads each window of
place offsets by method A or by the residue-filtered pair listing, whichever computed cost is
lower; within n log n on every bench family, at most 0.962 of the sweep's instructions, answers
equal on the 91 dumps (COMPLEXITY K106).

**Program.** Lists `P \ (R_1 | ... | R_k)` where P is a positive list type with finite or
cofinite heads and every R_i is a list chain that enters a shared tail at a different height.
The escape solve (crates/zed-kernel/src/types/empty/escape.rs, module comment and lines about
20 to 83) decides it by 2-SAT over at most two atoms per row, with laminar atoms at each place;
that solve is linear in the cells. The cost is the **cell discovery**: for each row, finding
its first two to four separating places. A node v at height ht(v) is at place
`ht(s_N) − ht(v) + 2` of every row N whose tail lies below it, so one node is at a different
place for each row. The reads that find no cell are the "empty reads"
(`Type::escape_cell_counts()`, second number).

Families (builders): `r8stageout` and `r8stagein` (`r8_stage_boundary`, Gemini R8),
`r9bmmlate` (`r9_bmm`, Claude R9), `r9cosets` (`r9_cosets`, Codex R9), `r10alternating`,
`r11_ternary_alignment_probe` (Codex R11, on `r9_bmm` with
`a[i][q] = (i mod 3 != 0) or (q >= m−2)`, b all ones, m = max(4, isqrt n)).

**Verdict now and wanted.** All are Inhabited now and wanted Inhabited; the verdict is right.
The cost is wrong: wanted O(n log n) reads, or a refusal class proved hard (refusal only for
pathological cases, by the author's order).

**Measurements** (empty reads on the round-11 code; computed by Codex R11, meas/cells.md;
the r8stageout and r9bmmlate rows agree with Claude R11's meas/q1-empty-reads.txt):

| family | 16 | 64 | 256 | 1024 | 4096 | 16384 |
|---|---:|---:|---:|---:|---:|---:|
| r8stageout | 3 | 34 | 610 | 10,114 | 163,330 | 2,619,394 |
| r8stagein | 6 | 90 | 930 | 10,302 | 115,940 | 1,367,730 |
| r9bmmlate | 12 | 280 | 3,120 | 28,768 | 245,952 | 2,032,000 |
| r9cosets | 4 | 82 | 1,398 | 21,748 | 342,802 | – |
| r10alternating | 8 | 160 | 1,664 | 14,848 | 124,928 | – |
| r11 ternary alignment | 8 | 200 | 2,080 | 19,488 | 163,968 | – |

r8stageout grows 16 times per 4 times n (Θ(n²)); r9bmmlate about n^1.5; r9cosets reads
exactly K²+3K−6 empty probes, K = floor((n−2)/7) (Codex R9, proof in archive/r9/codex).
Work at 4096 is 0.80G to 1.05G units on r8stage* (META8), so the verdict stays fast in
practice at these sizes.

**Methods tried, in order.**

| round, seat | method | result |
|---|---|---|
| r6 Claude | escape as 2-SAT over at most two atoms per row, laminar atoms | adopted; the solve is linear; discovery is the open cost |
| r7 Codex | height-congruence skip (gcd of root heights, finite and cofinite residues) | adopted; r6parity 0 empty reads; beaten by r7congruenceout (R7-C1) |
| r7 Gemini | K ≤ 2 quadrant decomposition with NTT power sums | rejected: declines r7congruence and r7bmmout (K = 3) to a search of exponent 1.9; a wrong Empty on Codex's cycle-meet input |
| r7 Claude | Boolean matrix multiplication argument against listing cells | argued: listing all cells of all rows is BMM |
| r8 Claude | place window `lo = max(2, min_below + 2 − h)`, per-value residue filter | adopted; beaten by r8heightout |
| r8 Codex | suffix gcd of live root heights at least h | adopted; beaten by r8residuesout |
| r8 orchestrator | the three combined plus the live-row count | ≤ n empty reads on every family named up to round 8; beaten by r8stageout (Θ(n²)) |
| r8 Gemini | two-stage finder: Stage A multi-residue buckets; Stage B heavy-light decomposition with CRT-NTT power sums and Hankel recovery (archive/r8/R8_GEMINI.diff) | 0 empty reads on every named family (confirmed in META8). Not taken: (1) chooses Stage A or B by a probe count against a linear multiple (escape.rs:1091 of that patch), rejected as a threshold; META9 reopened whether it is an allowed switch between identical outputs at a derived cost crossing, not settled; (2) its own worst case O(I √N log^1.5 N); (3) the CRT bound is never checked against the prime product (wrong moments past about n 2^25 without notice); (4) `hankel_recover` can panic; (5) incomplete on four cold cells in one shell (Codex R9-C3, red test on its patch) |
| r9 Claude | Claim 1: listing each row's cells is BMM; adversaries r9bmm, r9bmmlate, r9bmmone | argued; r9bmmlate Θ(n^1.5) |
| r9 Codex | r9_cosets with the K²+3K−6 proof | computed and argued |
| r10 both | OV through the shift encoding | refuted: the encoding's input is already N² |
| r10 Codex | selector reduction: bichromatic OV to Inhabited of `cons(D_A, cons(D_B, nil))` minus d selector rows, O(nd) literals | confirmed (test over all 4,096 n 3 d 2 matrix pairs): no O(I polylog I) exact verdict for the **general** class under the OV hypothesis. Does not reach the fragment: its cells `D_A \ A_q` cross, the fragment's cells are laminar (Codex R11 example: red vectors (0,1),(0,0),(1,0) give cells {0,1} and {1,2}) |
| r11 Claude | cell discovery on one shared chain is subset matching: row N separates at node v_j exactly when `p_{t_N − j + c} ⊄ h_j` | argued for one chain; conjectured for tail trees (tree pattern matching). Gives existence of a cell per shift, not the first two to four separating places that the finder needs |
| r11 Codex | the expanded Cole–Hariharan route | argued limit: one finite alphabet A of width n repeated along a positive chain of n is O(n + |A|) shared but n·|A| expanded occurrences; no sharing-preserving reduction |
| r11 Claude | Klee's measure problem (Gorbachev–Künnemann) as a hardness source | argued: gives n^{3/2−o(1)} under the 3-uniform hyperclique hypothesis for rows with three or more atoms, which the code already sends back to the search for Empty; does not touch the two-atom fragment. Orchestrator's objection, open: the reduction's boxes have interval sides, and `Ints` has no ranges, so writing a box side as a head may not stay at input size O(n polylog n) |
| r11 Claude | per-value convolution (FFT per distinct value) | not implemented; O(σ n log n), quadratic when the number of values σ grows with n. Codex R11 adds (meas/coverage-control.json): testing only "every row has a cell" is not enough; at one place {0,1} with negatives {0} and {1} the cells are disjoint singletons, so cells must be recovered and checked together, as the 2-SAT stage does |

**Literature** (all in review-record/library/ with bib.md entries, or in the round folders):

- Cole, Hariharan, "Verifying Candidate Matches in Sparse and Wildcard Matching", STOC 2002,
  DOI 10.1145/509907.509992: abstract, fourth bullet, "an O(n log² m) time deterministic
  algorithm for Subset Matching and Tree Pattern Matching" (confirmed by the orchestrator and
  by Codex on the page image; review-record/r11/codex/sources/fetched/ColeHariharan2002.*).
  Kept as the best algorithmic lead. A copy fetched for verification only; do not commit it.
- Gorbachev, Künnemann, "Combinatorial Designs Meet Hypercliques", arXiv 2303.08612,
  main.tex lines 159 to 184 (confirmed). Kept as an argument with the range gap above.
  review-record/r11/claude/sources/fetched/Gorbachev_2023_klee_arXiv_2303.08612/.
- Dudek, Gawrychowski, Starikovskaya 2020, generalized pattern matching: theorem `th:det_i`
  states O(n √(I log m) + n log n) (Codex R11 correction of Claude's quote, which put log m
  outside the root; not rechecked by the orchestrator). Partial method only: about n^1.5.
  Its lower bounds charge an explicit matching relation or report all alignments; neither
  gives a refusal class for the yes/no verdict (Codex R11).
- Fischer 2024, deterministic sparse pattern matching (Baur–Strassen): needs single-symbol
  text and wildcard pattern; no reduction from set-valued heads found.
- Chen–Williams 2019 (OV equivalence class): used by the selector reduction; general class only.
- Abboud et al. 2015, Subtree Isomorphism Revisited: OV hardness needs a branching embedding
  gadget, absent under functional tails.
- Dropped: Goldstein et al. 2017 (witness listing, not the verdict), Graf et al. 2017
  (L^1.5), Fredriksson. Unread leads fetched by Gemini R9: Chan–Larsen–Pătrașcu 2011, Chan et
  al. 2023, Fine–Wilf 1965, Fischer–Jin–Xu 2024, Roche 2018.

**Best open candidates**, in the order to try:

1. A sharing-aware subset-matching or tree-pattern-matching discovery (Cole–Hariharan
   O(n log² m)) over the tail tree, extended from "is there a cell at this shift" to "the first
   two to four separating places at every shift". Both parts are open: the extension, and a
   representation that does not expand shared alphabets (Codex's quotient argument shows
   cofinite heads are not a semantic obstacle on one spine: one representative per listed
   integer plus one fresh class preserves inclusion and disjointness).
2. Gemini R8's Stage B alone (no count switch), with the CRT bound checked, `hankel_recover`
   made total, and Codex's four-cold-cell case fixed; then measure its worst case. Its stated
   bound is above O(n log n).
3. A conditional lower bound **inside** the laminar fragment (none found by any seat), which
   would justify a refusal class there.

**Open disagreements.** (a) Claude: discovery is subset matching, so a near-linear existence
method likely exists; Codex: the expanded input is the limit, so the route does not yet give
the bound. (b) Claude: Klee's measure problem makes three-atom rows hard; orchestrator: the
range encoding step is unproved. (c) Whether Gemini R8's probe-count switch is a forbidden
threshold or an allowed switch between identical outputs (META8 said threshold; META9
reopened it; never settled).

## U2. R10-C3: a nine-node list lost precision (Refused(Fork) instead of Inhabited)

**Program.** `r10_precision_case(tag, reverse)`: nine nodes built by `r3_build` from
`(stop, mask, next)` = (true,63,0), (false,2,0), (false,59,1), (false,40,2), (true,61,0),
(true,61,4), (true,25,5), (true,61,6), (false,47,3), roots [1,2,3,7,8], alphabet 63; that is
`L \ (A1 | A2 | A3 | B4 | C)`. Test: `r10_answer_preservation_nine_node_list_regression`
(ignored, red).

**Verdict now:** Refused(Fork) in both definition orders. **Wanted:** Inhabited, with witness
`[0, 2]` (it is a member; `[]` and `[0]` are not).

**Cause (confirmed by the orchestrator and by both seats).** Main commit 5d72f0689
(GROUP-search-canon-key, "no new value search over an open fork; no cause kept from one"):
the `open_fork` term in `find_rep`, `if self.s().kept_forks > forks || open_fork`. Disabling
only that term gives Inhabited in both orders; 19bc4e25's whole kernel also gives Inhabited.
The commit fixed a query-order dependence, so removing the term is not acceptable (both seats
agree, score 0).

Why no list method decides it (Claude R11, meas/c3-paths.txt): `chain_verdict` None,
`sweep_verdict` None, escape cells (0, 0). The positive row is the bare carrier L, so the
escape's one length ℓ₀ is 1 and it declines; the witness has length 2. The B chains have
optional stops and end at the carrier, so membership depends on the length.

**Methods tried.** Removing `open_fork` (both, diagnostic only, rejected). A loose-transition
witness proposal (Codex R11, not implemented: repeated verification at successive stop
positions can be quadratic, and limiting attempts would need a budget).

**Best open candidate** (Claude R11, not implemented): let the escape accept a carrier-only
positive row by deciding each length 1 .. (largest chain height + 1); every longer length
behaves like the last, since all chains have reached the carrier. Naively O(n²); needs a
per-length incremental solve or a proof that a few lengths suffice. Also open: a full
first-bad-commit bisect of the main commits between 19bc4e25 and f0a7d073d (older kernels do
not compile against the current tests without stubs; /home/luke/Work/wt/rfx-scratch/orch/r11x/notes.txt).

## U3. Shared payloads with atom-named components (the rest of R10-C4)

**Programs.**
- `r11_named_payload_probe` (Claude R11): n tags `#r11tag_i(P)` sharing one payload
  P = union over j < n of `(#r11q_j, j)`.
- `r11_tagged_payload_probe` (Codex R11, `r11_tagged_payloads`): n tags `#r11outer_i(P)`,
  P = union over i < n of `(#inner((i,)), #inner((i,)))`.

**Verdict now and wanted:** Inhabited and Inhabited. Wanted cost O(n log n).

**Cause (argued, from the code):** `fields()` in empty.rs memoizes a payload diagram's rows
once per (length, diagram id) and queues atom-free components once per context, but every tag
still loops over the diagram's named components (`for (i, c) in &rows.named`), K tags × n
components.

**Measurements** (units at n = 1024, orchestrator, /home/luke/Work/wt/rfx-scratch/orch/r11x/
variants.txt, load 21.8 to 26.7):

| probe | Claude R11 fields() | Codex R11 fields() | merged (committed) |
|---|---:|---:|---:|
| r10 shared payload (fixed family) | 9.80M | 12.55M | 12.28M |
| r11 named payload | 505M | 592M | 594M |
| r11 tagged payload | 1.008G | 1.183G | 1.189G |
| r11 payload name prefix (U4) | 1.301G | 1.631G | 1.309G |
| r11 failure prefix | 21.2M | 21.5M | 21.8M |
| r11 many names | 4.08M | 4.44M | 4.74M |

The committed (merged) version costs about 17% more than Claude's variant on the named and
tagged probes; Claude's variant lacks the item context (R11-C4), which is needed (its absence
fails `r11_tuple_fields_within_list_items_scale` at 58.8x and refuses the map-item case). The
17% is not diagnosed; the likeliest source is the second visit per node in item context.

**Best open candidate** (Claude R11, not implemented): index the named components of each
memoized payload by atom name and keep a list of those not yet pushed, so each (component,
name) pair is read once; the X44 tail walk already keys by (node, name).

## U4. R11-C3: payload-bearing name prefixes reread a shared persistent name map

**Program.** `r11_payload_name_prefixes(n)`: a tuple of the n prefix unions
`#r11_named_0((0,)) | ... | #r11_named_i((0,))`. Test `r11_payload_name_prefixes_must_scale`
(ignored, red: 66.3x instructions for 128 to 1024 against a limit of 12.6 on Codex's final
patch; computed by Codex R11). Verdict Inhabited, wanted Inhabited in O(n log n).

**Cause (argued by Codex R11):** every prefix shares a persistent name map, and every name is
in `Atoms::payloads`, so `fields()` and `decide_groups_read` iterate the shared map once per
prefix type. The type visited set does not stop repeated iteration over shared map nodes.
Unlike bare failure names (fixed in round 11 by reading `Atoms::payloads` only), payload
names cannot be skipped.

**Measurements** (instructions, Codex R11): f9ada7ca2 793K, 6.67M, 89.6M, 1.42G at 16, 64,
256, 1024; Codex's final patch 1.63G at 1024 (+14.6%). The committed merged version is
1.309G at 1024 (table in U3), so it has no regression against the base, but the family is
still quadratic.

**Methods tried** (Codex R11): a two-context cache (2.36G at 1024), a node-id shortcut (2.38G;
equal payload wrappers have different node ids), a Type-equality shortcut (1.63G). None
addresses the persistent-map traversal.

**Best open candidate:** an index over the shared map nodes of the persistent name maps
(visit each map node once, as the visited-set rule requires for every DAG traversal), not
only over Type nodes.

## U5. r10padded grows about n^1.5 after the C2 port

Claude R11 reports `r10padded` (`r10_padded_congruence`) at 8.3 times its cost from 1024 to
4096 (meas/q8-bare.txt); Codex's empty-read table shows r10padded linear in empty reads (678
at 1024, 2,726 at 4096), so the growth is outside the empty reads. Not rerun by the
orchestrator; cause not located. Codex R11 notes that cloning a wide projected head per node
remains possible in the C2 projection.

## U6. Q5: the answer certificate across main's canon-key change

Not delivered by any seat in rounds 10 and 11. Wanted: a dump of every named group's answer
on the round-11 head against 19bc4e25, bridged across main's canon-key change (old keys are
not stable), with every narrowing explained. Known narrowings: R10-C3 (U2), and three map-item
wrapper refusals that the item context turned into checked Inhabited answers. Codex R10 had a
partial dump with three narrowings, all the X45 map rule (archive/r10/codex). Codex R9's dump
of 19bc4e25 against cb709f13: 630,616 keys, 0 missing, 0 changed.

### Result (front1, 2026-11-19): every narrowing explained

Method. The R9 tooling keys each answer by the type's digest, which the canon-key change
altered, so it cannot bridge the two kernels. Instead:

- Key: a hash of the printed type (`format!("{t}")`), with the test thread's name
  (`unnamed` for threads a test spawns) and the query kind (`v` for `verdict`, `e` for
  `is_empty`). Only top-level queries were logged, not the ones a search makes inside.
- Corpus: the zed-tests tree of 19bc4e25 itself, run in two scratch worktrees.
  - Tree a: 19bc4e25 as it is.
  - Tree b: the same tests with the kernel files of the round-11 head 22ff3536d.
  Each test binary was run in chunks of 20 tests, each chunk under timeout 60.
- The instrumentation was never committed. It is two wrappers around `verdict` and
  `is_empty` that append one line per answer to a file.

Totals over 77 binaries. Tree a gave 640,352 keys and tree b gave 639,596; 638,400 are in
both. Of those, 737 differ, all in l01_23_subtyping. No other binary has a changed answer.
Its keys found in one tree only are queries the other kernel did not ask:

| binary | only in a | only in b |
|---|---|---|
| l01_16 | 633 (`is_empty` false, mostly single literals) | 0 |
| l01_22 | 5 | 5 (the same types, printed with different `fn N` ids) |
| l01_26 | 572 | 367 |
| l01_27 | 690 | 212 |

The 737 changes in l01_23, from a to b:

| change | named tests | spawned threads |
|---|---|---|
| Refused(NoWitness) to Inhabited | 170 | 1 |
| Refused(MorphismSplit) to Inhabited | 153 | 0 |
| Refused(Fork) to Empty | 82 | 11 |
| Refused(Fork) to Inhabited | 34 | 2 |
| `is_empty` false to true | 4 | 10 |
| Refused(MorphismSplit) to Refused(NoWitness) | 43 | 0 |
| Refused(Fork) to Refused(NoWitness) | 4 | 0 |
| Inhabited to Refused(Fork) | 1 | 222 |

There is no change between Inhabited and Empty in either direction.

- The 14 `is_empty` changes from false to true are types refused before. Of them, 10 are
  Empty in b, and 4 are judgments tests on query order.
- The 223 narrowings are 222 sweep_agreement and r6_reduction cases plus
  `oracle::the_two_routes_agree_on_recursive_systems`. All 223 come from one term:
  `open_fork` in `find_rep`, added by 5d72f0689 (GROUP-search-canon-key, "no new value
  search over an open fork"). That commit is an ancestor of 22ff3536d.
  - Check: tree b was rebuilt with the term switched off (env `U6_NO_OPEN_FORK`) and
    l01_23 was run again. All 223 keys answer Inhabited, as in a.
  - The other 514 changes are unchanged by the switch.
  - The term stops the verdict from depending on query order (the reason for
    5d72f0689), so these narrowings are accepted, of the same kind as R10-C3 (U2).
    Removing the term is not an option.
- The three map-item wrapper refusals named above were not looked for on their own. If
  their tests are in this corpus, they are among the 737 changes, and the 223 narrowings
  are all in l01_23.

Limits of the certificate:

- The printed type omits definition bodies, so two types can share a key. A few keys in
  the current-kernel run below have more than one answer, probably for this reason.
- A test that failed or timed out logged only the answers before it stopped. In tree a,
  14 of 397 l01_23 tests did not pass: scaling tests under load (up to 97), and one
  timeout (r6_reduction). Tree b had the same, plus four refusals tests whose expected
  messages changed.
- Gains (a refusal becoming decided) are not proved one by one. Where the tests have an
  exact oracle, they check them against it.
- The script that ran the chunks printed `basename`'s exit status instead of the test
  binary's. The counts above come from the test logs, not from that status. Recounted per
  chunk:
  - tree a: 251 passed, 23 failed, 19 gave no result;
  - tree b: 252 passed, 24 failed, 17 gave no result.

### The current kernel against 19bc4e25 (beyond Q5)

This compares the 19bc4e25 tests on 75a3ed206. They were copied in as a test binary
`u6old`, with small shims for API changes. Some old tests fail on newer messages and print
forms (343 of 397 l01_23 tests pass), so the coverage is partial. Diagnostics ran on the 24
sweep_agreement tests and on r6_reduction until its timeout.

| run | Inhabited to Fork | Empty to Fork | `is_empty` true to false |
|---|---|---|---|
| no switch | 267 | 8 | 8 |
| `open_fork` off | 16 | 6 | 6 |
| `forked` off (the K35 `past_fork` rule) | 17 | 6 | 6 |

The run with no switch gives the same answers as the chunked run on every common key, so
it is deterministic. The `open_fork` term again explains all but 22 narrowings: 16
Inhabited to Fork and 6 Empty to Fork.

Those 22 are new after the round-11 head:

- 18 are decided in tree b (12 Inhabited, 6 Empty).
- 4 are refused in b but Inhabited in b with `open_fork` off.
- All come from tests with exact oracles that accept a refusal: sweep_agreement families
  xc, xp and r7rc, and r6_reduction cases r6sat.

One of them was traced: `34eead6370d677c5`, xc2359, Empty in a and b. The refusal comes from
the K26 fork refusal in `tuples_on` (`self.refuse_fork()` after the `classes` split and the
key-region pass), reached from `Search::solve`.

The commit that moved this type there is not found. 188 kernel commits lie between 22ff3536d
and 75a3ed206, and `tuples_on` changed in several of them:

- the key regions of 10c13b7c7 and 34a583731;
- `take_blame_on_false`;
- `nested_cover` and `take_out_piece` inside the loop.

This is filed as REFUSAL-front-post-r11-forks. The keys, the dumps and the switch method are
under /home/luke/Work/wt/scratch/front1-u6 (x1nar.k and the cmp* directories). The scratch
trees are removed.

## U7. Case A proof and Mutant 2 (needs a second reader)

Codex R11 wrote the per-child transition and dominance argument for narrowing r0 to
`rem_cuts` in `find_prefix_chains` (review-record/r11/codex/R11_CODEX.md, section Q4): the
narrowing holds when `!step_loose`, `non_disjoint_stop_heads` is empty and `spine_u1` is None.
It argues Mutant 2 (dropping `!step_loose`) changes only precision, never an Empty. Claude did
not review it. Open: a second seat's reading, and a whole-program mutation or order test
(Codex names this as its claim most likely to be wrong).

Second reading and mutation run (front1, 2026-11-19, on 75a3ed206). Steps 1 to 7 of Codex Q4
were checked against today's `find_prefix_chains` and hold:

- Pass 1 and Pass 2 store a forced child as `None` and leave it `None`. A partial group whose
  tokens all jump cuts `Some(rem_w)` by its head per child, through `jump_target` or the
  `multi_partial_groups` event loop, so `rem_w` is R less the union of the heads landing at w.
- A group with staying tokens sets `step_loose` instead.
- The dominance in step 6 rests on three facts. The rest of the problem depends on x only
  through the set of live tokens. Positive heads and the decided negative groups treat every x
  in R alike. A larger set of live negative tokens never admits more lists. So an x in every
  `rem_w` leaves exactly the forced tokens, and every other x leaves at least those.

The Mutant 2 argument is written at the guard. It covers both readers of the narrowed `r0`: the
same-step return guarded by the earlier steps' `had_loose`, and `witness_heads`.

Mutation run: the guard without `!step_loose`, with a line printed each time the narrowing ran
on a loose step. All 578 zed-kernel lib tests and all 747 l01_23 tests ran one at a time.

- Every test passed, except the bench `judgments::bench::a_meet_of_unions_of_functions_scales`.
  It timed out at 60 s at load 95 and passed on the unmutated tree. That bench does not reach
  the guard: it printed no line before it timed out.
- The mutant ran on a loose step 18 times: 14 in
  `sweep_agreement::r7_random_optional_spine_choices_against_masks` and 4 in
  `r9_run_tokens_against_product_automaton`. Both tests check every case against an exact
  decider (the masks, and a search of the rows' product automaton) in both definition orders.
- So the mutant survives, as the argument predicts: it is sound, and no test can tell it apart
  by its verdicts.
- Nothing in the suite measures what the guard buys in precision. The guard is kept as Codex
  kept it.

## Follow-ups outside this item (recorded, not part of the remainder)

- X7: the `end` family (`L \ by_place_from_the_end(n)`) costs n^1.5 to n² before it refuses
  (main's cost; patch within 1.3% of main at 16 and 64, Codex R11).
- X13: the base search's verdict depends on query order where the new path declines.
- r6twowide (68.4G units at 64) and r6threeun (7.0G at 64): main's own cost, patch within 1.6%
  of main (Codex R11).

## Seats' readiness

Every seat has said NOT READY in every round since round 6, except Gemini's READY in rounds
6, 7 and 8, each rejected by the orchestrator for wrong Empty answers or quadratic families
(META6 to META8). Round 11: Claude NOT READY, Codex NOT READY.
