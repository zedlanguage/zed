# X14 (cross-review xs): the large tuple SCC — decision

Orchestrator's synthesis, 2026-11-03. Inputs: round 1 and round 2 reports in /home/luke/Work/wt/xs2/{claude,codex,gemini}/ (R1_*.md, R2_*.md, with peer critique), the cross-measure in /home/luke/Work/wt/xs-cmp (src/, logs/), and the split_bdw2 fix run (logs/bdw2/, diff at /tmp/claude-1001/-home-luke-Work-zed/d9cf9445-8c38-402a-9cb6-5af85b56359b/scratchpad/bdw2.diff, the same change is in xs-cmp/src/gemini.rs).

## Decided

1. **Decider: `split_bdw2`** (xs-cmp/src/gemini.rs:3331, `check_residual_sr_amc2` at :3367, `struct Stamp` at :3337). It is Gemini's `split_bdw` (grounded core, then the witness-DAG delcheck with the structural refusal SR-AMC) with one change: the successor dedup in the residual check uses a generation-stamp array, O(outdeg) per node, instead of `Vec::contains`, O(outdeg²). The stamp generation is reset at `u32::MAX`; there is no size switch.
2. **Admission check: Gemini's `flipped_complete`** (xs-cmp/src/gemini.rs:868), replacing `Group::flipped`, which accepted non-monotone groups.
3. **Refusal**: what SR-AMC cannot decide is refused with its own message naming the cause and span (X12's rule), never by a count or size.

## Evidence (all measured, logs in xs-cmp/logs/)

| candidate | wrong (6 generators × 200,000 systems, vs naive, classical and Büchi references) | refused systems per 200,000 | scaling, 35 families, 512→4096 | widened variants |
|---|---|---|---|---|
| split_bdw2 (chosen) | 0 | 846–4,150 (identical to split_bdw node for node) | ≤ 8.03 | ≤ 8.01 at 512→4096 and 4096→32768 |
| split_bdw (Gemini) | 0 | 846–4,150 | ≤ 8.05 | up to 13.93 at 512→4096, 36.92 at 4096→32768: quadratic |
| combined (Codex) | 0 | 1,574–6,531 | ≈ 8.15 | — |
| splitD1 (Claude) | 0 | 1,499–6,696 | ≈ 8.33 | — |
| splitC (Claude) | 0 | about twice splitD1 | — | — |

- Order invariance (perm, perm_shuffle, local): 0 differences for all candidates.
- split_bdw2 vs split_bdw: 0 differences per node over about 1.2M systems; same refusals.
- Admission checks on the named systems (logs/admit_*.log): `flipped_complete` 0 misses, 18,854 false rejections; Codex's repair 0 misses, 24,328; Claude's `fixed2` misses M5_ref, CodexXY, W_and and one random group: unsound, rejected. All three falsely reject `W_andTop = (A (M R0 R0 int) top)`; that is a refusal, not a wrong answer, and is left as a known refusal.
- Gemini's harness flaw (unknown heads read as Top, morphism bounds ignored) is fixed in xs-cmp; its published oracle counts reproduce exactly (Forward 5000: 0 wrong, 1 refused; Reverse 2771: 0 wrong, 1 refused).

## Rejected

- Count- or size-based refusal of a large SCC: a threshold.
- `fixed2` admission: unsound (four misses above).
- Deduplicating `g.c` when the graph is built: changes the graph other code reads; the stamp is local to the check.

## For T6

Port split_bdw2 and flipped_complete into zed-kernel types/empty.rs (and wherever the delcheck worklist lives), with: the 35 families and the worst widened variants (exring:6:1, defeatgsr:6:42:and, indirect_alt_ladder:6:7, g_codex_adversary:6:24:mor, tiles:6:0:mor) as scaling tests at n and 8n; split_bdw (the Vec::contains dedup) as the negative control, run once and not committed; the named admission systems (logs/named.txt) as correctness tests, W_andTop expected refused.
