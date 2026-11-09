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

## GROUP-setop: recursive members under `&` and `\` (2026-11-09)

Decision: **Gemini's positive skeleton is adopted**; Codex's flat refusal is rejected.

The group decider (`types/empty.rs` `judge`) reads a meet `a & b` with a recursive occurrence as an `And` node of its operands, and a difference `a \ b` as `a` (admission keeps a recursive occurrence out of a complement and out of the right of `\`). Each node holds at least the values of the type it stands for, so the system over-approximates inhabitation: an `Empty` answer is exact, and the member is not searched. An `Inhabited` answer is not exact on a node that reaches a meet or a difference (`#a & #b` is empty while both operands are inhabited; `#b \ #b` is empty while `#b` is not), so those members, found by one reverse walk with each node visited once, go to the search, as every member of such a group did before.

The plan row's two conditions, measured:

- No wrong `Empty`: the nine `group_oracle` sweeps pass with the skeleton, and their verdict tallies are identical to those of the search form.
- The search is skipped: `Type::members_searched` counts the members sent to the search. Sweeps, search form to skeleton: cells 184 to 161 and 226 to 213; mixed 97 to 88 and 122 to 117; claude (24 and 0) and layer (11 and 13) unchanged. A meet of k members with one empty operand sends none (the search form sent all 2k + 2).

Meets of k members (`l01_23_subtyping::setop::meets_of_k_members_scale`, k 8 and 64): one empty operand, 603K to 4.34M instructions, 7.2 times (limit 17.6), no member searched; all operands inhabited, 609K to 4.33M, 7.1 times, the meet alone searched. In the search form the first family cost 3.15M to 73.2M, 23 times, in a probe.

The exponential case, named: a meet whose product of states the search must walk, the meet of k parity lists (even count of each of `0..k`, odd length; `2^(k+1)` product states). Its verdict is `Refused(Fork)` (COMPLEXITY.md K35) after a search for a value: 178M, 1.11G and 4.51G instructions at k 2, 3 and 4, in either form. `is_empty` counts it inhabited at 24.0M and 257M instructions at k 4 and 32, 10.7 times (limit 22). Follow-up VERDICT-fork-value: the value `[k]` has length 1, so the search for a value after a fork need not walk the product.

Rejected:

- Codex's flat refusal (R2_CODEX.md, `RecursiveSetOperation`: refuse every obligation still holding a meet or difference that depends on a member). Control, not committed: a refusal of every obligation holding a meet of recursive types fails `rec::products_of_recursive_types` (`multiple(2) & multiple(3) & multiple(5)` against `multiple(30)`), which the search decides today.
- Keeping the search alone: same verdicts, but every member of the group is searched, and the one-empty family is superlinear (23 times at k 8 and 64).
- Trusting the skeleton's `Inhabited` answers: wrong on `#a & #b`. Control, not committed: reading `a & b` as `a` leaves the one-empty meet to the search, and `a_meet_with_an_empty_operand_is_empty_with_no_search` and the scaling test fail on their counts.
