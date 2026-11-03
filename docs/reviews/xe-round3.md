# Cross-review xe, round 3: the unified design

Date 2026-11-02. Inputs: the three round-2 reports (archive/r2), the three round-3 reports with peer critique (wt/xe3/*/R3_*.md), and six cross-check reports, one per question group, in wt/xv/<group>/REPORT.md. Each cross-check rebuilt the four trees (HEAD, Claude, Codex, Gemini), ran them against brute-force oracles with negative controls, and measured scaling. Where a cross-check report gives a number below, the number is from that report; I re-checked three claims myself (marked "checked").

Plan ids: T4 = Omega test and integer semantics (Q9). T5 = Cuts table and emptiness narrowing (Q6). T6 = inhabitation, order independence, finite listing, printer, BDD (Q1–Q5, Q7). ST1/ST2 = Scope::narrow and product.rs precision (Q8). T12-Z4 = memory planner (Q10).

## Facts every part rests on

1. **No tree calls the solvers from the checker.** `grep` for presburger, preimage and product callers outside crates/zedc/src/store/ finds nothing (checked, exit 1). pugh.zed compiles with no diagnostic. Refusals are dropped at preimage.rs:316, :319 and product.rs:1239. So every refusal below must become a compile error with a cause and a span, and each part gets an end-to-end test through `zedc check`.
2. **Pointer-keyed memos are wrong.** Gemini's `list` memo in bdd.rs (keyed by `Arc::as_ptr`) gives 4 wrong lists in 1800 (checked by grep, bdd.rs:949–1462). Gemini's Q10 pointer keys differ on 227 of 714 plans. Codex's certificate keys on `Arc::ptr_eq`. Rule for all parts: memo keys are canonical structure or interned ids, never addresses.
3. **Spec sentence DESIGN.md:1675 is wrong** (checked): "Emptiness assumes empty a type met again while it is being decided ...". A type met again under a morphism is assumed inhabited (greatest fixed point); one met again under a tuple is assumed empty (least fixed point). Groups are decided bottom-up, because the step function is not monotone across groups.

## Q9 / T4: integer constraints (Omega test)

Base: the `synth` tree (Claude's solver plus a canonical order by color refinement, Gemini's local repair of disequalities, Bland's rule), with Gemini's lazy composition and refusal fields (`Preimage.refusal`, `Scope.refusals`) and Codex's union-find for ties. Codex's point checks are dropped. Measured: 0 wrong in 40,000 brute-force systems; the planted bugs are caught (MUT1, MUT2); refusals do not change under renaming (0 of 8, against Claude's 19 of 22).

Work, in this order:
1. Wire the solver into the checker. A refusal is a diagnostic with its cause and span. pugh.zed becomes an end-to-end test with expected output.
2. Replace the bounded dive with Pugh's exact dark-shadow and gray-shadow (splinter) search. Refusal is decided by a structural criterion of the system, never by a count.
3. Decide two-variable-per-inequality (UTVPI) systems with the zero-weight SCC parity test (0 wrong); use the rational LP only as a proof of rational infeasibility. Gemini's "parity tightening" is rejected (902 wrong, and not in its code).
4. Decide two-variable integer feasibility exactly (it is polynomial) instead of refusing 2-variable slabs.
5. `Lin` coefficients use `Int`, not i128: the i128 refusal is a size cap. Rows reach 359 digits, so Gemini's "max coefficient 15" is refuted.
6. Bland's rule pivots grow as about 2^(0.7n) on shifted sparse systems. Use it only as the anti-cycling fallback of a steepest-edge or Dantzig rule, and add the shifted family as a scaling test.
7. Models need Ω(n²) bits (about 1.957·n²). Decide without building the model; produce the model on demand, only for a message.
8. Fix the 3 failing step tests (a different valid countermodel: compare by checking, not by text; a model wider than 128 bits: follows from item 5; one random-test refusal: follows from items 2–4).

Continue on wt/t4 (cfb4985) and wt/t4-spec (6892067).

## Q8 / ST1, ST2: Scope::narrow and product.rs

Base: Claude's spine with switch set SW=446 (F2 + F3 + F4 + J + PK + F1e: no carried negation in `sides`, sides sorted before join, worklist in project_block, joint projection on a repeated bound move, sides grouped by relation names, equalities hashed into part keys). Measured: linear on every fixed-name shape, 0 unsound, no dependence on order, ST2 B1 and B2 fixed, ping and walkrel reach the fixed point, 39 of 41 repository tests pass. Codex's threshold-tree API is not adopted (never called; it would be a second path). Gemini's "two cycles reach the fixed point" is refuted: the chain needs n−2, and any fixed count is a threshold.

Fixes:
1. F2 loses per-name facts in 2 of 300 cases: carry the negation into the per-name products only.
2. Update the 2 failing tests; their new constraint sets are subsets of the old ones (check each).
3. F6 computes the test's relation before narrowing; add if-inside-or to the generators.
4. `pairs` is quadratic: keep a persistent names map. `thresh` is quadratic: flatten `if c {t} else {false}` to `c && t` and the then-arm chain with it.
5. walkrel grows ×4 per doubling: find the quadratic step and replace it with a lookup.
6. B4 (inequalities only) is missed soundly: record it as a known precision limit in COMPLEXITY.md with its test.
7. Scope::join grouping agrees on 299 of 300: in `either`, state a top-relation side's finite per-name products as constraints.

## Q2, Q3 / T6: inhabitation and order independence

Base: Claude's search with the strict verdict (0 wrong; the others are unsound: HEAD 5,094 wrong "empty", Gemini 2 wrong "empty" and 31 wrong "inhabited").

1. **Canonical form.** Definitions are numbered by a fixed traversal; names are ignored. Add the rename test. This removes Claude's 18 name-dependent answers.
2. **delcheck worklist**: deletion with counters, re-check only the tuple SCCs that lost a member, synchronous rounds. 0 wrong in 200,000 systems; chain n=4096 in 12,291 steps.
3. **Refusals** carry Codex's `ProofRefusal` causes and become a diagnostic at the span of the SCC's head definition, listing its definitions.
4. **Cache.** Tables keyed by canonical type: PROVED_EMPTY (proof with no open assumption) and WITNESSED (checked witness). Results resting on an assumption stay per query. A refusal is a function of the canonical type only. Tests: cold, batch, reversed, rename, built-apart copies, on both entry points; a keep-first-answer mutant must fail them.
5. Fix DESIGN.md:1675 as stated above.

**Open (X14): one large tuple SCC is still quadratic** (235M steps at n=4096). The positive fragment reduces to a Büchi game (the reduction is inferred, not proved), for which no O(n log n) algorithm is known. Refusing an SCC re-checked more than k times is a count, so it is rejected. Decision: this goes to a hard-algorithm cross-review round now, in parallel with T4 (see below); T6 needs it only after T5, so nothing waits on it.

## Q1, Q7 / T6: emptiness verdicts and the BDD

Base: Claude's search, for soundness and determinism. The Q1Q7 cross-check recommends Gemini's tree as base for speed, but Gemini answers "inhabited" on unsatisfiable pigeonhole n=4 and 5 when warm (it reads MEMO), and Q2Q3 shows it unsound both ways. So port Gemini's fast parts into Claude's tree:
- Gemini's one-pass `forced` with Claude's split (each alone is quadratic in the other's half).
- XOR nodes for parity diagrams only (n=48: 71 nodes, width 6, against 8105 without). Gemini's 2n(n+1) bound is refuted at Part level.
- The chain rule and `Expr` sharing.
- verdict and subtype_verdict must agree on every case (Claude's tree disagrees on 3): one route.
- 2-SAT parts are decided (linear), not refused.
- Refusal cost must be O(n log n); today it is about N^1.35 in both trees.
- Codex's certificate is never called and is not adopted.

## Q6 / T5: the Cuts table

Gemini's Cell table (9.50 G instructions at c=1024, best measured), without its Scalar case and without its pointer-keyed `list` memo. The prefix trie is rejected (c^2.93 with columns reversed). The Ω(c²) lower bound stands (DESIGN L1.23).

## Q4 / T6: finite listing

Remove both listing size rules (both change behavior with size). In their place:
- `Type::finite()` with an explicit stack, used by stage.rs `trick`;
- integer lists for exponent and product;
- a lazy value iterator for tuples (product.rs:363);
- a refusal with its own message when a type is not known finite.

## Q5 / T6: the printer

No tree prints correctly. Build one printer over the whole type graph: a global memo keyed by Type, names given in postorder, a definition for each node used twice or more, Gemini's leaf text. A struct prints its surface name; a part whose leaf is true prints as the complement; a recursive type prints its Group. Messages use the printer, not Display. Spec and grammar gain the one-tuple `(T,)` and `L .. U -> V`, written in DESIGN prose and sec:grammar together. Test: `xp cases` 449 parsed, 449 equal; output size linear on the shared-1000 case.

## Q10 / T12-Z4: memory planner

Occurrence ids with a memoized resolve, then integer plan keys. Gemini's pointer keys are rejected (fact 2).

## Issue table updates

| ID | decision |
|---|---|
| X5 | closed by Q2Q3: Claude's search is sound on 200,000 random systems; the fixed-point rule is the corrected DESIGN.md:1675 |
| X6 | kept in Q1Q7 as Gemini's forced/narrowing ported into Claude's tree |
| X12 | closed: each refusal cause has its own message (Codex's ProofRefusal causes) and a span |
| X13 | split: E4b, the choice chain, mux≡mux2 and the nth union become T6 scaling tests with n and 8n, measured on the merged tree; the large tuple SCC is X14 |
| X14 | new: one large tuple SCC is quadratic; hard-algorithm cross-review |
