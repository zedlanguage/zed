Campaign xe: open-problem consultation on polynomial type emptiness in zed-kernel (types/bdd.rs, types/empty.rs). Models: gpt-6.1-sol at medium effort (Codex), gemini-4-argon at high effort (agy), claude-opus-5-5 at medium effort (Claude).

Round 1: baseline zed-impl e135800; all three reported. Author's decisions of 2026-11-01 below.

| ID | raised (round, agents) | short statement | decision and reason | changed in (round, commit) | status |
|---|---|---|---|---|---|
| X1 | r1 Sol, Claude | `no_morphism` read "not proved empty" as "inhabited": unsound | accepted | 967100a: a key must be shown by a built value | fixed |
| X2 | r1 Gemini, Sol | `forced` (dominator walk) missed an atom on two nodes; quadratic walk | accepted | f881a39: exact, O(n log n) | fixed |
| X3 | r1 Sol | equal Expr DAGs built separately compared in 2^depth | accepted | 96e1bec: pairs compared once | fixed |
| X4 | r1 all | decision tree cubic in c | accepted; input is Theta(c^2), so Omega(c^2) is the lower bound and O(c log c) impossible | 6530287 is Claude's Cuts table: O(c^2) in either column order (c=128 181 ms, reversed 191 ms). Sol's trie: 6.6x faster in order, cubic reversed (c=256 17.2 s); not adopted as a second path; its constant to study in round 2 | fixed |
| X5 | r1 Claude | search: one answer per type, only a checked value is permanently "inhabited" | accepted as the base; soundness for recursive morphism types (W = (W)->int) must be proved, likely by a fixed-point theorem | | open |
| X6 | r1 Gemini | narrow a column to the union of its tuple types first; `forced_to` | accepted | | open |
| X7 | r1 Claude | exact below a size limit, else pair projection; Empty/Inhabited/Unproved | REJECTED: behavior switches at a size threshold | | rejected |
| X8 | r1 Claude | keep a zip BDD only below a result size | REJECTED: equal types stop comparing equal from depth 4; behavior switch | | rejected |
| X9 | r1 Claude | print `let` only above expansion 8; `(let ...)`/`(if ...)` in messages | REJECTED as thresholds and as non-type syntax: messages must print the syntax users write; extend type syntax only if it adds expressiveness | | rejected |
| X10 | r1 Claude, Gemini | PAIR = 2; rows count at least 2; cap of 3 state changes; width <= 2 | REJECTED: numeric limits | | rejected |
| X11 | r1 Claude | memo kept across queries makes answers order-dependent | REJECTED: batch (whole program) and incremental (one file) checking must give identical answers; both must work | | rejected |
| X12 | r1 Claude | "not proved" vs "counterexample" messages | each error condition gets its own message | | open |
| X13 | r1 measured | still exponential at HEAD or in prototypes: E4b n=3 (HEAD >60 s); choice-chain build (HEAD 18.4 s at d=23); mux = mux2 must stay true and fast; union of nth_from_end(1..n) (Gemini 23 s at n=11) | must become polynomial, ideally O(n log n), for the vast majority of reasonable cases; pathological cases may be refused by a structural error, never by a size switch | | open |

Round 2: baseline zed-impl f425b32, zed cb3d910. Sol triage of round 1 is folded into BRIEF2. X12, X13, X5, X6 remain open.

Round 2 finished 2026-11-02: baseline zed-impl f425b32, zed cb3d910; same models; all three reported, exit 0. Reports: archive/r2/R2_{CLAUDE,CODEX,GEMINI}.md. No round 2 design has been merged. Implementation waits for round 3 and the orchestrator's synthesis, by the author's order: all three reports, then each agent critiques the others, then the orchestrator checks everything and synthesizes one unified design, and only then is it implemented. Meanwhile item T4 (Omega test, S18) failed three implementation attempts, on branch t4 (cfb4985), for the reasons listed under Q9 of BRIEF3; it was stopped to wait for this synthesis. Status of X5, X6, X12, X13: still open, pending round 3.

Round 3 finished 2026-11-02: three reports with peer critique (wt/xe3), then six cross-check agents, one per question group (wt/xv/<group>/REPORT.md), each rebuilding all trees against brute-force oracles with controls. The orchestrator's unified design is wt/xv/SYNTHESIS.md. X5 closed (Claude's search, 0 wrong in 200,000 systems; DESIGN.md:1675 fixed-point sentence corrected: morphism cycle = inhabited, tuple cycle = empty). X6 kept (Gemini's forced ported into Claude's tree). X12 closed (one message per refusal cause, with span). X13 becomes T6 scaling tests. New X14: one large tuple SCC is quadratic (Büchi-game reduction, inferred); a count-based refusal is rejected as a threshold; sent to a hard-algorithm cross-review. Implementation starts with T4 on the synth tree.
