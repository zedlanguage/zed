# Design: the non-expanding products solver (row PRES-products-factored-solver)

Agent b22-factored1, 2026-11-24, phase 1d (META3 R3-1 to R3-8 applied; the phase-1c text is
`$S/design-1c.md`, the phase-1b text `$S/design-1b.md`). Base code: wt/b22-presburger4-5 at
9bff04425 (copies `$S/pairs-9bff.rs`, `$S/presburger-9bff.rs`; P: = presburger.rs, K: = pairs.rs),
`$S` = /tmp/claude-1001/-home-luke-Work-zed/d9cf9445-8c38-402a-9cb6-5af85b56359b/scratchpad/b22-factored1.
Prototype: `$S/proto/factored2.rs`, which includes `factored.rs` (phase 1: oracles, builders),
`stage2.rs` (stage A' of sec. 3), `tests2.rs` and `tests3.rs` (the tests of sec. 8). Build:
`rustc --edition=2024 -O -A dead_code factored2.rs`; `timeout 60 ./factored2 <part>`, outputs
`$S/proto/run14-<part>.log`. 56 parts, each under 60 s; 55 exit 0 and `wlgrowg` exits 101 (the
failing test of exception 4). run13 and run14 agree apart from `ms=` on every unchanged part.
Parts `cone1` and `bmm` (A225 items 2 and 3) were added after run14 and log to run15-*.log.

Marks: **[proved]** means a proof is in this file. **[computed]** names the prototype part and
the line it prints. **[inferred]** names what would confirm it. **[cited]** gives the source.

## 0. Summary of the result

Sizes used throughout. For the residual R (the pairs stage A' keeps), W_R = Σ_R |a||b| (the
product atoms written out), W_full = Σ_R (|a|+1)(|b|+1) (every term of the expanded rows), and
E_R = the number of terms in the form of R that is written (sec. 4). |a| counts variable terms.
L is the set of pairs pass 1 lists, and W_listed = Σ |a||b| over the pairs the exact peel receives.

1. **Theorem D** (sec. 2) is exact over the integers and over the rationals [proved]. `kept`'s
   single-holder rule is its |D| = 1 case.
2. **Stage A'** (sec. 3) drops pairs along sign directions, never forming a product or listing
   the pairs of a wanted product on[x] × on[y]. Its result does not depend on the order or
   naming of rows and variables [proved; computed on 13,000 instances, 26 cases × 20 renamings].
   Sets are exact trie ids; no hash value stands for a set (R3-1). It runs to a joint fixpoint
   with `kept`'s count rules and the exact single-holder peel, all counted in the work.
3. **R** is written in factored form, E_R ≤ W_full ≤ 4·W_R when |a|, |b| ≥ 1 [proved].
4. **`products` has no product-size refusal.** R goes to `satisfiable`, which may rewrite it up
   to its direct size, no more than 9bff hands it today (R2-5). Backend refusals stay.
5. **Cost.** At n and 8n, 42 of 49 families have a work ratio ≤ 10.5, all but two ≤ 9 [computed,
   run14]. The other seven are under exceptions of sec. 5.3, each tested at its bound: pass-1 OV
   (1), moment_curve and o2_distinct (2), the peel on sum_no_count, wlgrow, p4_open (3), P4 (3b),
   the worklist on wlgrow_g (4). Exception 4 has no method within O(n log n); its test fails.

## 1. The question

Rows a, b are linear forms over integer variables. A pair (a, b) stands for the product row
a ⊗ b ≥ 0. The **linear reading** asks whether base ∧ ⋀_{(a,b)∈P} lin(a ⊗ b) has an integer
point, where each product atom w*z is an opaque integer variable y_{wz} = y_{zw}. Write
a = a_0 + Σ a_w w, so lin(a⊗b) = a_0 b_0 + a_0 Σ b_z z + b_0 Σ a_w w + Σ_{w,z} a_w b_z y_{wz}.
The coefficient of y_{wz} (w ≠ z) is a_w b_z + a_z b_w, which can cancel.

Atoms are split in two:
- **mentioned atoms** M: those in a premise, the goal or a definition (`partners`,
  P:29052-29068);
- **free atoms** U: all other atoms, which occur only in pair rows.

**Input (R2-1).** The crate's input: factor rows, one list on[x] per factor x, the wanted
products (x, y), each meaning all pairs on[x] × on[y], and `partners`. Its size is
k = Σ_rows(|r|+1) + |wanted| + Σ|partners| (P:29088-29092). A list is one object however many
wanted products name it. The prototype's `kp` adds Σ|on[x]| over distinct nonempty lists, so
it is at most 2k. m rows on x and m rows on y are 2m in k, not m².

**Assumption A2 (R2-7, closed).** Step 0's dominance drops (a + c, b) only where b ≥ 0 is
certified. All tiers decide integer points by `linear_reading` (P:28624-28657), and `table`'s
factor rows are premise rows and bound rows of P:28976-29033, which hold at every integer point
of the premises (Codex, META2 R2-7). Sec. 8 test 6 is the rational control.

## 2. Theorem D (dropping pairs along a direction)

**Theorem D.** Let L be the set of pairs in play and D ⊆ L. Suppose there is an integer vector
u on the free atoms U such that, for every pair r ∈ L, c_r(u) := Σ_{y∈U} coef_r(y)·u_y ≥ 0,
and c_r(u) > 0 for r ∈ D. Then base ∧ L has an integer point iff base ∧ (L ∖ D) has one.

*Proof.* (⇒) Dropping rows keeps a point. (⇐) Let x be an integer point of base ∧ (L∖D).
For an integer t ≥ 0, put x_t = x + t·u (u is zero outside U). Atoms in U occur in no base
row, so x_t satisfies base. For r ∈ L, lin_r(x_t) = lin_r(x) + t·c_r(u). For r ∈ L∖D this is
≥ lin_r(x) ≥ 0. For r ∈ D, c_r(u) ≥ 1, so lin_r(x_t) ≥ 0 for the integer
t = max(0, max_{r∈D} ⌈−lin_r(x)⌉). x_t is an integer point. ∎ [proved]
Over the rationals the same t works: x_t is rational, and t is chosen by the same formula (R3-8).

*Corollary (order).* After dropping D_1 with u_1, apply the theorem again on L∖D_1 with u_2.
By induction the verdict on L equals the verdict on the final residual R. [proved]

*Special case.* `kept`'s single-holder rule (an atom held, with a nonzero coefficient, by one
live pair) is the |D| = 1 case u = ±e_y. A pair whose atoms are all mentioned (a **closed**
pair) has c_r(u) = 0 for every u: it is never dropped and constrains no direction.

*Literature.* The largest D is the maximum-support set of a homogeneous system (Tucker), one
LP (Peña and Soheili, arXiv 2003.08911 [cited, L38]). Stage A' does not compute it; a pair it
misses goes to R.

## 3. Stage A'

In the prototype: `stage_a2` and the struct `J` in stage2.rs.

**Step 0. Canonical rows, dominance and the 2-D cone rule (R2-7, R2-11, R3-3).**
- Each row is divided by g, the gcd of its variable coefficients; its constant becomes the
  reduced fraction c/g. Rows equal after this are one class, and the row of least g stands
  for it, so the choice depends on content only, never on an index.
- On each side, among the rows of equal normalized linear part ℓ, only the least c/g is kept.
- **Cone rule** (`cone2`). On each side list, the rows whose homogenized vector (coefficients and
  constant) has exactly two nonzero coordinates, p and q, are grouped by (p, q). In a group of
  n ≥ 3 rows whose directions (a_p, a_q) fit in an open half-plane, every row strictly between
  the two extreme directions is dropped from the list, with all its pairs. Cost O(r log r) for a
  group of r rows (a sort by angle). Other groups and other rows are left as they are.
- A wanted product with an empty side is dropped before step 1, as P:29111 does (R2-8).

*Proof of dominance.* Let a = g(ℓ + c) and a' = g'(ℓ + c') with c' ≥ c and g, g' > 0. Then
lin(a'⊗b)/g' = lin(a⊗b)/g + (c' − c)·b. Where b ≥ 0 is certified (A2), (a, b) and base imply
(a', b), and dropping (a', b) keeps the verdict. [proved]

*Proof of the cone rule.* Sort the group's directions by angle. The directions fit in an open
half-plane iff exactly one circular gap between neighbors exceeds π (cross product < 0); the
other gaps then sum to less than π, so every direction lies in the closed arc from the first
row e_1 after that gap to the last row e_2 before it, an arc shorter than π. A direction v in
that arc is v = λ_1 v_1 + λ_2 v_2 with λ_1, λ_2 ≥ 0, not both 0: v_1 and v_2 are independent,
and Cramer's rule gives λ_1 = (v × v_2)/(v_1 × v_2), λ_2 = (v_1 × v)/(v_1 × v_2), both ≥ 0 since
v lies between them in an arc shorter than π, and rational since the entries are integers. Both
rows have only the coordinates p, q, so as linear forms a = λ_1 e_1 + λ_2 e_2. The map
(a, b) ↦ lin(a ⊗ b) is bilinear: each coefficient of lin(a⊗b) is a sum of products a_i b_j, and
the atom y_{wz} is the same variable in every pair. So for every row b of the other side,
lin(a⊗b) = λ_1 lin(e_1⊗b) + λ_2 lin(e_2⊗b). The wanted product pairs a, e_1 and e_2 with the same
rows b, so wherever (e_1, b) and (e_2, b) hold, (a, b) holds: base ∧ L and base ∧ (L minus the
pairs of a) have the same points. This needs no sign of b, so not A2, and it holds over the
integers and the rationals. Later drops by Theorem D apply to the smaller L, and the corollary
of sec. 2 covers them. ∎ [proved] Tests: `cone` (sec. 8 test 11).

The rule does not apply to moment_curve: its rows a_i = x + iz + i²w have three nonzero
coordinates. Gemini's folded form of that family (its E_R ratio 12.70 against 56.70) is not
adopted; phase 2 measures it through Omega, where its coefficients, which grow with m, are
rewritten.

**Step 1. Components with parity.** Union-find with union by rank and parity over the rows and
one node per distinct nonempty side list (R2-1). Each row joins its side node with parity 0,
and a wanted product joins its two side nodes with parity 1. Both rows of every pair lie in
one component, on opposite parities. A component whose parities conflict (a row reaches both
sides) is **odd**. Cost O(k α(k)). [proved]

**Step 2. Two frames.** For frame+, H is the bipartite multigraph between components and
variables, one edge (comp(r), w) of sign sgn(r_w) per live row r and w ∈ r. Frame− is the
same with sign sgn(r_w)·(−1)^{par(r)}, rows of odd components left out.
- A block of H is **unbalanced** if it has a cycle with an odd number of negative edges. Z0 is
  the set of variables in unbalanced blocks (Tarjan, then a parity BFS in each block).
- The **parts** are the connected pieces of H − Z0, and ρ is a 2-coloring of each part's
  components with sign·σ_w = ρ_C on every edge.

H − Z0 is balanced: a cycle of H − Z0 lies in one block of H, has a variable node not in Z0,
so that block is balanced. ρ is unique up to one flip per part, and a flip leaves every Def
set unchanged, so nothing depends on an order. [proved, asserted on every run]

**Step 3. Three sign predicates.** For a variable w, its live holders are the live rows that
contain it.
- **glob**: σ_w = s if every live holder r of w has sgn(r_w) = s; otherwise 0.
- **frame±**: σ_w = s if every live holder r lies in one part and has (edge sign)·ρ_{comp(r)} = s.
  A variable held by a row of an odd component has no frame− sign.

Def(r) = {w ∈ r : σ_w ≠ 0}. *Direction:* u_{wz} = σ_w σ_z (glob, frame+) or −σ_w σ_z (frame−)
on free atoms with σ_w σ_z ≠ 0. For a pair (a, b) in component C, a_w σ_w = |a_w| ρ_C (frame+)
or |a_w| ρ_C (−1)^{par(a)} (frame−), and par(b) = par(a) + 1. So every term of c_{(a,b)}(u),
including both terms a_w b_z and a_z b_w of a cross atom, is |·||·| ≥ 0. c > 0 iff
Def(a) × Def(b) holds an incidence whose atom is free. Theorem D applies. [proved]

*Monotonicity and unique fixpoint.* Live holders only shrink, so Def sets only grow and a
droppable pair stays droppable; the single-holder rule is monotone too. Two drop orders end at
the same set: each drop of one order is droppable at the other's final set. [proved; asserted on
every event except under the `frame_bad` mutant]

**Set identity (R3-1).** Every Def set and every set pass 1 interns is a root of a hash-consed
binary trie over dense variable ids (`tput`, `tn`, `tid`): a node is the exact tuple (height,
left id, right id), interned by that tuple, so two sets have the same id iff they are equal.
Adding a variable rebuilds the ⌈log₂ V⌉ nodes on its path. Memos are keyed by these ids; no hash
value stands for a set. The phase-1c Zobrist memo gave a wrong verdict (test `collision`).

**Step 4. Pass 1, per wanted product and predicate, without listing pairs (R3-2, R3-4).**
- Def sets are interned once per row and predicate; a side's **groups** are its distinct Def
  sets. key(S) is the member of S with the fewest partners and d(S) that number of partners.
- A group pair (S, T) survives iff S = ∅, or T = ∅, or every atom of S × T is mentioned.
- *Estimates.* With x the side with fewer groups and Σ_T |T| the other side's total size,
  est_plain = g_x + Σ_S |S|·min(d(S), Σ_T|T|); est_strip = Σ|S| + Σ|T| + Σ_{w∈U_x}
  min(d(w), |U_y|) + Σ_{z∈U_y} min(d(z), |U_x|) + g_x + g_y, U the union of a side's groups.
- **Plain walk** (when est_plain ≤ est_strip). For each S of side x: if Σ_T |T| ≤ d(S), every
  T is tested directly (Gemini's guard); otherwise the candidates are the T whose key is in
  partners(key S), cut once per (key, side list, predicate) to the other side's keys (Claude's
  key cut). A test of (S, T) stops at the first free atom; it is memoized per pair of set ids.
- **Stripping** (otherwise; Gemini). A variable w of U_x mentioned with every z of U_y is
  universal: removing it from S keeps the answer for every T. The stripped groups S ∩ H_x,
  T ∩ H_y are interned; an empty stripped group survives with every group of the other side.
  The nonempty ones are tested by the walk above, or by the **complement method** (Claude F4)
  when est_comp = |H_x||H_y| + g_y|H_y| + Σ|S| < est_walk = Σ_S |S|·min(d(S), Σ_T|T|) + Σ_T|T|:
  Free(w) = H_y minus the partners of w, Miss(z) = the groups T lacking z; S survives with T
  iff T ∩ ⋃_{w∈S} Free(w) = ∅, and only the T in Miss(z_0) are checked, z_0 the member of
  Free(S) with the shortest Miss list.
- A pair is listed iff its groups survive under all three predicates. A listed pair with every
  atom of its supports mentioned is closed (memoized per support pair): to R, to no live list.

Plain, walk and complement compute the same survivors [proved: stripping keeps each test's
answer; the complement test is the definition]; only the cost differs. Test `strip` (test 12).

**Step 5. The joint fixpoint (R2-2, R2-3, R3-5).** On the open listed pairs:
- Initialization is charged 1 per listed pair. A row dies when it has no live pair; its sign
  counts drop in O(|r|). A variable that gains a sign adds itself to the Def sets of its live
  holders (one trie insertion each), which become dirty.
- **Relevance** (`relevant`). w is irrelevant if, for every row r holding w, w*z is mentioned
  for every z of every row r can be paired with (r's component, opposite parity); it never makes
  an incidence free and is left out of the Def sets. Budget 2 d(w) + 2 lookups per w, past which
  w counts as relevant (safe: that only adds tests). Cost O(k log k).
- **Delta rechecks** (Claude, R3-5). A dirty row tests each live pair e = (a, b), memoized per
  pair of exact set ids. On a miss, e was open at its last test, so only the new incidences are
  tested: (new Def(a)) × Def(b) and (old Def(a)) × (new Def(b)), cost (l_a − p_a)·l_b +
  p_a·(l_b − p_b), p the lengths then. Def lists grow only by appending, so "old" is a prefix.
- `kept`'s count rules (K:740-1060) run on the live pairs: P3 (atom held by one row each side),
  P2, P4 without its gate W4 ≤ 4k. P0 is the closed case of step 4.
- What they leave goes to the exact single-holder peel, which lists the free atoms of each
  live pair (charged Σ|a||b|) and drops a pair holding an atom no other live pair holds.
- Any drop can wake any rule; the run ends when none drops a pair.

**Determinism of what is printed (R3-8).** R's pairs, the drops by rule and every diagnostic
list are emitted sorted: in the prototype by row index (`left.sort_unstable`, stage2.rs:1052),
in the crate by row content (sorted terms, then constant), so the order is fixed by the input.

## 4. The residual R in factored form (R2-4)

For each residual pair, let a be the row with fewer terms (ties by content: sorted terms, then
constant, never row index). For each such a, both sizes are computed exactly and the smaller
form is written: a rule on the written size, with no constant.
- **direct**: each pair row written out, Σ_b (|a||b| + aff(a,b) + 1), with
  aff(a,b) = [b_0 ≠ 0]·|a| + [a_0 ≠ 0]·|b|.
- **shared** (|a| ≥ 2): one integer variable s_{a,z} = Σ_{w∈a} a_w y_{wz} per z in N(a), the
  union of the supports of a's partners. Each pair row becomes
  a_0 b_0 + a_0 Σ b_z z + b_0 Σ a_w w + Σ_z b_z s_{a,z} ≥ 0, size
  |N(a)|·(|a|+1) + Σ_b (|b| + aff(a,b) + 1); each s equation is counted once (`sizes2`).

*Exactness.* Each s is defined by an integer equation over integer atoms; every point of the
expanded system extends uniquely, and the new system projects onto the old one. [proved]

*Built* (PRES-products-shared-output, b22-factored3, 2026-11-24): `factored::written` writes
each a in the smaller form, the s variables numbered from `first_free_aux` (above every
auxiliary variable of the premises, goal and definitions), and `linear_reading` leaves them
out of a point it reports. With one partner the shared form is larger by 2|b|, so it is
written only for a row with several partners. Tests: the verdicts of both forms agree through
`satisfiable` on closed_rL and moment_curve, with the control "s equations dropped" proving
fewer goals (`the_shared_form_gives_the_verdicts_of_the_direct_form`); the written sizes of
closed_rL at r = L = 6 and 17 are 504 and 10404 against the direct 1332 and 83810, growth
20.64 against 62.92 at 8.03 times the input (`the_written_size_of_closed_rl_scales`; both are
output, exception 2).

*Size.* E_R is at most the uncollected affine term count of the expanded rows,
Σ(|a||b| + aff + 1) ≤ W_full, and W_full ≤ 4·W_R when |a|, |b| ≥ 1 (a constant-only factor is
not a factor) [proved]. (x+1)(y+1) has E_R = 4 = W_full > 3·W_R. The control: one closed pair
(x_0+..+x_3)(y_0+..+y_3) has E_R = 17 = W_R + 1 [computed, small].

*closed_rL* (r rows of full support over L variables per side, all atoms mentioned):
E_R = rL² + rL + r²L + r²: 504 at r = L = 6 and 10404 at 17 [computed, `closed`].

*moment_curve* (a_i = x + iz + i²w, b_j = y + jt + j²u, all 9 atoms mentioned): no atom is
free, so all m² pairs are in R, E_R = 4m² + 12m. The m² inequalities are irredundant (R2-10:
Codex and Gemini at m = 6, Gemini also at m = 20, by an integer Y matrix of
2(s−i_0)² + 2(t−j_0)² − 1 that is −1 at (i_0, j_0) and ≥ 1 elsewhere) [cited]. So Θ(k²)
written rows is a bound of this encoding of R, not of the question.

## 5. Cost

### 5.1 Bounds of each step [proved]

N = k. Hash operations on exact keys are counted as expected O(1); with ordered maps in their
place (the deterministic choice), each such operation, and so each bound below, gains a log k
factor. Sorting costs its log factor in either case.

| step | work |
|---|---|
| 0 normalize, classes, dominance, cone rule | O(k log k) |
| 1 components | O(k α(k)) |
| 2 frames | O(k) |
| 3 initial counts | O(k) |
| 4 pass 1 | Π (below) |
| 5 relevance | O(k log k) |
| 5 trie insertions | O(k log k): ≤ 3 Σ\|r\| insertions, ⌈log₂ V⌉ nodes each |
| 5 worklist | O(k + \|L\| + Σ_L(\|a\|+\|b\|) + Σ_{open L} \|Def(a)\|·\|Def(b)\|) ≤ O(k + W_listed') |
| 5 P2/P3/P4 | O(k + Σ_L(\|a\|+\|b\|)) plus P4's O(W4 log k), W4 = Σ_L min(\|a\|,\|b\|) (K:152-155) |
| 5 exact peel | O(W_listed) |
| residual output | O(E_R) |

- Π (R3-8, as `stage_a2` does it): per wanted product and predicate, min(est_plain, est_strip),
  plus the key cuts, Σ over distinct (key, side list, predicate) of d(key), plus the tests, Σ
  over distinct tested (S, T) of |S|·|T| (≤ |S|·d(S) per S under Gemini's guard); the complement
  adds est_comp and |Miss(z_0)|·|Free(S)| per S.
- Walked groups: Σ_{wanted (x,y)} min(g_x, g_y) = O(N^{1.5}), g_x the groups of on[x] (pairs
  with min < √N give ≤ |wanted|·√N; at most √N lists have g ≥ √N, so the rest give ≤
  Σ_x g_x·√N) [proved, Claude R2]. That is the outer loop; Π ≤ N² at worst (exception 1).
- The worklist: each (row, predicate) is dirtied ≤ |r| times, a recheck costs deg_L(r), and
  Σ_r |r|·deg_L(r) = Σ_L(|a|+|b|). With delta rechecks each incidence of an open pair is tested
  at most once per predicate: ≤ 3·Σ_{open L} |a||b| =: 3·W_listed' [proved, Claude R3]. That sum
  is not bounded by k log k: exception 4.

### 5.2 Measured scaling (k at n and 8n) [computed, run14-*.log; work = all of steps 0-5]

"k at 8n": k at the larger size; "ratio": work at 8n over work at n; limit 10.5.

| family | k at 8n | k ratio | work ratio | note |
|---|---|---|---|---|
| star, x+iu / y_j, empty_side | 6400, 8000, 7200 | 8.00 | 8.00, 8.19, 8.88 | R2-1 |
| wl with K, without K (r = L, 6 → 17) | 1265, 1225 | 6.76, 7.25 | 6.66, 7.47 | R2-2 |
| empty_def; wl_triggered closed, hole, control | 2049; 2262 | 7.21-7.97 | 7.17-8.04 | R2-2 |
| explicit_closed (1×1, L 6 → 17) | 1513 | 7.42 | 7.62 | R2-9 |
| sum_on_factors, sum_beside, o1_chain, codex_h_chain | 32642, 26007, 7200, 5631 | 7.98-8.01 | 8.32, 8.65, 8.52, 8.65 | R2-3 |
| closed_rL, closed_hole (6 → 17); o3 unary, l1; nonparallel, nonparallel_cross | 1225, 1227 | 7.18-7.97 | 7.47, 7.46; 7.43, 7.97; 7.97, 7.96 | |
| grid, hard_tri; d64, d84, d8_circ, wheel, cascade; premise_k_atoms, gemini_s1, gemini_s1_mixed, near_cohort | | 7.34-8.02 | 7.05, 7.89; 7.97-8.02 | |
| **o2_zero_residual** (16 → 45) | 8199 | 7.70 | 7.86 (was 15.41) | R3-2 |
| **closed_wake, no_wake** (m 32 → 256) | 2065, 2069 | 7.56, 7.47 | 7.27, 7.20 (were 29.8) | R3-3; left 4, 5 |
| n0_claude, n0_gemini | 25765, 12241 | 8.26, 7.80 | 8.34, 7.85 | R3-4 |
| explicit_w2 high degree, control | 17010, 9090 | 8.08, 7.95 | 8.22, 8.23 | R3-4 |
| codex_chain, codex_chain_freeze | 3905, 3907 | 7.17, 7.14 | 8.27, 8.25 | R3-5; worklist 9.70 |
| wl_seq_chain (Gemini 3B, l 20 → 80) | 9608 | 7.95 | 10.46 | R3-5; worklist 8.10, pass 1 10.47 |
| p4_open, peel off (`no_peel`) | 2371 | 6.57 | 9.97 | R3-6; P2/P3/P4 alone 19.71 |
| **o2_distinct** (16 → 45) | 8193 | 7.74 | **10.69** | exc. 2; 7.89 without the closed check |
| **moment_curve** (20 → 160) | 1619 | 7.39 | **18.21** | exc. 2; \|L\| 400 → 25600 |
| **ov_log2sq** (n 64 → 280, d = ⌈log₂² n⌉) | 34707 | 7.74 | **19.96** | exc. 1; pass 1 20.31 |
| **sum_no_count** (count rules off) | 32642 | 8.00 | **47.03** | exc. 3; peel 63.15 |
| **wlgrow** (Claude F1, l 10 → 28) | 10081 | 7.00 | **28.32** | exc. 3; worklist 8.14, peel 47.20 |
| **p4_open** (Gemini 5B) | 2371 | 6.57 | **32.94** | exc. 3, 3b; peel 50.52 |
| **wlgrow_g** (l 10 → 28) | 10109 | 6.97 | **31.71** | exc. 4; worklist 34.00 |

nopass1 control: nonparallel, m = 128: 20492 with pass 1, 447497 with every pair listed.

### 5.3 Hard-rule exceptions

DESIGN: "nothing that can be solved within O(n log n) time should ever be refused". Each item is
a cost, not a refusal, with its bound, reason and a scaling test at that bound, at the code.
1. **Pass 1 on bicliques that are neither sparse nor co-sparse: Π of sec. 5.1, up to O(k²).**
   Narrowed by R3-2 (stripping and the complement bring o2_zero to 7.86) to products where both
   est_walk and est_comp are large. Reason: exact pass-1 emptiness is OV-hard (sec. 5.4). Test
   `ov` (OV vectors, d = ⌈log₂² n⌉, n 64 → 280, survivors equal to brute force, 67 and 295):
   pass 1 grows 20.31 at k ratio 7.74; pass-1 ratio / k ratio² = 0.34 ≤ 1.31.
2. **Closed pairs that must be written: O(k + |L| + W_R).** Narrowed by R3-3: closed_wake and
   no_wake leave it (the cone rule). It covers residuals where no row of a side is a
   nonnegative combination of two others that the cone rule sees: moment_curve, whose |L| =
   Θ(k²) closed pairs R must write, and o2_distinct, whose closed check grows with W_R (closed
   checks 4578 → 95087 as W_R goes 6975 → 172304). Reason: the output; the closed check reads
   W_R atoms of pairs that go to R. Test `out2`: work/(k + |L| + W_R) goes 1.026 → 0.306
   (ratio 0.30) on moment_curve and 2.608 → 1.245 (0.48) on o2_distinct, limit 1.31.
3. **The exact single-holder peel: O(W_listed).** It lists the free atoms of what P2/P3/P4
   leave. Reason: W_listed = W_R + W_drop, and W_drop cannot be brought under the input's
   order: unless the orthogonal vectors hypothesis fails, no algorithm finds the single-holder
   fixpoint in O(N^{2−ε} + W_R) [proved, b22-factored3 2026-11-24, PERF-factored-peel-wlisted:
   the reduction and its proof are in the module doc of `factored.rs`, "The exact peel and its
   lower bound"; tests `the_peel_decides_orthogonal_vectors` and
   `the_peel_on_orthogonal_vectors_follows_its_listed_incidences`]. On wlgrow the peel drops no
   pair, so its 47.20 is the growth of the output W_R (`the_peel_on_wlgrow_is_bounded_by_its_output`).
   Phase 1b's triangle inference stays withdrawn. Tests on the superlinear peel
   (R3-6): `nocount` (count rules off): peel 63.15, peel/W_listed 2.638 → 2.627, ratio 1.00 ≤
   1.31; `p4open`: peel 50.52; `wlgrow`: peel 47.20.
   3b. **P4 of `kept`: O(k + W4 log k), W4 = Σ_L min(|a|,|b|)** (K:152-155). Gemini's EXP 5B is
   confirmed: with `no_peel`, P2/P3/P4 grow 19.71 at k ratio 6.57. Reason: P4 keeps per-pair,
   per-variable candidate lists; a grouped form (O9) is not built, which is not a hardness
   result. Test `p4open`: work/(W4 log₂ k) 0.274 → 0.187, ratio 0.68 ≤ 1.31.
4. **The worklist: O(k log k + W_listed')** (sec. 5.1), superlinear when many open listed pairs
   have long rows whose Def sets grow late. Delta rechecks and exact ids bring Claude's wlgrow
   to 8.14, Gemini's 3B resized to an 8× step in k to 8.10 and Codex's chain to 9.70. They do
   not help wlgrow_g, wlgrow with an unsigned variable g in every Y row (no x_l universal, so
   relevance and stripping keep every incidence): worklist 34.00 at k ratio 6.97, against
   W_listed' 14400 → 705600; worklist/W_listed' 1.72 → 1.19, within the stated order.
   Reason: the open pairs that die are {(s, t) : ∃ w ∈ Def(s), z ∈ Def(t), w*z free}, the ends
   of a path query kept under insertions into Def; with Bad(t, w) = ∃z z ∈ Def(t) ∧ w*z free it
   is Q(A,C) = R(A,B), S(B,C), the standard query that is not free-connex. Kara, Nikolic,
   Olteanu, Zhang, LMCS 2023 (arXiv 1907.01988, DOI 10.46298/lmcs-19(3:11)2023) [cited]: no
   constant delay after linear preprocessing under the BDG07 conjecture
   (main_result_static.tex:392); under OMv, no fully dynamic method with O(N^{1/2−γ}) amortized
   update time and delay (lower_bound.tex:14-15). Berkholz, Keppeler, Schweikardt, PODS 2017
   (arXiv 1702.06370, DOI 10.1145/3034786.3034789) [cited], BKS2016_arxiv_upload.tex:952-955:
   "unless the \OMvcon fails, there is no dynamic algorithm that enumerates $\queryphi$ with
   arbitrary preprocessing time, and $\bigOh(n^{1-\smalleps})$ delay and update time"; this
   query is not q-hierarchical, so the bound applies. Insertions only: Abo Khamis, Kara, Olteanu, Suciu 2024 (arXiv 2312.09331,
   DOI 10.1145/3695837) [cited] state O(N^{fhw}) for full queries (prelims.tex:35) and extend it:
   "To support arbitrary conjunctive queries, our algorithms need to consider free-connex tree
   decompositions" (conclusion.tex:8). Here a bag must hold A and C, covered only by R and S, so
   the width is 2 and the bound O(N²) [inferred], no better. Test `wlgrowg` asserts the worklist
   ratio ≤ 10.5 and fails (34.00): A225, exception 4.
   *Reduction from Boolean matrix multiplication (O8) [proved; test `bmm`].* Input: n×n Boolean
   A, F. Variables w_x, y_x, z_v (x, v < n), g, r₁, r₂. One wanted product; side A holds
   s_u = Σ_{A[u][x]=1} w_x and b_x = y_x − w_x; side B holds t_v = z_v + (−1)^v g, t₊ = r₁ + g,
   t₋ = r₂ − g. Mentioned: w_x*z_v iff F[x][v] = 0, and every w_x*r_i. Steps:
   (1) w_x has holders of both signs on side A (s_u, b_x) and g on side B, in one component and
   parity, so pass 1 signs neither under glob, frame+ or frame−. (2) Every pair (b_x, t) holds
   a free atom y_x*z_v or y_x*r_i with both factors signed, so pass 1 lists
   none and b_x is dead when step 5 starts; w_x is then signed. (3) Each (s_u, t) holds a free
   w_x*g with g unsigned, so pass 1 closes none. (4) Step 5: Def(s_u) = {w_x : A[u][x] = 1},
   Def(t_v) = {z_v}, so (s_u, t_v) holds a free incidence iff ∃x A[u][x] ∧ F[x][v], that is
   (AF)[u][v] = 1, and Theorem D drops exactly those. (5) (s_u, t₊) and (s_u, t₋) share every
   free w_x*g, so neither is a single holder, Def(t_±) = {r_i} gives no free incidence, and both
   stay: g never gets a sign, even when every t_v of one sign dies. (6) No other rule drops a
   pair, so R = {(s_u, t_v) : (AF)[u][v] = 0} ∪ {(s_u, t_±)}. The test checks this equality for
   n ∈ {24, 68}, F with 0, 3, n and 4n ones, with and without g, including dead columns of AF.
   Size: k = Θ(n²) and AF is read off R in O(n²). So a worklist in O(k^c) multiplies Boolean
   matrices in O(n^{2c}): c = 1 contradicts the BDG07 conjecture that BMM is not in O(n²);
   O(k log k) beats every known BMM algorithm; a combinatorial method needs k^{1.5−o(1)} under
   the combinatorial BMM conjecture (Henzinger et al., below, introduction.tex:17), ratio 22.6
   at 8× k; fast matrix multiplication gives k^{ω/2}, ratio about 11.8 at ω ≈ 2.37 [ω from
   memory, inferred]. Family `bmm_free3_g`: worklist 13.38 at k ratio 7.00 (`bmm_free3`, without
   g, is decided by pass 1's closed check: worklist 5.41, pass 1 12.27, exception 1).
   *Where the OMv route fails.* Henzinger, Krinninger, Nanongkai, Saranurak, STOC 2015 (arXiv
   1511.06773, DOI 10.1145/2746539.2746609) [cited]: OMv is online, the algorithm "has to output
   the resulting column vector before it can proceed to the next round" (introduction.tex:5).
   The worklist gets A and F at once; offline, OMv is one matrix product, so OMv gives no bound
   here, and the method it points to is fast matrix multiplication per round of deaths, still
   above 10.5 by the count above. The reduction bounds the general worklist; it does not show
   that wlgrow_g's own family is hard, so a method for that family stays open (O8).

### 5.4 A conditional lower bound for pass 1 [proved reduction]

**Claim.** No algorithm decides whether pass 1 lists any pair in O(k^{2−ε}) time, for any
fixed ε > 0, unless the orthogonal vectors conjecture (OVC) fails.

*Reduction (Gemini's realizable form).* Take OV vectors p_1..p_n, q_1..q_n ∈ {0,1}^d. Rows
A_i = x + w_i on one factor and B_j = y + Σ_{t: q_j[t]=1} z_t on the other, one wanted
product; x·y, x·z_t and w_i·y mentioned, and w_i·z_t mentioned iff p_i[t] = 0. Every σ is +1,
S_i = {x, w_i}, T_j = {y} ∪ supp(q_j), and (A_i, B_j) survives iff p_i·q_j = 0. k = O(nd).
The family `ov_log2sq` of exception 1 is this construction.

*Which OVC.* Chen and Williams, arXiv:1811.12017, intro.tex:27 [cited, read]: "we say Π is in
truly subquadratic time if there is an ε > 0 such that for all constant c, Π is solvable in
O(n^{2−ε}) time on n vectors in c log n dimensions. Note the Orthogonal Vectors Conjecture
(OVC) is equivalent to saying OV is not in truly subquadratic time." So the claim holds for
d = c·log n over all c, or for d = ω(log n) with d = n^{o(1)} (Vassilevska Williams 2015, Conj.
4, vass15.txt:236-238 [cited, read]); one fixed c gives no bound (vass15.txt:232).

*What it bounds:* exact emptiness of the pass-1 join only. Not the public verdict (with no
base rows the zero point satisfies it) and not the worklist. A weaker stage would be sound but
leaves more pairs in R.

### 5.5 Structural fragments with proved bounds (R2-9, R3-4)

- **N0.** Every row of every wanted product has a nonempty Def set and no atom between the two
  sides' signed variables is mentioned. Every key cut is then empty and every direct test stops
  at its first lookup: Π = O(k + Σ_{distinct (key, list, predicate)} d(key)), O(k) when each
  list is in O(1) wanted products [proved]. With the key cut: 8.34 (Claude's family, 16.81
  without) and 7.85 (Gemini's) [computed, `n0`].
- **Unary.** One variable per row, at most c slope classes per side: step 0 keeps one row per
  class, ≤ c² group pairs per product, O(c²·k).
- **Explicit 1×1 products with row width ≤ w.** With Gemini's guard, S is tested directly when
  |T| ≤ d(S), at ≤ w² lookups; otherwise the key cut costs < w: O(k·w²·log k) [proved]. Gemini's
  EXP 4C (w = 2): 8.22, control 8.23 [computed, `explicitw2`], 18.61 without the guard. Without
  the width bound the fragment is false.

Every other input has the cost of sec. 5.1 with the exceptions of sec. 5.3.

## 6. The residual, the backend and the verdict (R2-5, R2-6, R3-7)

**No product-size refusal.** `products` hands base ∧ R to `satisfiable`. Integer feasibility of
R is NP-hard (3-SAT with 0 ≤ x_i ≤ 1, empty residual, Codex). The backend's refusals
(refusal.rs 25-71: Growth, Shadows, Tie, Work, Questions) stay.

**R in Omega (option b).** `pivots` (P:18951-18963), `define` (P:20215-20218) and `meetings`
(P:17835-17851) may eliminate s by substitution, rewriting R up to its direct size ≤ W_full ≤
4·W_R, no more than 9bff hands it today; no E_R cutoff. Phase 2 meters Omega's peak terms and
substitutions on closed_rL, moment_curve (both forms) and Codex's pivot family at n and 8n. A
backend that keeps definitions unexpanded is O7.

**The public reference (Codex B4).** Verdicts are exact against the *expanded reference*: 9bff's
`products` with every wanted pair written out and the product-size refusals removed
(CERTIFY_PER_INPUT's P4 gate, EXPAND_PER_INPUT's Φ, TERMS_PER_INPUT; sec. 7), deciding through
the same `linear_reading` and tiers.

**The verdict contract [proved where stated; tests in phase 2].**
- `Entailment` is Proved / Refuted / NotProved / Refused (P:28557-28568). Cheap, Local and
  Whole are `Tier`s, all deciding integer points by `linear_reading` (P:28624-28657).
- **The condition (Claude F7).** `linear_reading` returns Proved exactly when
  `satisfiable(&f)?` (P:28676) returns Ok(None). On a tier where `satisfiable` decides both the
  factored and the expanded formula, Proved in one iff Proved in the other: Theorem D and its
  corollary, step 0 (dominance under A2, the cone rule), sec. 4 exactness [proved]. Where it
  refuses one form only, the verdicts can differ: on Cheap the refusal is returned (`?`); on
  Local and Whole `.unwrap_or(first)` (P:28648) and `.unwrap_or(second)` (P:28653) turn it into
  the previous tier's verdict, hiding it. Phase 2 counts and reports these cases; the contract
  claims nothing for them.
- **Refuted** only with a point checked under real multiplication (`real.holds`, P:28708), as
  today; which of Refuted and NotProved comes out depends on the solver's point, in either form.
- **Payloads.** Refuted(shown) is filtered to `Atom::Sym` (P:28709-28713). Proved(ps) (P:28677)
  and NotProved(m) (P:28715) carry the solver's formulas and model: m is filtered to non-product,
  non-s atoms, and ps gets R's pairs in product form, not rows over s; how without expanding
  them is O11.
- **Aux numbering (Gemini N1).** s variables are `Atom::Aux` numbered from one above the largest
  Aux in the premises, goal and definitions, as `unbounded` does (P:28497-28507), so no s shares
  a number with a `bitAnd` variable, written by number after the sort at P:28703 (P:28706).
- Phase 2 runs every crate test and corpus case through both forms on all tiers; any verdict
  change blocks until explained case by case.

Options for R, scored in `$S/design-1c.md` sec. 6 and unchanged: (i) factored, the smaller of
direct and shared, no product-size refusal, 8, recommended; (ii) (i) plus LP dominance, 4;
(iii) refuse when E_R > c·k, 0 (a constant on a size, forbidden); (iv) a separation oracle, 4.

## 7. Crate sites to change in phase 2 (R2-11)

| constant or check in 9bff | sites | replaced by |
|---|---|---|
| CERTIFY_PER_INPUT = 4 (C2/C4/C5 budgets, P4 gate W4 ≤ 4k) | K:41, 152, 412, 515, 525, 600, 623, 640, 646, 946-953 | stage A' and the joint fixpoint (sec. 3) |
| EXPAND_PER_INPUT = 16, Φ (K:134-148: the questions refused when the pairs left after stage 2 expand past 16k) | K:48, 134-148, 1064-1071, 1131-1132; the rustdoc link refusal.rs:68 | no refusal; R in factored form |
| TERMS_PER_INPUT = 40 | P:29087, 29093-29099, 29127-29133 | removed with the wanted-product input |
| `Refusal::Products` | K:231, 1071, 1132; P:2566, 28637, 28645, 28654, 29098, 29132; refusal.rs:19-23, 62-70, 339-345 | not produced by `products`; variant, display and docs removed or reworded |
| tests asserting `Products` | K:1488, 1935, 1953-2077 (`entailment_refused_for_its_products_says_so` and the `refused_after` cases) | one successor test per removed assertion, deciding the question |
| payloads and Aux numbers | P:28677, 28703-28715 | sec. 6 |

Phase 2 searches every use of each symbol (a stale link or `Products` test is the control) and
closes PRES-pairs-beta-remove (β = EXPAND_PER_INPUT).

## 8. Tests [computed unless marked phase 2]

Each test has a negative control that it is shown to detect.
1. **Brute force on tiny instances.** Exact rational FM on base ∧ all expanded pairs against
   base ∧ R. tiny0, tiny1, tiny2 (random_tiny, claude_conflict, gemini_shared_conflict): 4000,
   4000, 5000 cases; same 3998, 3987, 4988; differ 0; skipped 2, 13, 12 (over 20000 FM rows in
   a step); replay failures 0; renaming differs 0. Rational oracle, factor rows in base (A2);
   control 2x = 1 returns Some(true). The integer check is phase 2.
2. **Replay.** Every drop's certificate is rechecked by expansion: 0 failures on 13,000 and on
   12 families (`replayfams`). Controls: `frame_bad` 1281, 2145, 3022 replay failures and 14,
   24, 19 verdicts changed; `drop_any_free` 14, 23, 18; D11 (equal-support dominance) 2, 0, 0.
3. **Renaming.** Pairs left, compared by gcd-normalized content (`feas_left`, R3-8; `keep_of`
   compared row ids, Gemini EXP 6B: 46, 25, 17 false differences), after permuting variables
   and rows and reversing products: 0 differ in 13,000; 26 small cases same under 20 renamings.
   Control: phase-1 stage A on (v0+v1)², (v0−v1)² leaves 0 or 2 by order, 22 over 20.
4. **Joint fixpoint.** D3 (x+y)(x−y), x*x mentioned: 0 left; control y*y too: 1. sum_on_factors
   at 960: 0. Pairs left ⊆ those of the single-holder rule alone: 0 exceptions (tiny, replayfams).
5. **Sizes.** x*y: E_R 2; (x+1)(y+1): 4 = W_full; (x_0+..+x_3)(y_0+..+y_3): 17; closed_rL: 504, 10404.
6. **A2 (R2-7), part `a2`.** Base 2x ≥ 1, x ≤ 1, u = 0, u*x = 0, failed-goal row x = 1/2; rows
   a = u, a' = u + 1, b = x − 1; step 0 drops (a', b). b in base: both forms Some(false). Control,
   b not in base, rationals: Some(false) against Some(true), detected. Phase 2: a production test
   forcing Local or Whole to derive an integer-only side, both forms on each tier.
7. **Empty sides (R2-8).** Gemini's two components with the product (∅, {r0, r4}): 0 left.
8. **D14 guards.** w*w free: 0 left; mentioned: 1. (x)(−x), x*x mentioned: 1; free: 0. P4 path
   (Codex): 1. three_rows(100): 0.
9. **Scaling (sec. 5.2).** Limit 10.5 (9 preferred) for 8× input; 42 of 49 pass; the others are
   tested at the bounds of sec. 5.3 (`ov`, `out2`, `nocount`, `p4open`, `wlgrow`, `wlgrowg`).
10. **Set identity (R3-1), part `collision`.** Codex's construction, also Gemini's EXP 3C: two
    different Def sets a, b of 65 variables with equal 64-bit Zobrist value under the phase-1c
    seed (0x79941b0cfb104fe2); a has a free atom with T = {130}, b none. Exact ids give
    has_free(a, T) = true and has_free(b, T) = false in both orders, and the integrated
    instance replays with the expanded verdict Some(false). All three checks fail on the
    phase-1c prototype (one order drops falsely, the other keeps falsely) [computed].
11. **Cone rule (R3-3), part `cone`.** 4000 cases of each tiny generator and of `cone_plane`
    (rows on shared coordinate planes): fired 1088 times on `cone_plane`, 0 verdict changes, 0
    replay failures; control `cone_bad` (wrong extreme) changes 7. closed_wake, m = 32 and 256:
    4 left, E_R = 20 (1024 and 65536 without the rule); no_wake: 5 left, E_R = 23.
    Part `cone1` (the claim of sec. 11 most likely wrong): a second product shares side A's rows
    with another side B (shape 0), drops one cone row of side A (shape 1), or puts side A on the
    other factor (shape 2), so a list loses rows for one product only. Fired 1068, 805 (all on
    the reduced list) and 1017 times; 0 verdict changes and 0 replay failures; `cone_bad` changes
    1, 2 and 2 [computed, run15-cone1.log]. A crate test of the same shapes is due in phase 2.
14. **BMM reduction (O8), part `bmm`.** R equals the zeros of AF (plus the t_± pairs) in all 16
    cases of sec. 5.3; `bmm_free3_g` worklist 13.38 [computed, run15-bmm.log].
12. **Stripping and the method choice (R3-2), part `strip`.** Plain, automatic, walk-only and
    complement-only agree on 3 × 3000 tiny cases and on o2_zero, o2_distinct, ov, n0,
    n0_gemini, explicit_w2 and wlgrow; control `strip_bad` (its own side's universe) changes
    318, 153 and 272 cases.
13. **Phase 2 (the crate):** both forms on every crate test and corpus case, all tiers, refusals
    of one form counted; Omega metering (sec. 6); the `kept` subset; an integer oracle; the A2
    production test; d84_bip_tri, hard_tri and near_cohort, refused today, must be decided.

## 9. Open items

- **O1.** Pass 1 on bicliques neither sparse nor co-sparse (exception 1). OV hardness covers
  exact emptiness only, so it explains these families but does not bound Π from above.
- **O3.** Whether a weaker near-linear stage followed by a larger R is better in total is open.
- **O7.** A backend that keeps s definitions unexpanded (R2-5, for the author).
- **O8.** Exception 4. The reduction from BMM is written and tested (sec. 5.3); the OMv route
  fails because the worklist is offline. Open: a method within O(n log n) for wlgrow_g's family,
  which the reduction does not cover; for the general worklist none exists unless BMM is in
  O(n² log n).
- **O9.** A grouped form of P4 (exception 3b), over Def groups as in step 4.
- **O10.** Gemini's folded form of moment_curve, measured through Omega in phase 2.
- **O11.** How Proved(ps) carries R's pairs without s and without expanding them (sec. 6).
- Closed: O6 (exact ids, R3-1); O2 replaced by R2-5; O4 and O5 (R2-7, R2-10).

## 10. Not adopted

Codex's closed_rL zero witness (R1 Q5, for phase 2); Gemini's folded moment_curve (O10, sec. 3).

## 11. Changes for META3 (phase 1d)

Lines are of this file; the R2 map is in `$S/design-1c.md` sec. 11.

| decision | what changed | lines | met |
|---|---|---|---|
| R3-1 | hash-consed trie (exact (height, left, right) nodes) for every set id; Zobrist memo removed; test `collision` (Codex, Gemini 3C), red on phase 1c; O6 closed | 28, 162-166, 475-480, 504 | met |
| R3-2 | estimates, stripping, walk or complement per biclique; exception 1 narrowed, test `ov` at d = ⌈log₂² n⌉; test `strip`; o2_zero 7.86 | 168-191, 266-272, 291, 312-316, 485-488 | met |
| R3-3 | 2-D cone rule in step 0 with its proof; closed_wake, no_wake are tests; exception 2 narrowed (test `out2`); folded moment_curve left to phase 2 | 95-99, 106-125, 292, 317-323, 481-484, 502 | met |
| R3-4 | key cut per (key, side list, predicate); Gemini guard; N0 bound restated (O(k) only when each list is in O(1) products), 8.34; explicit w = 2 holds, 8.22 | 175-178, 293-294, 374-386 | met |
| R3-5 | delta rechecks and exact ids; wlgrow 8.14, 3B at 8x 8.10, chain 9.70 (worklist); exception 4 with cited reason, failing test `wlgrowg` 34.00; O8 | 193-204, 273-276, 295-296, 304, 333-350, 499-500 | partly: no method within O(n log n) |
| R3-6 | P4 listed as exception 3b (test `p4open`, 0.68); exception 3 tests the superlinear peel (`nocount` 63.15, ratio 1.00); O9 | 262, 297, 303, 324-332, 501 | met by listing, P4 not fixed |
| R3-7 | public reference; contract on the condition that `satisfiable` decides both forms; hidden refusals named; payloads, Aux numbering; O11 | 390-428, 443, 503 | met in text; tests in phase 2 |
| R3-8 | first-use definitions; rational t; Π and step-4 text match the code; sorted output; `feas_left` by content; Aux | 18-21, 73, 172-178, 211-213, 266-269, 459-462, 424-426 | met |

**Not met, and why:**
- **Exception 4 has no method within O(n log n)** (wlgrow_g 34.00); BMM reduces to the
  worklist (sec. 5.3, O8). Seven families are above 10.5, each under sec. 5.3.
- **A correction.** I first wrote that P4 was not superlinear, from a run with `no_single`, which
  switches P4 off with the peel. With `no_peel`, P2/P3/P4 grow 19.71: Gemini was right (exc. 3b).
- wl_seq_chain 10.46 and p4_open with the peel off 9.97 pass, above the preferred 9.
- Ties in sec. 4 use row content, which includes variable ids: the written form, not the pairs
  left, may change with variable names.

**Claim most likely to be wrong:** the cone rule's claim that it never changes a verdict
outside the tiny and wake families. The proof of sec. 3 needs a, e_1, e_2 to be paired with the
same rows b; that holds because the rule runs per side list and a wanted product pairs a whole
list, but a crate path that drops rows of one list for one product only would break it.
