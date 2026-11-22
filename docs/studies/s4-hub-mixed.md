# A threshold-implication hub of three or more values with both signs (S4-hub-mixed)

Plan row S4-hub-mixed, 2026-11-22, by b22-research3 (helper h9). Sources: DESIGN at zed
3fc4f56 (step L1.39, item (2) of the reduced-product paragraph), zed-impl at 590e5fd95
(`crates/zedc-preimage/src/threshold.rs`, `product.rs`, `loops.rs`), and the papers in
section 5.

## 1. The question

A threshold-implication component has parts `x + k*w <= a || y - m*w >= b` and base atoms of
the same two shapes, all sharing one name `w`, the hub. With the hub fixed at `c` the
component is a Horn system on lower bounds ("if `x >= a - k*c + 1` then `y >= b + m*c`"), and
its least and greatest members are found by two propagations in O(N log N). With every `k`, `m`
of one sign the hub's values that pass are an interval found by binary search, O(N log N log W)
in all. With both signs and a hub of two values the two answers are joined. The open case was
both signs and three or more hub values: the row asked for an O(N log N log W) method, or a
family showing that the number of distinct answers grows too fast, with a hardness proof.

Result: no such method is known, and one would multiply Boolean matrices in near-quadratic
time (section 2). The number of hub values where the answer changes is polynomial, at most
O(N²), and reaches Θ(N²) (section 3), so an exact method exists in polynomial time but not in the
row's bound. The component stays refused as a whole (`threshold::Answer::MixedHub`); DESIGN
and the code comment at `threshold::mixed` now give the reason.

## 2. Reduction from the Boolean matrix product

Take k×k Boolean matrices A and B. Build:

- the hub `w` in `1..=k`; a name `t` in `1..=1`; names `u_i`, `v_j`, `x_ij` in `0..=1`;
- for each `(i, l)` with `A[i][l]` false, a name `y` in `0..=k` and the parts
  `t + w <= l || y + w >= l + 1` and `y <= 0 || u_i >= 1`;
- for each `(l, j)` with `B[l][j]` false, the same two parts with `v_j`;
- for each `(i, j)`, the parts `u_i <= 0 || x_ij >= 1` and `v_j <= 0 || x_ij >= 1`.

Claim: the exact least value of `x_ij` is 1 exactly when entry `(i, j)` of AB is false.

Proof.

1. Fix the hub at `c`. The upper arm `t + w <= l` fails exactly when `1 + c > l`, that is
   `c >= l`; the part then forces `y >= l + 1 - c`. At `c < l` nothing forces `y` above 0.
2. The part `y <= 0 || u_i >= 1` fires when `y >= 1`. So at the least member, `y >= 1` exactly
   when `c >= l` and `l + 1 - c >= 1`, that is `c = l`, and `u_i` is 1 exactly when some edge to
   `u_i` has `l = c`: when `A[i][c]` is false. Likewise `v_j` is 1 exactly when `B[c][j]` is
   false.
3. So the least value of `x_ij` at `c` is 1 exactly when `A[i][c]` or `B[c][j]` is false.
4. Every hub value passes. There are no upper bounds other than the names' own ranges, and the
   least member stays within them, because the largest value forced on `y` is `l + 1 - c <= k`.
5. The points that pass are the union over the hub values of the points that pass at each value.
   So the exact least value of `x_ij` is the least over `c` of its least value at `c`. That is 1
   exactly when (3) holds at every `c`, that is, when no `c` has both `A[i][c]` and `B[c][j]`
   true, that is, when entry `(i, j)` of AB is false.

Size: at most 2k² edges of two parts each plus 2k² parts, so N ≤ 6k² parts; 3k² + 2k + 1
names; hub width W = k; every coefficient is -1, 0 or 1. Only the first part of an edge has the
hub on both arms, with the two signs 1 and -1.

Consequence: a solve in O(N log N log W) would compute AB in O(k² log³ k), so the exponent ω of
matrix multiplication (over the Booleans) would be 2. The best bound known is ω < 2.371339
(Alman et al. 2024, quoted in section 5), and no combinatorial method in k^(3-ε) is known
(Abboud and Vassilevska Williams 2014, Conjecture 5). The bound is conditional: it shows that no
such solve is known, not that none exists. It has the same form as DESIGN's existing argument
against parts with two lower bounds. More generally, a solve in O(N^(ω₀/2 - ε)) for any ε > 0,
with ω₀ = 2.371339, would improve the best known bound on ω.

Other reductions considered and not used: triangle detection, orthogonal vectors and hitting
set. Each needs "for some `c`, some path" or a negation. The component only answers "for every
passing `c`, forced", which is the min over `c` of a monotone reachability. The Boolean product
has exactly that form.

## 3. How often the answer changes

Upper bound (proof sketch; not checked beyond the families below). With the hub at `c`, every
value the propagation compares is an affine function of `c` or a constant: a forced value
`b + m*c`, a threshold `a - k*c + 1`, an upper bound `a - k*c`, or an end of a name's pieces
(`ceil`/`floor` return either their argument or a piece end). The parts that fire depend only
on the outcomes of these pairwise comparisons, because the least member is the least fixed
point of a Horn system decided by them. The same holds for the backward propagation and for the
emptiness test. Two affine functions change their order at most once. So between two consecutive
crossings the set of fired parts is fixed. The answer, a maximum of the fired lines at each name,
changes only at crossings: O(N²) hub values for names of one interval, and O(N² + N·P) with P
pieces. This differs from parametric shortest paths, where the answer changes n^Ω(log n) times
(Carstensen 1983). There, a path's length is a sum along the path; here a forced value is a
maximum of single lines and does not add up along a path.

Lower bound, measured. Family `steep_lines(n, m)` (tests file, section 4): the hub runs over
`0..=n*m - 1`; block `i` forces `y >= w - i*m` exactly while `w` is in `[i*m, (i+1)*m)`, through
a name `p_i` and two parts of both signs; and `x_j` (j = 1..m-1) is forced to 1 when `y >= j`.
The least value of `x_j` at `c` is 1 exactly when `c mod m >= j`. It changes 2n - 1 times, so
there are (m - 1)(2n - 1) changes in all, with N = 2n + m - 1 parts. At n = m: about N²/4.5.
Measured counts at n = m = 4, 8, 16: 21, 105, 465, equal to the formula. So a method that walks
the hub values where the answer changes, and updates the names that change, does Θ(N²) updates
on this family. A full exact method by that walk is O(N²) solves of O(N log N), that is
O(N³ log N): strongly polynomial, but outside the O(N log N log W) bound the standing rules ask
for. It is not built.

## 4. Checks

Tests in `tests/steps/l01_39_scope_relations/xst/threshold.rs` (group `l01_39_scope_relations`):

- `the_least_values_under_a_mixed_hub_are_a_boolean_product`: 300 random pairs a run, k from 1 to
  6, entries true with probability 2/3. It compares the join over the hub values (each value
  solved by `threshold::solve` with the hub fixed) with the Boolean product. At k = 2, where
  `solve` answers directly, it compares with `solve` and with enumeration when there are at most
  4 edges (47 components on the first run). A fixed k = 2 pair is enumerated on every run. For
  k ≥ 3 with an edge it checks that `solve` answers `MixedHub`.
- `the_answer_at_each_hub_value_changes_quadratically_often`: the family of section 3 at
  n = m = 4, 8, 16. It checks each value's least values against `c mod m >= j` and the total
  count against (m - 1)(2n - 1).

Negative controls, run once and not committed:

- First part of an edge written with one sign (`t + w <= l || y - w >= 1 - l`): the product test
  failed on all 20 seeds tried (`ZED_TEST_SEED` 1 to 20). 19 failed at an entry of the product,
  1 at the `MixedHub` check.
- In `steep_lines`, the block's end removed (`lower(p, 0, 1)`): the family test failed at the
  `MixedHub` check, because the component then has one sign.
- In `steep_lines`, blocks that overlap (`lower(p, -1, (i + 2) * mi)`, both signs kept): the
  family test failed at n = m = 4, hub value 4, least values `[1, 1, 1]` against `[0, 0, 0]`.

No benchmark: no code path changed cost (comments, DESIGN and tests only).

## 5. Literature

Searches (allpapers, paperclip, `-n 250`, outputs read in full):

| Mode | Query | Papers |
|---|---|---|
| keyword | parametric shortest path breakpoints lower bound | 235 |
| keyword | parametric linear programming number of breakpoints Murty | 235 |
| keyword | two variables per inequality parametric | 238 |
| semantic | directed reachability with edges present on an interval of one integer parameter; for every vertex, reachable for all parameter values | 239 |
| semantic | Horn implications between integer bounds with thresholds linear in one shared parameter; exact bounds over all parameter values; conditional lower bound from Boolean matrix multiplication | 218 |
| keyword | offline dynamic reachability lower bound Boolean matrix multiplication | 240 |

No paper solves this exact problem. The ones used:

- E. Fischer, O. Lachish, R. Yuster, "Two-phase algorithms for the parametric shortest path
  problem", 2010, arXiv:1001.3749, doi:10.48550/arXiv.1001.3749, checked 2026-11-22, line 41:
  "Carstensen [3] has shown that there are constructions for which the number of shortest path
  changes ... is n^{\Omega(\log n)} ... Carstensen also proved that this is tight". It also
  cites Murty (Math. Programming 19, 1980) for exponentially many changes in parametric linear
  programming. Used for the contrast in section 3.
- A. Abboud, V. Vassilevska Williams, "Popular conjectures imply strong lower bounds for dynamic
  problems", 2014, arXiv:1402.0054, doi:10.48550/arXiv.1402.0054, checked 2026-11-22, line 20,
  Conjecture 5: "any combinatorial algorithm requires n^{3-o(1)} time in expectation to compute
  the Boolean product of two n × n matrices".
- J. Alman, R. Duan, V. Vassilevska Williams, Y. Xu, Z. Xu, R. Zhou, "More Asymmetry Yields
  Faster Matrix Multiplication", 2024, arXiv:2404.16349, doi:10.48550/arXiv.2404.16349, checked
  2026-11-22, line 5: "ω < 2.371339".
- L. Bordeaux, G. Katsirelos, N. Narodytska, M. Y. Vardi, "The Complexity of Integer Bound
  Propagation", JAIR 40, 2011, doi:10.1613/jair.3248. Background only: bound propagation over
  two variables per inequality, with pseudo-polynomial and hardness results. It does not cover a
  shared parameter.
- G. Aubian et al., "Complexity Gaps between Point and Interval Temporal Graphs for some
  Reachability Problems", 2025, arXiv:2501.11380. Fetched, not read in full. Its title matches
  the edges present at one hub value (point labels) of section 2; not relied on.

## 6. Decisions and what is left

- Refused as a whole, as before; only the reason changed. `threshold::mixed` still stops at a
  third hub value. Each component's answer then comes from projecting its parts one at a time,
  which `product::Scope::project_threshold` documents as exact where it records no refusal.
- DESIGN mismatch, named and not changed in code. Until now DESIGN said that this shape "is
  tried as K3 and rejected when K3 refuses it". The code does something else.
  `loops::check` (`loops.rs`, the `fail` predicate) keeps any component that
  `threshold::shape` reads in the class of S4, whatever the hub's values and signs. So K3 never
  refuses this shape, and its parts are projected one at a time. DESIGN now states what the code
  does. If the author wants the K3 message instead, `loops::check` would test the hub's box (in
  `loops::Test::boxes`) and the signs before admitting the shape. That change rejects programs
  that are accepted today, so it is the author's call.
- Not built: the exact O(N³ log N) walk of section 3, and the O(W · N log N) join over every hub
  value. Each is polynomial and would replace the per-part projection (exact or refused) with an
  exact answer, at a cost above the standing O(N log N) target. Building either is a design
  decision for the author.
