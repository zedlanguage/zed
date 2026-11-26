//! The linear solvers of the compiler `zedc`'s constraint store (DESIGN.md sec:constraints):
//! linear terms over the rationals, the two-variable and three-variable deciders, the
//! negative-cycle search and the unit two-variable-per-inequality closure. `zedc` re-exports each
//! module at its old path (`zedc::store::linear`, ...).
//!
//! # References
//!
//! The papers named in short form in `live3` and `negsssp`; `utvpi`, `twovar` and `negsssp`
//! give their other papers in their own module docs. "Crossref" means that a lookup on
//! api.crossref.org on 2026-11-20 gave the authors, title, venue, volume and pages written here;
//! "read" names the copy read on 2026-11-21 (verification only, kept outside the repository)
//! and the parts the code uses.
//!
//! - H. W. Lenstra Jr., "Integer programming with a fixed number of variables", Mathematics of
//!   Operations Research 8(4), 1983, pp. 538-548, doi:10.1287/moor.8.4.538. Read 2026-11-21
//!   (scanned PDF from LibGen, read page by page). Sec. 1, pp. 539-541: with `τK` between the
//!   balls `B(p, r)` and `B(p, R)`, `R/r < c_1` (3), (4), and a reduced basis of `L = τZ^n`,
//!   the walk of the lemma (8) gives a lattice point `y` with `|p - y| <= 1/2 √n |b_n|` (10);
//!   if `y` is not in `τK` then `r < 1/2 √n |b_n|`, and the planes `H + k·b_n` that meet
//!   `B(p, R)` number `t` with `t - 1 < c_1 c_2 √n`, each a problem in `n - 1` variables.
//!   Sec. 2, pp. 541-543: the balls come from a simplex of vertices of `K`, each vertex
//!   replaced while some vertex of `K` is more than `3/2` times as far along a face normal;
//!   then `R/r < 2n^(3/2)`. `live3` follows this in dimension three (its steps 2-4) with six
//!   linear programs in place of the replacement loop and the ratio 25 its own docs derive,
//!   and its `reduce` states the nearest-point bound with `|b_i*|` (see there).
//! - A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, "Factoring polynomials with rational
//!   coefficients", Mathematische Annalen 261(4), 1982, pp. 515-534, doi:10.1007/bf01457454.
//!   Read 2026-11-21 (PDF, OpenAlex's cached copy; pp. 516-518 checked on the page images,
//!   since the text layer garbles the formulas). A basis is
//!   reduced when `|mu_ij| <= 1/2` (1.4) and `|b_i* + mu_i,i-1 b_i-1*|^2 >= 3/4 |b_i-1*|^2`
//!   (1.5); "The constant 3/4 in (1.5) is arbitrarily chosen" (p. 517). Proposition (1.11),
//!   p. 518: `|b_1|^2 <= 2^(n-1) |x|^2` for every nonzero `x` in the lattice, so the first
//!   vector is within `2^((n-1)/2)` of the shortest. `live3::reduce`, step 3.
//! - N. Megiddo, "Linear programming in linear time when the dimension is fixed", J. ACM 31(1),
//!   1984, pp. 114-127, doi:10.1145/2422.322418. Read 2026-11-21 (PDF, OpenAlex's cached
//!   copy). Sec. 2,
//!   p. 116: "there is a way to drop a fixed fraction of the set of constraints regardless of
//!   the size of that set"; sec. 3.2, pp. 118-121, the search: pair hyperplanes by slope, test
//!   medians, and settle `B(d)` of them with `A(d)` queries, `A(d) = 2A(d - 1)`, `B(d) =
//!   1/2 B(d - 1)^2`, the other work `cn + c(1 - B)n + ... <= (c/B)n`; sec. 4 the oracle, one
//!   query by up to three linear programs in one dimension less. `live3` step 1 (`least`,
//!   `search`). An earlier note here cited "sec. 4" for the whole method; the search is
//!   sec. 3.2. Tests of `live3` against enumeration: `random_bounded_systems_match_enumeration`
//!   and the others in tests/steps/l01_38_omega_test/live3.rs; they check answers, not the
//!   linear bound.
//! - A. V. Goldberg, "Scaling algorithms for the shortest paths problem", SIAM J. Comput.
//!   24(3), 1995, pp. 494-504, doi:10.1137/s0097539792231179. Read 2026-11-21 (PDF from
//!   LibGen). Sec. 3, pp. 495-496: bit scaling doubles lengths and prices each
//!   iteration so the price function is 1-feasible, REFINE restores feasibility or finds a
//!   negative cycle, and Lemma 3.2: "O(log N) iterations". `negsssp`
//!   uses it as Duong's paper states it (v2 source, Lemma "Scaling", read 2026-11-20): "For
//!   integral weights at least -W, it suffices to implement a scaling step that returns either
//!   a negative-weight cycle or a potential with reduced weights at least -W/2. There are
//!   O(log(nW)) steps, followed by a nonnegative SSSP computation".
//! - M. Thorup, "Integer priority queues with decrease key in constant time and the single
//!   source shortest paths problem", STOC 2003, pp. 149-158, doi:10.1145/780542.780566
//!   (J. Computer and System Sciences 69(3), 2004, pp. 330-353, doi:10.1016/j.jcss.2004.04.003):
//!   the queue Duong's paper cites for the cost of a Dijkstra search. Both read 2026-11-21
//!   (PDFs from LibGen). Corollary 2 (JCSS, p. 331): single-source shortest paths with weights
//!   in `[0, C)` "in linear space and O(m + n log log min{n, C}) time", by the queue of
//!   Theorem 1 (insert and decrease key in constant time, delete in `O(log log n)`) inside
//!   Dijkstra's search. `negsssp` departs from it: a binary heap, `O(log n)` per delete in
//!   place of `O(log log n)`.
//! - Y. Dinitz and R. Itzhak, "Hybrid Bellman-Ford-Dijkstra algorithm", J. Discrete Algorithms
//!   42, 2017, pp. 35-44, doi:10.1016/j.jda.2017.01.001. Read 2026-11-21 (PDF, OpenAlex's
//!   cached copy). The algorithm (BFD) repeats a Dijkstra search "without re-initializing the
//!   tentative value d(v)" (abstract), with a Bellman-Ford pass over the negative edges in the
//!   BFD-r form of sec. 5; Proposition 3.3, p. 39: with `neg(v)` the least number of negative
//!   edges on a shortest path to `v`, `d(v)` is exact after round `neg(v) + 1`, by induction
//!   over the last negative edge of the path and Lemma 3.2; Theorem 3.4: BFD stops "in at
//!   most neg(G) + 2 rounds", the last round being the one that changes nothing. So `k + 1`
//!   rounds give the distances when shortest paths hold at most `k` negative edges, and one
//!   more shows that they are final (BF-Dijkstra in `negsssp` and `utvpi`). Duong's Lemma
//!   "BF-Dijkstra" states the bound used: `O(η(m_F + n_F log log n))` time for exact distances
//!   or a walk shorter than every walk with at most `η` negative edges. Duong cites the hybrid
//!   also to K. Bringmann, A. Cassis and N. Fischer, "Negative-weight single-source shortest
//!   paths in near-linear time: now faster!", FOCS 2023, pp. 515-538,
//!   doi:10.1109/focs57990.2023.00038, arXiv 2304.05279; read 2026-11-21 (arXiv LaTeX
//!   source): Lemma "Dijkstra with Negative Weights" (sec. 3.2, proved in appendix A, "Lazy
//!   Dijkstra"), a shortest-path tree "in time O(sum_v (deg(v) + log log n) · η_G(v))",
//!   with `η_G(v)` the least number of negative edges on a shortest path to `v`, and "If G
//!   contains a negative cycle, the algorithm does not terminate."
//! - E. W. Dijkstra, "A note on two problems in connexion with graphs", Numerische Mathematik
//!   1(1), 1959, pp. 269-271, doi:10.1007/bf01386390. R. Bellman, "On a routing problem",
//!   Quarterly of Applied Mathematics 16(1), 1958, pp. 87-90, doi:10.1090/qam/102435; L. R.
//!   Ford Jr., "Network flow theory", RAND paper P-923, 1956, and E. F. Moore, "The shortest
//!   path through a maze", Proc. Int. Symp. on the Theory of Switching, Part II, 1959,
//!   pp. 285-292 (both without a DOI). Dijkstra, Bellman and Ford read 2026-11-21; Moore not
//!   found. What each paper says, the copies and the rungs tried for Moore are in
//!   `zed_graph::heap` (Dijkstra) and `zed_graph::worklist` (Bellman, Ford, Moore). In short:
//!   Bellman's sec. 5 iterates over all nodes and needs "at most (N - 1) iterations", for
//!   positive lengths; Ford's sec. 7 relaxes any violated pair until none is left, with no
//!   bound on the steps. The test here, a further change after `n - 1` passes showing a
//!   negative cycle, follows from Bellman's bound (a path of `n` or more edges repeats a node)
//!   and is not stated in either paper. The tests use Bellman-Ford-Moore as the reference
//!   (`bellman_ford_moore` below).

pub mod linear;
pub mod live3;
pub mod negsssp;
pub mod twovar;
pub mod utvpi;

/// The reference search the negative-cycle searches are tested against, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/bellman_ford_moore.rs"]
#[expect(
    dead_code,
    reason = "the solvers' tests use every shared oracle but `negative_cycle`"
)]
mod bellman_ford_moore;

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
use zed_testkit::seed;
