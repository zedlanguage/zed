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
//! "not read" means that only that was checked, and the sketch is from memory of the paper.
//!
//! - H. W. Lenstra Jr., "Integer programming with a fixed number of variables", Mathematics of
//!   Operations Research 8(4), 1983, pp. 538-548, doi:10.1287/moor.8.4.538: round the
//!   polytope so that it lies between two concentric balls of bounded ratio, reduce the
//!   lattice basis; then either the nearest lattice point to the center lies in it or it meets
//!   few hyperplanes `u·x = t`, and each is a problem in one dimension less. `live3` follows
//!   this in dimension three with a simplex in place of the balls (its steps 2-4). Crossref;
//!   not read.
//! - A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, "Factoring polynomials with rational
//!   coefficients", Mathematische Annalen 261(4), 1982, pp. 515-534, doi:10.1007/bf01457454:
//!   the LLL reduction of a lattice basis (size reduction and the swap condition with
//!   `δ = 3/4`), whose first vector is within `2^((n-1)/2)` of the shortest. `live3` step 3.
//!   Crossref; not read.
//! - N. Megiddo, "Linear programming in linear time when the dimension is fixed", J. ACM 31(1),
//!   1984, pp. 114-127, doi:10.1145/2422.322418: prune and search; pair the constraints, find
//!   the median of their intersection points, decide on which side of it the optimum lies, and
//!   drop a fixed fraction of the constraints each round, O(m) in all for fixed dimension.
//!   `live3` step 1. Crossref; not read, so "sec. 4" at the use is from memory, not checked.
//!   Tests of `live3` against enumeration: `random_bounded_systems_match_enumeration` and the
//!   others in tests/steps/l01_38_omega_test/live3.rs.
//! - A. V. Goldberg, "Scaling algorithms for the shortest paths problem", SIAM J. Comput.
//!   24(3), 1995, pp. 494-504, doi:10.1137/s0097539792231179. Crossref; not read. `negsssp`
//!   uses it as Duong's paper states it (v2 source, Lemma "Scaling", read 2026-11-20): "For
//!   integral weights at least -W, it suffices to implement a scaling step that returns either
//!   a negative-weight cycle or a potential with reduced weights at least -W/2. There are
//!   O(log(nW)) steps, followed by a nonnegative SSSP computation".
//! - M. Thorup, "Integer priority queues with decrease key in constant time and the single
//!   source shortest paths problem", STOC 2003, pp. 149-158, doi:10.1145/780542.780566
//!   (J. Computer and System Sciences 69(3), 2004, pp. 330-353, doi:10.1016/j.jcss.2004.04.003):
//!   the queue Duong's paper cites for the cost of a Dijkstra search. Crossref, and Duong's
//!   bibliography (`[Tho03]`); not read. `negsssp` departs from it: a binary heap, one log
//!   factor more.
//! - Y. Dinitz and R. Itzhak, "Hybrid Bellman-Ford-Dijkstra algorithm", J. Discrete Algorithms
//!   42, 2017, pp. 35-44, doi:10.1016/j.jda.2017.01.001: alternate a Dijkstra search with a
//!   Bellman-Ford pass over the negative edges, so `k + 1` rounds suffice when shortest paths
//!   hold at most `k` negative edges (BF-Dijkstra in `negsssp` and `utvpi`). Crossref, and
//!   Duong's bibliography (`[DI17]`); not read. Duong's Lemma "BF-Dijkstra" states the bound
//!   used: `O(η(m_F + n_F log log n))` time for exact distances or a walk shorter than every
//!   walk with at most `η` negative edges. Duong cites the hybrid also to K. Bringmann,
//!   A. Cassis and N. Fischer, "Negative-weight single-source shortest paths in near-linear
//!   time: now faster!", FOCS 2023, pp. 515-538, doi:10.1109/focs57990.2023.00038, arXiv
//!   2304.05279 (Crossref and the arXiv listing; not read for this note).
//! - E. W. Dijkstra, "A note on two problems in connexion with graphs", Numerische Mathematik
//!   1(1), 1959, pp. 269-271, doi:10.1007/bf01386390. R. Bellman, "On a routing problem",
//!   Quarterly of Applied Mathematics 16(1), 1958, pp. 87-90, doi:10.1090/qam/102435; L. R.
//!   Ford Jr., "Network flow theory", RAND paper P-923, 1956, and E. F. Moore, "The shortest
//!   path through a maze", 1959 (both without a DOI; from memory, not checked): relax every
//!   edge `n - 1` times; a further change shows a negative cycle. The tests use Bellman-Ford-
//!   Moore as the reference (`bellman_ford_moore` below). Crossref for Dijkstra and Bellman;
//!   not read.

pub mod linear;
pub mod live3;
pub mod negsssp;
pub mod twovar;
pub mod utvpi;

/// The reference search the negative-cycle searches are tested against, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/bellman_ford_moore.rs"]
mod bellman_ford_moore;

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;
