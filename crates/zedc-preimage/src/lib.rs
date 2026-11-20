//! The backward transfer of the compiler `zedc`'s store (DESIGN.md sec:domains): the preimage of a
//! test's condition, the reference transfer it is compared with, and the reduced product of the
//! domains. `zedc` re-exports each module at its old path (`zedc::store::preimage`, ...).
//!
//! # References
//!
//! The published work this crate's code takes an algorithm, a bound or a complexity claim
//! from. A comment at each use names the paper and sketches the part used there; the full
//! citation and how it was checked are here. "Crossref" means that a lookup on api.crossref.org
//! on 2026-11-20 gave the authors, title, venue, volume and pages written here; "not read"
//! means that only that metadata was checked, and the sketch at the use was written from
//! memory of the paper. Papers that `zedc_presburger` also uses (Pugh's Omega test, Seidel and
//! Aragon's treaps, Tarjan's set union, Blelloch, Ferizovic and Sun, Driscoll et al., Sarnak
//! and Tarjan, Freuder, Shostak) are described, with the parts used and how they were checked,
//! in that crate's References; the entries below give their citations only.
//!
//! ## Shared with `zedc_presburger`
//!
//! - W. Pugh, "The Omega test: a fast and practical integer programming algorithm for
//!   dependence analysis", Supercomputing '91, 1991, pp. 4-13, doi:10.1145/125826.125848, and
//!   its journal version, "A practical algorithm for exact array dependence analysis", CACM
//!   35(8), 1992, pp. 102-114, doi:10.1145/135226.135233. Used here: normalizing (sec. 2.1),
//!   a row made redundant by one other dropped (sec. 2.3, found by hashing in sec. 2.4; checked
//!   in the authors' expanded text on 2026-11-20), and the dark shadow
//!   `b·α - a·β >= (a - 1)·(b - 1)` (sec. 2.3.2).
//! - R. Seidel and C. R. Aragon, "Randomized search trees", Algorithmica 16(4-5), 1996,
//!   pp. 464-497, doi:10.1007/bf01940876: Theorem 3.3 and sec. 6, 5-wise independent
//!   priorities give O(log n) expected depth.
//! - R. E. Tarjan, "Efficiency of a good but not linear set union algorithm", J. ACM 22(2),
//!   1975, pp. 215-225, doi:10.1145/321879.321884; R. E. Tarjan and J. van Leeuwen, "Worst-case
//!   analysis of set union algorithms", J. ACM 31(2), 1984, pp. 245-281, doi:10.1145/62.2160;
//!   R. E. Tarjan, "Depth-first search and linear graph algorithms", SIAM J. Comput. 1(2), 1972,
//!   pp. 146-160, doi:10.1137/0201010.
//! - G. E. Blelloch, D. Ferizovic and Y. Sun, "Just join for parallel ordered sets", SPAA 2016,
//!   pp. 253-264, doi:10.1145/2935764.2935768.
//! - J. R. Driscoll, N. Sarnak, D. D. Sleator and R. E. Tarjan, "Making data structures
//!   persistent", JCSS 38(1), 1989, pp. 86-124, doi:10.1016/0022-0000(89)90034-2; N. Sarnak and
//!   R. E. Tarjan, "Planar point location using persistent search trees", CACM 29(7), 1986,
//!   pp. 669-679, doi:10.1145/6138.6151.
//! - E. C. Freuder, "A sufficient condition for backtrack-free search", J. ACM 29(1), 1982,
//!   pp. 24-32, doi:10.1145/322290.322292; R. Shostak, "Deciding linear inequalities by
//!   computing loop residues", J. ACM 28(4), 1981, pp. 769-779, doi:10.1145/322276.322288;
//!   R. Bellman, "On a routing problem", Quarterly of Applied Mathematics 16(1), 1958,
//!   pp. 87-90, doi:10.1090/qam/102435: shortest paths by relaxing every edge `n - 1` times, a
//!   further relaxation showing a negative cycle. Crossref; not read.
//!
//! ## Used only here
//!
//! All checked on Crossref and not read unless the entry says otherwise.
//!
//! - B. A. Galler and M. J. Fischer, "An improved equivalence algorithm", CACM 7(5), 1964,
//!   pp. 301-303, doi:10.1145/364099.364331 (Crossref spells the second author "Fisher"): the
//!   union-find forest with union by size.
//! - C. Okasaki, *Purely Functional Data Structures*, Cambridge University Press, 1998,
//!   doi:10.1017/cbo9780511530104, ch. 2: the persistent list as a shared stack.
//! - D. J. Pearce and P. H. J. Kelly, "A dynamic topological sort algorithm for directed acyclic
//!   graphs", ACM J. Experimental Algorithmics 11, doi:10.1145/1187436.1210590 (Crossref dates
//!   it 2007-02-09; the uses' "2006" is the volume's year): on an edge against the order, search
//!   forward from its head and backward from its tail only within the affected range of ranks,
//!   then reorder those nodes.
//! - P. Dietz and D. Sleator, "Two algorithms for maintaining order in a list", STOC 1987,
//!   pp. 365-372, doi:10.1145/28395.28434; M. A. Bender, R. Cole, E. D. Demaine,
//!   M. Farach-Colton and J. Zito, "Two simplified algorithms for maintaining order in a list",
//!   ESA 2002, LNCS, pp. 152-164, doi:10.1007/3-540-45749-6_17 (read 2026-11-20, PDF, the
//!   authors' copy): order maintenance by relabeling the smallest enclosing range of `2^i` tags
//!   whose density is at most `τ_i = T^{-i}`, `1 < T < 2`, a threshold that falls geometrically
//!   as the range doubles (section 3); quoted at `product.rs`, impl `Potential`, `rank_after`.
//! - J. Holm, K. de Lichtenberg and M. Thorup, "Poly-logarithmic deterministic fully-dynamic
//!   algorithms for connectivity, minimum spanning tree, 2-edge, and biconnectivity", J. ACM
//!   48(4), 2001, pp. 723-760, doi:10.1145/502090.502095 (named as not used).
//! - C. Schulte and P. J. Stuckey, "Efficient constraint propagation engines", ACM TOPLAS 31(1),
//!   2008, article 2, pp. 1-43, doi:10.1145/1452044.1452046, arXiv cs/0611009 (an erratum is
//!   TOPLAS 31(2), 2009, doi:10.1145/1462166.1462170): propagator events, idempotence and
//!   subsumption. The arXiv listing checked too.
//! - D. Amagata, J. Yamada, Y. Ji and T. Hara, "Efficient algorithms for top-k stabbing queries
//!   on weighted interval data (full version)", arXiv 2405.05601, 2024: the arXiv listing only.
//! - G. Averkov and M. Schymura, "Complexity of linear relaxations in integer programming",
//!   Mathematical Programming 194(1-2), 2022, pp. 191-227, doi:10.1007/s10107-021-01623-4.
//! - G. Ramalingam, J. Song, L. Joskowicz and R. E. Miller, "Solving systems of difference
//!   constraints incrementally", Algorithmica 23(3), 1999, pp. 261-275, doi:10.1007/pl00009261
//!   (named as not used).
//! - F. Cucker, P. Koiran and S. Smale, "A polynomial time algorithm for Diophantine equations
//!   in one variable", J. Symbolic Computation 27(1), 1999, pp. 21-29,
//!   doi:10.1006/jsco.1998.0242: the integer roots of a sparse polynomial with `t` terms of at
//!   most `B` bits in time polynomial in `t` and `B`.
//! - P. Jeavons and M. C. Cooper, "Tractable constraints on ordered domains", Artificial
//!   Intelligence 79(2), 1995, pp. 327-339, doi:10.1016/0004-3702(95)00107-7: max-closed
//!   constraints, for which the greatest values left by arc consistency form a solution.
//! - S. Cotton and O. Maler, "Fast and flexible difference constraint propagation for
//!   DPLL(T)", SAT 2006, LNCS, pp. 170-183, doi:10.1007/11814948_19: on adding an edge, a
//!   Dijkstra search over reduced costs finds a negative cycle through it or the new bounds.
//! - C. Bessière, J.-C. Régin, R. H. C. Yap and Y. Zhang, "An optimal coarse-grained arc
//!   consistency algorithm", Artificial Intelligence 165(2), 2005, pp. 165-185,
//!   doi:10.1016/j.artint.2005.02.004 (AC-2001; named as not used).
//! - M. H. Overmars and J. van Leeuwen, "Maintenance of configurations in the plane", JCSS
//!   23(2), 1981, pp. 166-204, doi:10.1016/0022-0000(81)90012-x: a balanced tree whose nodes
//!   keep the bridge of their children's hulls, found by descending one level a step.
//! - E. M. McCreight, "Priority search trees", SIAM J. Comput. 14(2), 1985, pp. 257-276,
//!   doi:10.1137/0214021: three-sided range queries in O(log n + f).
//! - K. Maziarz, T. Ellis, A. Lawrence, A. Fitzgibbon and S. Peyton Jones, "Hashing modulo
//!   alpha-equivalence", PLDI 2021, doi:10.1145/3453483.3454088 (named as not used).
//! - P. Cousot and R. Cousot, "Systematic design of program analysis frameworks", POPL 1979,
//!   pp. 269-282, doi:10.1145/567752.567778.
//! - J. L. Bentley, "Solutions to Klee's rectangle problems", unpublished notes, Carnegie Mellon
//!   University, 1977 (the segment tree): no DOI, not found on Crossref; from memory, not
//!   checked. G. M. Adelson-Velsky and E. M. Landis (1962), the AVL tree, and F. P. Preparata
//!   and M. I. Shamos, *Computational Geometry: An Introduction*, Springer, 1985; R. T.
//!   Rockafellar, *Convex Analysis*, Princeton, 1970, sec. 8, and A. Schrijver, *Theory of
//!   Linear and Integer Programming*, Wiley, 1986, sec. 8.2 (recession cones): books, not
//!   checked.

pub mod address;
mod divisors;
mod holes;
pub mod images;
pub mod loops;
pub mod preimage;
/// The backward transfer before S22a, which tests compare [`preimage`] with. Built only with
/// the feature `preimage-ref`, which only zed-tests enables (through zedc).
#[cfg(feature = "preimage-ref")]
#[doc(hidden)]
pub mod preimage_ref;
pub mod product;
mod shared_ints;
mod spans;
pub mod threshold;

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/scaling.rs"]
#[expect(
    dead_code,
    reason = "preimage's tests build no input before a timed run (`inputs`)"
)]
mod scaling;

// The meter's `malloc` in this crate's test binary, which `scaling` measures each run with
// (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
#[cfg(test)]
zed_alloc_count::meter_entry_points!();

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;
