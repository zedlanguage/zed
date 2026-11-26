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
//! memory of the paper. "Read 2026-11-21" means the text was found through the allpapers
//! search ladder and the entry checked against it on that date; the copy kind follows (a
//! LibGen or Sci-Hub copy is kept outside the repository, for verification only), and a
//! "Correction" says where the earlier entry, written from memory, was wrong. Papers that
//! `zedc_presburger` also uses (Pugh's Omega test, Seidel and Aragon's treaps, Tarjan's set
//! union, Blelloch, Ferizovic and Sun, Driscoll et al., Sarnak and Tarjan, Freuder, Shostak)
//! are described, with the parts used and how they were checked, in that crate's References;
//! the entries below give their citations only.
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
//!   pp. 87-90, doi:10.1090/qam/102435. All three read 2026-11-21 (PDF, LibGen, verification
//!   only). Freuder, Theorem 1 (p. 27): a search order is backtrack-free "if the level of
//!   strong consistency is greater than the width of the corresponding ordered constraint
//!   graph"; Theorem 3 (p. 30): a connected constraint graph has width 1 iff it is a tree, so
//!   on a tree strong 2-consistency (arc consistency) is enough. Shostak, the theorem of sec. 3
//!   (proved in sec. 7): a set of inequalities is unsatisfiable iff a graph built from it has
//!   an infeasible simple loop, one whose residue reads `0 <= c` with `c < 0`; for
//!   inequalities `x <= y + c`, Pratt's case that the abstract recalls and the paper
//!   generalizes, that is a loop of negative weight. Bellman, secs. 3 and 5: the least times
//!   `f_i = min_j (t_ij + f_j)`, `f_N = 0`, are found by successive approximation, and "at
//!   most (N - 1) iterations are required" (p. 89). Correction to the earlier entry, written
//!   from memory: Bellman assumes every `t_ij > 0` (sec. 4) and has no negative cycles and
//!   no test for one; the extra relaxation that shows a negative cycle is the later
//!   Bellman-Ford folklore, not this paper.
//!
//! ## Used only here
//!
//! All checked on Crossref; each entry says whether and how the text was read.
//!
//! - B. A. Galler and M. J. Fischer, "An improved equivalence algorithm", CACM 7(5), 1964,
//!   pp. 301-303, doi:10.1145/364099.364331 (Crossref spells the second author "Fisher", and
//!   so does the paper's byline). Read 2026-11-21 in full (PDF, LibGen, verification only).
//!   Used: each equivalence class is a tree, each node linked to "the node just above it",
//!   and each link carries "the (signed) distance" between the two nodes, so that the
//!   distance between any two nodes is the sum of the distances along a path between them
//!   (p. 302): the union-find with offsets of `product.rs`, `impl NameProducts`. Correction
//!   to the earlier entry, written from memory: the paper does not link by size. It says
//!   "either may be linked to the other" and links "the higher-numbered root ... to the
//!   lower-numbered root" (p. 303), for the address assignment. Tarjan and van Leeuwen
//!   (J. ACM 31(2), 1984, above; read 2026-11-20) credit linking by size to this paper
//!   (sec. 2), which its text does not bear out; their Lemma 1 (`size(x) >= 2^rank(x)`) and
//!   Corollary 2 ("no path has length exceeding log n") are the bound used for linking by
//!   size here.
//! - C. Okasaki, *Purely Functional Data Structures*, Cambridge University Press, 1998,
//!   doi:10.1017/cbo9780511530104, ch. 2: the persistent list as a shared stack. Read
//!   2026-11-21 in a DjVu scan from LibGen (verification only; its OCR text layer read
//!   through the installed libdjvulibre). Sec. 2.1, pp. 7-10: the stack signature (Figure
//!   2.1: `empty`, `isEmpty`, `cons`, `head`, `tail`) implemented as a list (Figure 2.3,
//!   `datatype a Stack = Nil | Cons of a x a Stack`); an update copies only the nodes on the
//!   path to the change, and "all nodes that are not on this path are shared between the
//!   original version and the updated version" (p. 10), so `cons` is O(1) and shares the
//!   whole old list. That sharing of the tail is all the code relies on. Departure: the book
//!   relies on garbage collection to reclaim nodes (remark, p. 10); here nodes are
//!   reference-counted (`Arc`) and dropped by a loop (`product::Pending`'s `Drop`).
//! - D. J. Pearce and P. H. J. Kelly, "A dynamic topological sort algorithm for directed acyclic
//!   graphs", ACM J. Experimental Algorithmics 11, article 1.7, 2006,
//!   doi:10.1145/1187436.1210590 (Crossref dates it 2007-02-09; the running head says 2006).
//!   Read 2026-11-21 (PDF, LibGen, verification only). Definition 2.5: for an inserted edge
//!   `x → y` with `ord(y) < ord(x)`, the affected region is `{k | ord(y) <= ord(k) <= ord(x)}`;
//!   sec. 3.1.1: `δxy` "is identified using a forward depth-first search from y and a backward
//!   depth-first search from x. Vertices outside the affected region are not explored"; sec.
//!   3.1.2: the two sets are sorted by `ord` and given the pooled old indices, backward set
//!   first, in `O(δ log δ)` (Lemma 3.1 proves the result a topological order). The earlier
//!   entry agreed with this.
//! - P. Dietz and D. Sleator, "Two algorithms for maintaining order in a list", STOC 1987,
//!   pp. 365-372, doi:10.1145/28395.28434 (read 2026-11-21, PDF, LibGen, verification only:
//!   Theorem 3, the first algorithm's insert costs O(log M) amortized, O(log n) with the
//!   arena resized, and the end of sec. 3 builds the O(1) amortized list of sublists of
//!   O(log M) records on it, a scheme the introduction credits to Tarjan and to Tsakalidis;
//!   this is what `product.rs`, `rank_after`, says of it); M. A. Bender, R. Cole, E. D. Demaine,
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
//!   TOPLAS 31(2), 2009, doi:10.1145/1462166.1462170). Read 2026-11-21 from the arXiv LaTeX
//!   source of cs/0611009 (the preprint, not the TOPLAS text). Used: sec. "Fixpoint
//!   Reasoning", a propagator `f` is idempotent when `f(D) = f(f(D))`, so it need not be run
//!   again on its own output; sec. "Event Reasoning", the events fix, lbc, ubc and dmc (a
//!   variable fixed, its lower or upper bound changed, its domain changed) say which
//!   propagators to queue again, and a propagator is subsumed by `D` when `f(D') = D'` for
//!   every `D' ⊑ D`, so it can be dropped; the figure "isolv" runs the queue to a fixpoint.
//! - D. Amagata, J. Yamada, Y. Ji and T. Hara, "Efficient algorithms for top-k stabbing queries
//!   on weighted interval data (full version)", arXiv 2405.05601, 2024. Read 2026-11-21 from
//!   the arXiv LaTeX source. Used: Definition 2.1, a stabbing query at `s` reports the
//!   intervals `x` with `x.l <= s <= x.r`; sec. 2.2 recalls that an interval tree answers it
//!   in `O(log n + m)` for `m` answers. Departure: their structures are static and answer
//!   weighted top-k queries (sec. 4); the code's tree is dynamic and persistent (McCreight,
//!   below, with path copying) and reports every interval stabbed.
//! - G. Averkov and M. Schymura, "Complexity of linear relaxations in integer programming",
//!   Mathematical Programming 194(1-2), 2022, pp. 191-227, doi:10.1007/s10107-021-01623-4.
//!   Read 2026-11-21 (open access; PDF, LibGen, verification only). Used: only the definition
//!   in sec. 3 (p. 199), "r ∈ R^d is a recession vector of a polyhedron P ⊆ R^d if P + r ⊆ P",
//!   the ray `{λr : λ >= 0}` a recession ray and the set of them the recession cone
//!   `rec(P)`, which `product.rs`, `Block::recession_uncertified`, uses for the strict integer
//!   recession rays that certify a group's parts. The paper's results (when relaxations of
//!   lattice-convex sets are bounded, Lemma 3.3 and the theorems on the number of
//!   inequalities) are not used.
//! - G. Ramalingam, J. Song, L. Joskowicz and R. E. Miller, "Solving systems of difference
//!   constraints incrementally", Algorithmica 23(3), 1999, pp. 261-275, doi:10.1007/pl00009261
//!   (named as not used).
//! - F. Cucker, P. Koiran and S. Smale, "A polynomial time algorithm for Diophantine equations
//!   in one variable", J. Symbolic Computation 27(1), 1999, pp. 21-29,
//!   doi:10.1006/jsco.1998.0242 (read 2026-11-21, PDF, LibGen, verification only): Theorem 1,
//!   "There is a polynomial time algorithm which given input f ∈ Z\[t\] decides whether f has
//!   an integer root and, moreover, the algorithm outputs the set of integer roots of f", in
//!   the size of the sparse encoding, the list of pairs `(i, a_i)` with `a_i != 0`: so
//!   polynomial in the number of terms and their bit sizes, as the earlier entry said.
//! - P. Jeavons and M. C. Cooper, "Tractable constraints on ordered domains", Artificial
//!   Intelligence 79(2), 1995, pp. 327-339, doi:10.1016/0004-3702(95)00107-7. Read 2026-11-21
//!   (PDF, LibGen, verification only). Definition 2.5: a constraint is max-closed when the
//!   componentwise maximum of two of its tuples is again a tuple of it. Theorem 4.2: a
//!   pairwise-consistent problem whose constraints are max-closed "either has a solution or
//!   has an empty constraint"; the proof takes for each variable the greatest value left, and
//!   shows these values satisfy every constraint. For binary constraints pairwise consistency
//!   is arc consistency (p. 330), so the earlier entry, "the greatest values left by arc
//!   consistency form a solution", holds for binary constraints, which is the case used
//!   (`product.rs`, the projection of a tree of difference constraints by shortest paths;
//!   `holes.rs`, the module comment).
//! - S. Cotton and O. Maler, "Fast and flexible difference constraint propagation for
//!   DPLL(T)", SAT 2006, LNCS, pp. 170-183, doi:10.1007/11814948_19. Read 2026-11-21 (PDF,
//!   Sci-Hub, verification only; a copy fetched for an earlier review). Definition 2: given a
//!   potential `π` with `π(x) + c - π(y) >= 0` on each edge and a new edge `u → v`, find a
//!   potential for the larger graph if one exists; Fig. 1 does it by a Dijkstra-like scan
//!   from `v` of `γ`, how far each potential must fall, and Theorem 2 proves it finds a
//!   negative cycle exactly when `γ(u) < 0` and otherwise returns a valid potential, in
//!   `O(m + n log n)` (Theorem 3). Sec. 4 then finds the implied bounds by Dijkstra over the
//!   reduced costs `π(x) + c - π(y)`, after Johnson. The paper credits the consistency check
//!   to Frigioni et al. The earlier entry agreed with this.
//! - E. W. Dijkstra, "A note on two problems in connexion with graphs", Numerische Mathematik
//!   1, 1959, pp. 269-271, doi:10.1007/BF01386390 (read 2026-11-21, PDF, LibGen, verification
//!   only): Problem 2, the path of least length from `P` to `Q`; nodes enter set A "in order
//!   of increasing minimum path length from node P", each by Step 2, the node of set B at
//!   least distance (p. 270). Branch lengths there are lengths, so not negative; `holes` and
//!   `product.rs` meet this by searching over the weights reduced by a potential. Full
//!   comment at the head of zed-graph `heap.rs`.
//! - C. Bessière, J.-C. Régin, R. H. C. Yap and Y. Zhang, "An optimal coarse-grained arc
//!   consistency algorithm", Artificial Intelligence 165(2), 2005, pp. 165-185,
//!   doi:10.1016/j.artint.2005.02.004 (AC-2001; named as not used). Read 2026-11-21 (PDF,
//!   LibGen, verification only): AC2001/3.1 keeps `Last((x_i, a), x_j)`, the support last
//!   found for `a` on `x_j`, and resumes the search for a new support after it, which makes it
//!   optimal, `O(ed^2)` time for `e` constraints on domains of size `d`.
//! - M. H. Overmars and J. van Leeuwen, "Maintenance of configurations in the plane", JCSS
//!   23(2), 1981, pp. 166-204, doi:10.1016/0022-0000(81)90012-x. Read 2026-11-21 (PDF, LibGen,
//!   verification only). Theorem 3.2: the hull of the union of two sets separated by a line,
//!   each hull kept in a concatenable queue, is found in `O(log n)` steps by finding the
//!   bridge, a binary search that drops part of one hull or the other at each step. Sec. 4:
//!   a balanced tree whose nodes keep the part of their hull not passed up and the position
//!   of the bridge of their two children's hulls; Lemma 4.3, an update costs
//!   `O(log^2 n + R)`. Departure: the code keeps only the bridge at each node, in a persistent
//!   AVL tree of dual points, and finds it by the same descent one level a step; the earlier
//!   entry agreed with this.
//! - E. M. McCreight, "Priority search trees", SIAM J. Comput. 14(2), 1985, pp. 257-276,
//!   doi:10.1137/0214021. Read 2026-11-21 (PDF, LibGen, verification only). Abstract: insert
//!   and delete in `O(log n)`, and the pairs with `x0 <= x <= x1` and `y <= y1` enumerated in
//!   `O(log n + s)` for `s` answers, in `O(n)` space; a node holds the pair of least `y` in its
//!   subtree, a heap on `y` over a search tree on `x`. The earlier entry agreed with this.
//! - C. Carathéodory, "Über den Variabilitätsbereich der Koeffizienten von Potenzreihen, die
//!   gegebene Werte nicht annehmen", Math. Ann. 64, 1907, pp. 95-115, doi:10.1007/BF01449883.
//!   Read 2026-11-21 (the German text; PDF, LibGen, verification only). Correction to the
//!   earlier entry, written from memory: the paper does not state the theorem for cones of
//!   `d` vectors. It studies the convex hull `K_n` of the curve with coordinates
//!   `2 cos kϑ, -2 sin kϑ`, `k = 1..n`, in `2n` dimensions, and shows that each boundary
//!   point of `K_n` is a convex combination of at most `n` points of the curve (p. 109,
//!   eq. 33, "p höchstens gleich n"). The general statement used at `product.rs`, fn `in_cone`
//!   and fn `bounds_at`, a vector in the cone of a set of vectors in `d` dimensions is in the
//!   cone of `d` of them, is the later standard form that carries his name, not found in
//!   this paper; `in_cone` proves the two-dimensional case it needs itself, so nothing rests
//!   on the attribution.
//! - G. E. Blelloch and M. Reid-Miller, "Fast set operations using treaps", SPAA 1998,
//!   pp. 16-26, doi:10.1145/277651.277660: union of treaps of sizes `m <= n` in
//!   O(m log(n/m + 1)) expected time by split and join; used at `divisors.rs`, the header and
//!   fn `union`. Read 2026-11-21 (PDF, LibGen, verification only): the abstract, "For two sets
//!   of size n and m (m <= n) the algorithms run in expected O(m lg(n/m)) work", and Theorem
//!   2.4 (p. 21) for union; the proof sketch is at `divisors.rs`.
//! - K. Maziarz, T. Ellis, A. Lawrence, A. Fitzgibbon and S. Peyton Jones, "Hashing modulo
//!   alpha-equivalence", PLDI 2021, doi:10.1145/3453483.3454088 (named as not used).
//! - P. Cousot and R. Cousot, "Systematic design of program analysis frameworks", POPL 1979,
//!   pp. 269-282, doi:10.1145/567752.567778. Read 2026-11-21 (PDF, LibGen, verification only).
//!   Sec. 10.1: the direct product of two analyses (Theorem 10.1.0.1), and the reduced
//!   product (Definition 10.1.0.2), which maps a pair to the least pair with the same meaning,
//!   `σ(<P1, P2>) = ⊓{<Q1, Q2> : γ1(P1) ∧ γ2(P2) = γ1(Q1) ∧ γ2(Q2)}`: the reduced product of
//!   the domains this crate builds. The paper has no theorem on keeping a fixed point across
//!   joins; the argument at `product.rs`, the block update that cites it, is that file's own.
//! - J. L. Bentley and D. Wood, "An optimal worst case algorithm for reporting intersections of
//!   rectangles", IEEE Trans. Computers C-29(7), 1980, pp. 571-577, doi:10.1109/TC.1980.1675628
//!   (the segment tree), read 2026-11-20 in full. Sec. IV, p. 574: a segment is kept at "every
//!   node in the tree whose interval is contained in X, on the condition that that node's
//!   father is not also contained in X", and "the algorithm visits at most four nodes and
//!   marks at most two nodes on each of the lg m + 1 levels"; so a range query or update
//!   touches O(log m) nodes, the bound used here. Their reference 2, "a very similar
//!   structure", is J. L. Bentley, "Algorithms for Klee's rectangle problems", unpublished
//!   notes, Carnegie-Mellon Univ., 1977, which van Leeuwen and Wood (Utrecht report
//!   RUU-CS-79-06, 1979, p. 20, reference 1, read 2026-11-20) cite as "Solutions to Klee's
//!   rectangle problems": not read, and nothing here rests on it. Searched under both titles
//!   on 2026-11-21 through every allpapers rung, and again that day with more repositories
//!   (CITE-unfound-four), without finding a copy; the rungs and their
//!   results are listed at the module comment of `zed_collections::min_add`. G. M.
//!   Adelson-Velsky and E. M. Landis (1962), the AVL tree (Dokl. Akad. Nauk SSSR 146(2),
//!   pp. 263-266, read 2026-11-21 at Math-Net.Ru; full comment at `Staircase` in
//!   `product.rs`), and F. P. Preparata and M. I. Shamos, *Computational
//!   Geometry: An Introduction*, Springer, 1985, doi:10.1007/978-1-4612-1098-6 (read
//!   2026-11-21, PDF, LibGen, verification only: sec. 7.2.4, the intersection of `N`
//!   half-planes by divide and conquer, `T(N) = 2T(N/2) + O(N)`, and Theorem 7.10, p. 289,
//!   `Θ(N log N)` and optimal; the use is at `product.rs`, fn `extreme_base`); R. T.
//!   Rockafellar, *Convex Analysis*, Princeton, 1970, sec. 8, and A. Schrijver, *Theory of
//!   Linear and Integer Programming*, Wiley, 1986, sec. 8.2 (recession cones). Rockafellar read
//!   2026-11-21 (scan, LibGen, verification only): p. 61, `C` "recedes in the direction of
//!   y" when "x + λy ∈ C for every λ ≥ 0 and x ∈ C", the set of such `y` with 0 being "the
//!   recession cone of C", written `0+C`, and Theorem 8.1, it "is then a convex cone
//!   containing the origin"; p. 62, for `C = {x | ⟨x, b_i⟩ ≥ β_i, ∀i ∈ I} ≠ ∅` "the
//!   recession cone of C is given by the corresponding system of homogeneous inequalities",
//!   `0+C = {x | ⟨x, b_i⟩ ≥ 0, ∀i ∈ I}`. That is the fact `product.rs` uses
//!   (fn `recession_cone_uncertified`, whose proof is given there in full): a part's rows
//!   hold along a direction `r` from every point that meets them iff `a.r ≥ 0` for each row
//!   `a`. Schrijver read the same day (LibGen PDF, verification only): sec. 8.2, p. 100,
//!   `char.cone P := {y | x + y ∈ P for all x in P} = {y | Ay ≤ 0}` for `P = {x | Ax ≤ b}`
//!   nonempty, "[Some authors call char.cone P the recession cone of P.]", the same statement
//!   with the rows' signs reversed. Departure: the code moves integer points and needs a
//!   rational direction, which neither book treats at this place; the proof there picks one
//!   from an open set of directions.

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
use zed_testkit::scaling;

// The meter's `malloc` in this crate's test binary, which `scaling` measures each run with
// (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
#[cfg(test)]
zed_alloc_count::meter_entry_points!();

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
use zed_testkit::seed;
