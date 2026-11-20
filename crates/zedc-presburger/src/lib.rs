//! The Presburger arithmetic of the compiler `zedc`'s constraint store (DESIGN.md
//! sec:constraints, step L1.38): formulas over integer variables and the Omega test that decides
//! them, the conjunctions they are split into, and the convex hull of their pieces. `zedc`
//! re-exports each module at its old path (`zedc::store::presburger`, ...).
//!
//! # References
//!
//! The published work this crate's code takes an algorithm, a bound, a lemma or a complexity
//! claim from. A comment at each use names the paper in short form ("Pugh 1991, sec. 2.3.2")
//! and sketches the part used there; the full citation and how it was checked are here, once.
//! "Crossref" means that a lookup of the DOI on api.crossref.org on 2026-11-20 gave the authors,
//! title, venue, volume and pages written here; "not read" means that only that metadata was
//! checked, and the sketch at the use was written from memory of the paper.
//!
//! ## Integer linear constraints
//!
//! - W. Pugh, "The Omega test: a fast and practical integer programming algorithm for
//!   dependence analysis", Supercomputing '91, ACM, 1991, pp. 4-13, doi:10.1145/125826.125848.
//!   W. Pugh, "A practical algorithm for exact array dependence analysis", Communications of the
//!   ACM 35(8), 1992, pp. 102-114, doi:10.1145/135226.135233. The second is the expanded journal
//!   version of the first, under a different title; comments before 2026-11-20 sometimes gave
//!   the first title with the second venue, and were corrected. Section numbers below are those
//!   of the author's expanded text (www.cs.umd.edu/~pugh/papers/omega.pdf, headed "Originally
//!   appeared at Supercomputing '91. This expanded version appeared in Comm. of the ACM, August
//!   1992"), whose headings the CACM print gives without numbers. Used:
//!   sec. 2.1, normalizing: divide a row by the gcd `g` of its variable coefficients, floor the
//!   constant of an inequality, and an equality whose constant `g` does not divide has no point;
//!   sec. 2.2, equalities: solve for a unit-coefficient variable, else, with `a_k` the
//!   coefficient of least absolute value and `m = |a_k| + 1`, add a variable `σ` and the row
//!   `m·σ = sum_i (a_i mod^ m)·x_i`, where `a mod^ b = a - b·floor(a/b + 1/2)` (the symmetric
//!   remainder, `zedc_int::Int::mod_hat`), and solve that for `x_k`, which shrinks the
//!   coefficients; sec. 2.3.1, the real shadow: a lower bound `β <= b·z` and an upper bound
//!   `a·z <= α`, `a, b > 0`, give `a·β <= b·α`; sec. 2.3.2, the dark shadow
//!   `b·α - a·β >= (a - 1)·(b - 1)`, every integer point of which has an integer `z` above it,
//!   equal to the real shadow when `a = 1` or `b = 1` (an exact projection, taken when every
//!   lower or every upper coefficient of `z` is 1), and otherwise the splinters (the paper
//!   says "a set of planes that are parallel to a lower bound"; "splinter" is the later name,
//!   used in this crate): with `a` the
//!   largest upper coefficient, for each lower bound `b·z >= β` the problem with
//!   `b·z = β + i` for each `0 <= i <= (a·b - a - b) / a`; the problem has an integer point
//!   exactly when the dark shadow or a splinter has one; sec. 2.3.3, "An Omega test nightmare",
//!   `27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4`, which has no integer point while its real
//!   shadow has some; sec. 4, projection onto protected variables. Checked 2026-11-20: Crossref
//!   for both DOIs; the expanded text read in full for secs. 2-4 (the formulas above are
//!   quoted from it); the CACM print (an OCR of the ACM copy) read for the dark-shadow formula
//!   and the headings. By that OCR's page numbers the dark shadow and the exact projection are
//!   on p. 104 or 105 (the page-105 number is missing), not p. 106 as some comments had it, so
//!   the comments now name the section instead. The Supercomputing '91 print was not read.
//!   Tests:
//!   `presburger::exact::projection::tests::the_omega_nightmare_has_no_point` and the nightmare
//!   case in `presburger::tests` check the example (enumeration over `-50..=50` in both
//!   coordinates, 2026-11-20, finds no point, and none with 45 raised to 46); a dark shadow
//!   written with `a·b` in place of `(a - 1)·(b - 1)` drops points, which the projection tests
//!   against enumeration (`small_systems_project_to_their_enumerated_values`) catch.
//!   A machine-checked proof of the test, including the dark shadow, is in Brănici-Faraon,
//!   Ciobâcă and Gratie, "Formalizing the Omega test in Dafny", EPTCS 452, 2026,
//!   pp. 67-81, doi:10.4204/eptcs.452.5 (Crossref 2026-11-20); it was consulted when the
//!   dark-shadow rule here was reviewed, and not read for this note.
//! - G. B. Dantzig and B. C. Eaves, "Fourier-Motzkin elimination and its dual", J. Combinatorial
//!   Theory A 14(3), 1973, pp. 288-297, doi:10.1016/0097-3165(73)90004-6; Pugh's sec. 2.3.1
//!   cites it for Fourier-Motzkin elimination. J. B. J. Fourier (1827) and T. S. Motzkin,
//!   "Beiträge zur Theorie der linearen Ungleichungen" (dissertation, Basel, 1936), named at the
//!   uses, have no DOI and were not read. Crossref for Dantzig and Eaves; not read.
//! - R. R. Meyer, "On the existence of optimal solutions to integer and mixed-integer
//!   programming problems", Mathematical Programming 7(1), 1974, pp. 223-235,
//!   doi:10.1007/bf01585518: the integer hull of a rational polyhedron is a rational polyhedron
//!   with the same recession cone. Crossref; not read.
//! - R. Shostak, "Deciding linear inequalities by computing loop residues", J. ACM 28(4), 1981,
//!   pp. 769-779, doi:10.1145/322276.322288: a system of two-variable rows is infeasible over the
//!   reals exactly when a simple loop of its graph has an infeasible residue. Crossref; not read.
//! - D. Monniaux, "Quantifier elimination by lazy model enumeration", CAV 2010, LNCS,
//!   pp. 585-599, doi:10.1007/978-3-642-14295-6_51: project by taking a model, generalizing it
//!   to a cube, projecting the cube and blocking it, until no model is left. Crossref; not read.
//! - N. Bjørner and M. Janota, "Playing with quantified satisfaction", LPAR-20, EPiC Series in
//!   Computing 35, 2015, doi:10.29007/vv21 (Crossref gives the pages as "15-1"; the comments'
//!   "LPAR-20, 2015, sec. 2.2" is this paper). Crossref; not read, so "sec. 2.2" is from
//!   memory, not checked.
//! - A. Komuravelli, A. Gurfinkel and S. Chaki, "SMT-based model checking for recursive
//!   programs", CAV 2014, LNCS, pp. 17-34, doi:10.1007/978-3-319-08867-9_2, arXiv
//!   1405.4028; journal version in Formal Methods in System Design 48(3), 2016, pp. 175-205,
//!   doi:10.1007/s10703-016-0249-4: model-based projection for linear integer arithmetic,
//!   which keeps of Cooper's method, for the model at hand, only the one disjunct that model
//!   satisfies. Crossref and the arXiv listing; not read.
//! - M. Karr, "Affine relationships among variables of a program", Acta Informatica 6(2), 1976,
//!   pp. 133-151, doi:10.1007/bf00268497: the affine equalities that hold on a set of points,
//!   kept in echelon form, and the join of two such sets of equalities (`hull`). Crossref; not
//!   read.
//! - H. W. Lenstra Jr., "Integer programming with a fixed number of variables", Mathematics of
//!   Operations Research 8(4), 1983, pp. 538-548, doi:10.1287/moor.8.4.538: integer
//!   feasibility in fixed dimension in polynomial time; the three-variable case is decided by
//!   `zedc_solvers::live3`, whose crate docs sketch the method. Crossref; not read.
//! - M. R. Garey and D. S. Johnson, *Computers and Intractability*, W. H. Freeman, 1979, problem
//!   AN2, simultaneous incongruences, NP-complete; named where an exact projection of
//!   congruences is given up. A book; from memory, not checked.
//!
//! ## Graphs and constraint networks
//!
//! - A. B. Kahn, "Topological sorting of large networks", CACM 5(11), 1962, pp. 558-562,
//!   doi:10.1145/368996.369025: repeatedly take a node with no edge into it from the nodes not
//!   yet taken ("Kahn's order"). Crossref; not read.
//! - E. W. Dijkstra, "A note on two problems in connexion with graphs", Numerische Mathematik
//!   1(1), 1959, pp. 269-271, doi:10.1007/bf01386390; R. Bellman, "On a routing problem",
//!   Quarterly of Applied Mathematics 16(1), 1958, pp. 87-90, doi:10.1090/qam/102435
//!   (Bellman-Ford, the tests' reference for difference rows). Crossref; not read.
//! - J. Holm, K. de Lichtenberg and M. Thorup, "Poly-logarithmic deterministic fully-dynamic
//!   algorithms for connectivity, minimum spanning tree, 2-edge, and biconnectivity", J. ACM
//!   48(4), 2001, pp. 723-760, doi:10.1145/502090.502095: named in `conjuncts` as the bound
//!   not taken. Crossref; not read.
//!
//! - R. E. Tarjan, "Depth-first search and linear graph algorithms", SIAM J. Comput. 1(2), 1972,
//!   pp. 146-160, doi:10.1137/0201010: biconnected components and strongly connected components
//!   in linear time by depth-first search with low links. Crossref; not read.
//! - E. C. Freuder, "A sufficient condition for backtrack-free search", J. ACM 29(1), 1982,
//!   pp. 24-32, doi:10.1145/322290.322292: a tree-structured network made arc consistent is
//!   solved without backtracking in an order from the root. Crossref; not read.
//! - R. Dechter, "Bucket elimination: a unifying framework for reasoning", Artificial
//!   Intelligence 113(1-2), 1999, pp. 41-85, doi:10.1016/s0004-3702(99)00059-4. S. L. Lauritzen
//!   and D. J. Spiegelhalter, "Local computations with probabilities on graphical structures and
//!   their application to expert systems", J. Royal Statistical Society B 50(2), 1988,
//!   pp. 157-194, doi:10.1111/j.2517-6161.1988.tb01721.x. Both: Crossref; not read.
//! - A. Darwiche and P. Marquis, "A knowledge compilation map", J. Artificial Intelligence
//!   Research 17, 2002, pp. 229-264, doi:10.1613/jair.989. Crossref; not read.
//! - E. Cuthill and J. McKee, "Reducing the bandwidth of sparse symmetric matrices", Proc. 24th
//!   ACM National Conference, 1969, pp. 157-172, doi:10.1145/800195.805928. C. H. Papadimitriou,
//!   "The NP-completeness of the bandwidth minimization problem", Computing 16(3), 1976,
//!   pp. 263-270, doi:10.1007/bf02280884. Both: Crossref; not read.
//! - B. Baetz and D. R. Wood, "Brooks' vertex-colouring theorem in linear time", arXiv
//!   1401.8023, 2014. Read 2026-11-20 (the arXiv PDF): Lemma 1, colorings of the biconnected
//!   components combine in O(|V| + |E|); Lemma 2, two vertices `a`, `b` at distance 2 with
//!   `G - {a, b}` connected give a Δ-coloring by coloring `a` and `b` alike and the rest in the
//!   reverse of a search order from a common neighbor; Lemma 3, such `a`, `b` are found in
//!   linear time in a biconnected graph that is neither complete nor a cycle. Not on Crossref
//!   (no journal version found).
//! - C. Berkholz, P. Bonsma and M. Grohe, "Tight lower and upper bounds for the complexity of
//!   canonical colour refinement", Theory of Computing Systems 60(4), 2017, pp. 581-614,
//!   doi:10.1007/s00224-016-9686-0, arXiv 1509.08251: sec. 3, "A fast canonical colour
//!   refinement algorithm". Crossref; the arXiv PDF read for the section's title and number.
//!   J. Cardon and M. Crochemore, "Partitioning a graph in O(|A| log2 |V|)", Theoretical
//!   Computer Science 19(1), 1982, pp. 85-98, doi:10.1016/0304-3975(82)90016-0. R. Paige and
//!   R. E. Tarjan, "Three partition refinement algorithms", SIAM J. Comput. 16(6), 1987,
//!   pp. 973-989, doi:10.1137/0216062. Both: Crossref; not read. J. Hopcroft, "An n log n
//!   algorithm for minimizing states in a finite automaton", Theory of Machines and
//!   Computations, Academic Press, 1971, pp. 189-196, doi:10.1016/b978-0-12-417750-5.50022-1:
//!   after a split, refine by all the new classes but the largest ("process the smaller half"),
//!   so each element is in O(log n) refining classes. Crossref; not read.
//!
//! ## Sets, trees and persistence
//!
//! - R. E. Tarjan, "Efficiency of a good but not linear set union algorithm", J. ACM 22(2),
//!   1975, pp. 215-225, doi:10.1145/321879.321884, and R. E. Tarjan and J. van Leeuwen,
//!   "Worst-case analysis of set union algorithms", J. ACM 31(2), 1984, pp. 245-281,
//!   doi:10.1145/62.2160: union by rank with path compression costs O(α(n)) amortized an
//!   operation; union by rank alone keeps a tree's height at most `floor(log2 n)`. Crossref;
//!   not read.
//! - R. Seidel and C. R. Aragon, "Randomized search trees", Algorithmica 16(4-5), 1996,
//!   pp. 464-497, doi:10.1007/bf01940876 (FOCS 1989, pp. 540-545, doi:10.1109/sfcs.1989.63531):
//!   Theorem 3.1, a treap of `n` items has expected access, insertion and deletion time
//!   O(log n); Theorem 3.3, "All the results of Theorem 3.1 continue to hold, up to constant
//!   factors, if the priorities are 8-wise independent random variables ... In order to achieve
//!   logarithmic expected access, insertion, and deletion time, 5-wise independence suffices";
//!   sec. 6, "Limited Randomness", proves it. The uses rely on the 5-wise case with priorities
//!   from `zed_kernel::priority`. Checked 2026-11-20: Crossref, and the authors' text
//!   (faculty.washington.edu/aragon/pubs/rst96.pdf) read for Theorems 3.1 and 3.3 and the title
//!   of sec. 6; the proof in sec. 6 was not checked line by line.
//! - G. E. Blelloch, D. Ferizovic and Y. Sun, "Just join for parallel ordered sets", SPAA 2016,
//!   pp. 253-264, doi:10.1145/2935764.2935768, arXiv 1602.02120: union, intersection and
//!   difference of sets of sizes `m <= n` by `join` in O(m log(n/m + 1)) work. M. R. Brown and
//!   R. E. Tarjan, "A fast merging algorithm", J. ACM 26(2), 1979, pp. 211-226,
//!   doi:10.1145/322123.322127, the same bound for merging. F. K. Hwang and S. Lin, "A simple
//!   algorithm for merging two disjoint linearly ordered sets", SIAM J. Comput. 1(1), 1972,
//!   pp. 31-39, doi:10.1137/0201004. All: Crossref; not read. E. D. Demaine, A. López-Ortiz and
//!   J. I. Munro, "Adaptive set intersections, unions, and differences", SODA 2000: not on
//!   Crossref; from memory, not checked.
//! - J. R. Driscoll, N. Sarnak, D. D. Sleator and R. E. Tarjan, "Making data structures
//!   persistent", J. Computer and System Sciences 38(1), 1989, pp. 86-124,
//!   doi:10.1016/0022-0000(89)90034-2. N. Sarnak and R. E. Tarjan, "Planar point location using
//!   persistent search trees", CACM 29(7), 1986, pp. 669-679, doi:10.1145/6138.6151. Both:
//!   Crossref; not read. O. Liljenzin, "Confluently persistent sets and maps", arXiv 1301.3388,
//!   2013: the arXiv listing; not read.
//! - D. D. Sleator and R. E. Tarjan, "A data structure for dynamic trees", J. Computer and System
//!   Sciences 26(3), 1983, pp. 362-391, doi:10.1016/0022-0000(83)90006-5 (STOC 1981,
//!   pp. 114-122): link, cut and path queries in O(log n) amortized by splaying the auxiliary
//!   trees of a path decomposition. Crossref; not read.
//! - K. Mehlhorn, R. Sundar and C. Uhrig, "Maintaining dynamic sequences under equality tests in
//!   polylogarithmic time", Algorithmica 17(2), 1997, pp. 183-198, doi:10.1007/bf02522825.
//!   A. Jeż, "Recompression: a simple and powerful technique for word equations", J. ACM 63(1),
//!   2016, pp. 1-51, doi:10.1145/2743014 (the use had "2015"; Crossref gives 2016).
//!   Both: Crossref; not read. T. I, "Longest common extensions with recompression", CPM 2017:
//!   not found on Crossref; from memory, not checked.
//! - D. Chambi, D. Lemire, O. Kaser and R. Godin, "Better bitmap performance with Roaring
//!   bitmaps", Software: Practice and Experience 46(5), 2016, pp. 709-719, doi:10.1002/spe.2325,
//!   and D. Lemire, G. Ssi-Yan-Kai and O. Kaser, "Consistently faster and smaller compressed
//!   bitmaps with Roaring", ibid. 46(11), 2016, pp. 1547-1569, doi:10.1002/spe.2402. Crossref;
//!   not read.
//! - P. M. Fenwick, "A new data structure for cumulative frequency tables", Software: Practice
//!   and Experience 24(3), 1994, pp. 327-336, doi:10.1002/spe.4380240306: node `i` covers the
//!   `i & -i` entries ending at `i`, so a prefix query or an update visits O(log n) nodes.
//!   Crossref; not read.
//! - J.-P. Aumasson and D. J. Bernstein, "SipHash: a fast short-input PRF", INDOCRYPT 2012,
//!   LNCS 7668, pp. 489-508, doi:10.1007/978-3-642-34931-7_28: the standard library's default
//!   hash, named where a faster unkeyed hash (FxHash) replaces it for keys no input chooses.
//!   Crossref; not read.
//!
//! ## Geometry
//!
//! - A. M. Andrew, "Another efficient algorithm for convex hulls in two dimensions", Information
//!   Processing Letters 9(5), 1979, pp. 216-219, doi:10.1016/0020-0190(79)90072-3: the monotone
//!   chain hull of sorted points in linear time. Crossref; not read.
//! - B. Chazelle and D. P. Dobkin, "Intersection of convex objects in two and three dimensions",
//!   J. ACM 34(1), 1987, pp. 1-27, doi:10.1145/7531.24036. M. I. Shamos and D. Hoey, "Geometric
//!   intersection problems", FOCS 1976, pp. 208-215, doi:10.1109/sfcs.1976.16. Both: Crossref;
//!   not read; the uses' "Theorem 3" of Chazelle and Dobkin is from memory, not checked.
//! - G. Montúfar, R. Pascanu, K. Cho and Y. Bengio, "On the number of linear regions of deep
//!   neural networks", NIPS 2014, arXiv 1402.1869: the arXiv listing; not read.
//! - T. Zaslavsky, "Facing up to arrangements: face-count formulas for partitions of space by
//!   hyperplanes", Memoirs of the AMS 1(154), 1975, doi:10.1090/memo/0154: `c` lines in the
//!   plane cut it into at most `1 + c + c(c-1)/2` regions, with equality in general position.
//!   Crossref; not read (the count is elementary: the `k`-th line crosses at most `k - 1`
//!   earlier lines and so adds at most `k` regions).
//!
//! ## Numbers and sums
//!
//! - D. J. Bernstein, "Factoring into coprimes in essentially linear time", J. Algorithms 54(1),
//!   2005, pp. 1-30, doi:10.1016/j.jalgor.2004.04.009. Read 2026-11-20: the author's text of
//!   2004-04-04 (cr.yp.to/lineartime/dcba-20040404.pdf), whose numbering the uses follow:
//!   Algorithm 11.4, `(gcd, ppg, pple)(a, b)`; 13.2, the natural coprime base `cb{a, b}`; 16.2,
//!   `cb(P ∪ {b})` for coprime `P`; 17.3, `cb(P ∪ Q)` for coprime `P` and `Q`; 18.1, `cb S` by
//!   halving `S` and merging with 17.3; 21.2, factoring over a coprime base. The journal print
//!   was not read, so its numbering is not checked against this.
//! - R. Bellman, *Dynamic Programming*, Princeton University Press, 1957 (no DOI checked).
//!   E. Horowitz and S. Sahni, "Computing partitions with applications to the knapsack
//!   problem", J. ACM 21(2), 1974, pp. 277-292, doi:10.1145/321812.321823 (meet in the middle).
//!   D. Pisinger, "Linear time algorithms for knapsack problems with bounded weights",
//!   J. Algorithms 33(1), 1999, pp. 1-14, doi:10.1006/jagm.1999.1034. Z. Galil and O. Margalit,
//!   "An almost linear-time algorithm for the dense subset-sum problem", SIAM J. Comput. 20(6),
//!   1991, pp. 1157-1189, doi:10.1137/0220072. K. Koiliaris and C. Xu, "A faster
//!   pseudopolynomial time algorithm for subset sum", SODA 2017, pp. 1062-1072,
//!   doi:10.1137/1.9781611974782.68. K. Bringmann, "A near-linear pseudopolynomial time
//!   algorithm for subset sum", SODA 2017, pp. 1073-1084, doi:10.1137/1.9781611974782.69.
//!   R. M. Karp, "Reducibility among combinatorial problems", Complexity of Computer
//!   Computations, 1972, pp. 85-103, doi:10.1007/978-1-4684-2001-2_9. All: Crossref; not read.
//!   L. A. Levin, "Universal sequential search problems", Problems of Information Transmission
//!   9(3), 1973: not on Crossref; from memory, not checked.
//! - K. Bringmann and P. Wellnitz, "On near-linear-time algorithms for dense subset sum",
//!   SODA 2021, pp. 1777-1796, doi:10.1137/1.9781611976465.107, arXiv 2010.09096. Read
//!   2026-11-20 (the arXiv PDF) for Theorem 4.2, "Structural Part, Formal Version of Theorem
//!   3.3": a `C_δ`-dense multiset `X` with no `C_α`-almost divisor has every sum in
//!   `[λ_X, Σ_X - λ_X]`, `λ_X = C_λ·μ_X·mx_X·Σ_X/|X|²`, with `C_δ = 1699200·log(2n)·log²(2μ_X)`,
//!   `C_α = 42480·log(2μ_X)` and `C_λ = 169920·log(2μ_X)`.

pub mod conjuncts;
pub mod hull;
pub mod presburger;
pub mod upper_hull;

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/scaling.rs"]
#[expect(
    dead_code,
    reason = "presburger's tests use only some of the shared checks"
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
