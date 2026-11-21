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
//!   the comments now name the section instead. The Supercomputing '91 print was read
//!   2026-11-21 for secs. 2.1-2.3.3 (PDF, LibGen, verification only; printed pp. 5-7): it has
//!   the same section numbers and the same rules as the expanded text: sec. 2.1 floors `a_0/g`;
//!   sec. 2.2 takes `m = |a_k| + 1` and "a mod^ b = if a mod b < b/2 then a mod b else (a mod
//!   b) - b", which equals `a - b·floor(a/b + 1/2)` above, also at `a mod b = b/2`; sec. 2.3.1
//!   writes the dark shadow as `Σ a_k a'_i x_i >= (|a_k a'_k| - |a'_k| - a_k + 1) + Σ a'_k
//!   a_i x_i`, the constant `ab - a - b + 1 = (a - 1)(b - 1)`, and the splinters as
//!   `a_k x_k = j + Σ -a_i x_i` for `0 <= j <= floor((|m a_k| - |m| - a_k)/|m|)`, `m` the most
//!   negative upper-bound coefficient. Sec. 2.3.3's nightmare differs between the two: the
//!   SC'91 print has `3 <= 11x + 13y <= 21, -8 <= 7x - 9y <= 6`, the expanded text the one
//!   above; enumeration over `-60..=60` in both coordinates (awk, 2026-11-21) finds no integer
//!   point in either.
//!   Tests:
//!   `presburger::exact::projection::tests::the_omega_nightmare_has_no_point` and the nightmare
//!   case in `presburger::tests` check the example (enumeration over `-50..=50` in both
//!   coordinates, 2026-11-20, finds no point, and none with 45 raised to 46); a dark shadow
//!   written with `a·b` in place of `(a - 1)·(b - 1)` drops points, which the projection tests
//!   against enumeration (`small_systems_project_to_their_enumerated_values`) catch.
//!   A machine-checked proof of the test, including the dark shadow, is in Brănici-Faraon,
//!   Ciobâcă and Gratie, "Formalizing the Omega test in Dafny", EPTCS 452, 2026,
//!   pp. 67-81, doi:10.4204/eptcs.452.5 (Crossref 2026-11-20), read 2026-11-21 in the arXiv
//!   LaTeX source (arXiv:2609.34882). Its sec. "Verified Elimination" generates the dark shadow
//!   as `aU - bL > ab - a - b` for `L <= ax`, `bx <= U`, which over the integers is the
//!   `>= (a - 1)(b - 1)` above. Its lemma `BoundsSatisfyOriginal` proves it by contraposition:
//!   with no integer `x` and `i = floor(U/b)`, `ai + 1 <= L` and `U + 1 <= b(i + 1)`, and
//!   combining the two gaps gives `aU - bL <= ab - a - b`. It also proves the grey shadows'
//!   offsets and termination, but decides satisfiability only, with no projection; so it
//!   checks the rule this crate uses, not the crate's code.
//! - G. B. Dantzig and B. C. Eaves, "Fourier-Motzkin elimination and its dual", J. Combinatorial
//!   Theory A 14(3), 1973, pp. 288-297, doi:10.1016/0097-3165(73)90004-6; Pugh's sec. 2.3.1
//!   cites it for Fourier-Motzkin elimination. J. B. J. Fourier (1827) and T. S. Motzkin,
//!   "Beiträge zur Theorie der linearen Ungleichungen" (dissertation, Basel, 1936), named at the
//!   uses, have no DOI and were not read. Dantzig and Eaves read 2026-11-21 in the
//!   publisher's PDF (Sci-Hub mirror; copy kept outside the repository). P. 289: split the
//!   rows by the sign of `x1` into `D_i(X) <= x1`, `x1 <= E_j(X)` and `0 <= F_k(X)`; the
//!   reduced system is `D_i(X) <= E_j(X)` for all `i, j` with `0 <= F_k(X)`, and an `x1` with
//!   `max_i D_i(X) <= x1 <= min_j E_j(X)` exists whenever `X` meets it. Their proof, in full:
//!   the reduced rows follow from the old, and conversely `max D_i <= min E_j` leaves room for
//!   `x1`. They note that `p` lower and `q` upper rows become `p·q` rows, which with `p, q >= 2`
//!   "will greatly increase the number of inequalities"; the doubly exponential bound named at
//!   the uses is the count this gives over several steps (`m` rows become at most `(m/2)^2`,
//!   so `k` steps give at most about `(m/2)^(2^k)`), not a theorem of the paper. The
//!   elimination is over the reals; over the integers it is exact only when each lower or each
//!   upper coefficient of `x1` is 1 (Pugh's exact shadow), which the uses prove where they use it.
//! - R. R. Meyer, "On the existence of optimal solutions to integer and mixed-integer
//!   programming problems", Mathematical Programming 7(1), 1974, pp. 223-235,
//!   doi:10.1007/bf01585518. Read 2026-11-21 in a scan of the journal volume (LibGen; copy kept
//!   outside the repository). Theorem 3.9: for rational `A1`, `A2` the convex hull `C_m` of
//!   `{(x, y): A1 x + A2 y = b, x >= 0, y >= 0, x integer}` is polyhedral. Theorem 3.6 (pure
//!   integer, `S = {x: Ax = b, x >= 0, x integer}`): every point of `S` is a convex combination
//!   of the finitely many extreme points of `S` (Theorem 3.4) plus a vector of
//!   `H = {x: Ax = 0, x >= 0, x rational}`; the proof is by Farkas' lemma, a point outside that
//!   form giving a `μ > 0` that no extreme point can minimize. Meyer does not state "the
//!   integer hull has the recession cone of `P`" as a theorem; the use relies on it only in
//!   this form, for a `P` with an integer point `x0`: (a) a rational ray `r` of `P`'s cone
//!   scaled to an integer `r'` gives `x0 + k r'` in `S` for every `k >= 0`; (b) a linear
//!   function unbounded over `S` is unbounded over `P`, hence (linear programming) grows
//!   along some ray of `P`'s cone, which Theorem 3.6 also shows for `S` directly. Sec. 2's
//!   example (`-αx1 + x2 <= 0` with `α` irrational) shows rationality is needed. The same
//!   statement with "same recession cone" is in A. Schrijver, *Theory of Linear and Integer
//!   Programming*, Wiley 1986, sec. 16.2 (not read here).
//! - R. Shostak, "Deciding linear inequalities by computing loop residues", J. ACM 28(4), 1981,
//!   pp. 769-779, doi:10.1145/322276.322288. Read 2026-11-21 in the publisher's PDF (LibGen;
//!   copy kept outside the repository). Correction: this entry said a two-variable system is
//!   infeasible over the reals exactly when a simple loop of its graph has an infeasible
//!   residue. The paper says that is false in general (sec. 3, p. 771: for Figure 1's `S`,
//!   "Although S is unsatisfiable, the graph has no infeasible loops, simple or otherwise");
//!   its theorem (p. 772, proved in sec. 7) is about a closure `G'`, the graph with one new
//!   edge for each simple admissible loop labeled by that loop's residue: "S is unsatisfiable
//!   if and only if G' has an infeasible simple loop". Sec. 2: one vertex per variable plus
//!   the zero variable `v0` (named `z` at the uses), one edge per inequality; a residue is the
//!   inequality transitivity gives along the path (Lemma 1). Sec. 4 is the case the uses rely
//!   on: for rows `x <= y + c` "the graph for a set S in separation theory is thus its own
//!   closure", so S is infeasible exactly when the constants around some simple loop sum to a
//!   negative number (Pratt's observation), and with integer constants such a set "is integer
//!   feasible if and only if it is real feasible". The uses (`conjuncts.rs` `Edge`,
//!   `presburger.rs` `difference_hulls`) read only difference rows and bounds, so they were not
//!   affected by the error; the shortest-path reading of the bounds is standard and is
//!   proved at `difference_hulls`, not in this paper.
//! - D. Monniaux, "Quantifier elimination by lazy model enumeration", CAV 2010, LNCS,
//!   pp. 585-599, doi:10.1007/978-3-642-14295-6_51: project by taking a model, generalizing it
//!   to a cube, projecting the cube and blocking it, until no model is left. Read 2026-11-21
//!   (the publisher's PDF, verification only) for secs. 2.2 and 3. Sec. 2.2, "Eager Model
//!   Enumeration Algorithm": an SMT solver gives a conjunction of literals `C_i` that implies
//!   `F`; "Instead of adding ¬C_i to the constraints of the system, we add ¬π(C_i)", `π` the
//!   projection of a conjunction, so the solver is called once for each disjunct of the
//!   projected result, not of the DNF of `F`; it stops because only finitely many conjunctions
//!   of `F`'s atoms exist. Sec. 3, Algorithm 2 (`Q-Test`), does the same lazily for nested
//!   quantifier blocks, adding `¬π_i(C'')` to `M_i`, with `Generalize` (Algorithm 1, the
//!   deletion filter) to shrink each conjunction; sec. 3.3 proves it correct and finite by the
//!   same finiteness of the conjunctions. With one existential block, Algorithm 2 is the loop of
//!   sec. 2.2. Departures at the use (`presburger/exact.rs`, module docs and `tried`): the
//!   blocked set is a union of intervals of one symbol, a model is asked only in its gap,
//!   the implicant is not minimized (no `Generalize`), and the cell adds the line through the
//!   model.
//! - N. Bjørner and M. Janota, "Playing with quantified satisfaction", LPAR-20 (short
//!   presentations), EPiC Series in Computing 35, 2015, pp. 15-27, doi:10.29007/vv21 (Crossref
//!   gives the pages as "15-1"). Read 2026-11-21 in the publisher's open copy (EasyChair). Sec.
//!   2.2, "Model Based Projection", Requirement 1: for `M |= F` and `φ = Mbp(M, x, F)`, `x` is
//!   not free in `φ`, `M |= φ`, `φ ⇒ ∃x F` (correctness), `φ` is no larger than `F`
//!   (complexity), finitely many models' projections cover `∃x F` (coverage) and only finitely
//!   many distinct projections arise (convergence); `Mbp` of a formula is that of the
//!   conjunction of its atoms' signs in `M`, so the comments' "sec. 2.2" is right. Sec. 2.4
//!   gives `Mbp` for integer arithmetic: the greatest lower bound in `M` resolved against each
//!   upper bound by the Omega test's dark shadow `as + (a - 1)(b - 1) <= bt` when `M` satisfies
//!   it, else by one divisibility case chosen from `M`. Departure at the use: the cell projects
//!   the whole implicant exactly (`super::eliminated`, exact and dark shadows with splinters),
//!   which implies `∃x F` and holds at the model as Requirement 1 asks, but may be larger than
//!   `F`; the coverage and convergence then follow from the finitely many implicants. Tests for
//!   both: the cover against enumerated points (`presburger::exact::tests::
//!   holed_tails_agree_in_every_order_and_with_enumerated_points` and the `..._match_
//!   enumeration` tests there) catch a cell that holds a value with no point or a loop that
//!   stops early; they cannot catch a loop that is correct but asks more questions than the
//!   bound in the module docs on inputs they do not draw.
//! - A. Komuravelli, A. Gurfinkel and S. Chaki, "SMT-based model checking for recursive
//!   programs", CAV 2014, LNCS, pp. 17-34, doi:10.1007/978-3-319-08867-9_2, arXiv
//!   1405.4028; journal version in Formal Methods in System Design 48(3), 2016, pp. 175-205,
//!   doi:10.1007/s10703-016-0249-4: model-based projection for linear integer arithmetic,
//!   which keeps of Cooper's method, for the model at hand, only the one disjunct that model
//!   satisfies. Read 2026-11-21 in the arXiv LaTeX source (1405.4028): sec. 5, "Model Based
//!   Projection": a function `Proj_λ` from models of `λ_m` to quantifier-free formulas is an
//!   MBP "iff it has a finite image, λ ≡ ⋁_{M ⊨ λ_m} Proj_λ(M), and for every model M of λ_m,
//!   M ⊨ Proj_λ(M)"; the appendix section "Model Based Projection for Linear Integer
//!   Arithmetic" (in the arXiv appendix, not the CAV body) writes Cooper's method with strict
//!   bounds `ℓ < x` as `⋁_{x=e} λ_m[e] ∨ ⋁_{ℓ<x} ⋁_{i=0}^{D-1} λ_m[ℓ + 1 + i] ∨ ⋁_{i=0}^{D-1}
//!   λ_m^{-∞}[i]`, `D` the lcm of the divisors, and `LIAProj_λ(M)` picks `λ_m[e]` if `M ⊨ x =
//!   e`, else `λ_m[ℓ + 1 + i_ℓ]` for the greatest lower bound `ℓ` that `M` satisfies, `i_ℓ =
//!   M[x - (ℓ + 1)] mod D`, else `λ_m^{-∞}[M[x] mod D]`. Lemma: it is an MBP, "The proof is
//!   similar to that of LRAProj" (finitely many disjuncts, and the disjunct picked holds at
//!   `M`, since `x` itself equals `ℓ + 1 + i_ℓ` modulo `D` and lies above `ℓ`); the paper
//!   gives no separate proof for the integer case. Departures at the use
//!   (`presburger/exact/projection.rs`, `liaproj`): bounds are non-strict, `l <= y`, so the
//!   disjunct is `l + i` with `i = (m(y) - m(l)) mod D`; non-unit coefficients are made unit by
//!   scaling to `y = L·x` with `L | y` added (the paper assumes this done); an equation
//!   `a·x + t == 0` is used by scaling each literal by `|a|` and adding `|a| | t`, the same
//!   disjunct `λ_m[e]` written without division; and with lower bounds
//!   only, the code takes the dual infinite disjunct (drop the bounds, `y = m(y) mod D`), which
//!   the paper does not write but is Cooper's method with `x` negated. Test:
//!   `presburger::exact::projection::tests::small_systems_project_to_their_enumerated_values`
//!   against enumeration catches a disjunct with a value of no point or one not holding `m`;
//!   it cannot catch a choice of disjunct that is valid but makes the cover ask more often.
//! - M. Karr, "Affine relationships among variables of a program", Acta Informatica 6(2), 1976,
//!   pp. 133-151, doi:10.1007/bf00268497: the affine equalities that hold on a set of points,
//!   kept in echelon form, and the join of two such sets of equalities (`hull`). Read
//!   2026-11-21 in the publisher's PDF (LibGen; copy kept outside the repository). Sec. 2: an
//!   affine space `ker(A, e)` is kept as the matrix-vector pair in reduced row-echelon form, a
//!   form unique to the space (2.2). (4.11): the affine union of `U1`, `U2` is the smallest
//!   affine space holding both, which exists because affine spaces are closed under
//!   intersection. (5.4), proved in the appendix: the affine union of `ker(A1, e1)` and
//!   `ker(A2, e2)` is the linear sum computed on the matrices `(A_i, e_i)` with `e_i` as one
//!   more column. Sec. 5.2 computes that sum in `n` steps, one per column, after step `s` the
//!   two matrices agreeing in their first `s` columns. Departure: `hull.rs` picks as pivot the
//!   atom the fewest rows mention, not the first column, so its form is not Karr's unique
//!   one, and its join walks persistent treaps of rows (module `hull::rows`) rather than
//!   columns; what it keeps from Karr is the definition of the join (the affine union).
//! - H. W. Lenstra Jr., "Integer programming with a fixed number of variables", Mathematics of
//!   Operations Research 8(4), 1983, pp. 538-548, doi:10.1287/moor.8.4.538: integer
//!   feasibility in fixed dimension in polynomial time; the three-variable case is decided by
//!   `zedc_solvers::live3`, whose crate docs sketch the method. Read 2026-11-21 in the
//!   publisher's scanned PDF (Sci-Hub mirror; copy kept outside the repository; also read for
//!   `zedc-solvers`, whose `lib.rs` entry quotes secs. 1 and 2 and says where `live3` departs).
//!   Sec. 1: a reduced basis of the lattice either gives a point inside the body or shows that
//!   few parallel planes `H + k·b_n` meet it, each a problem in one dimension less; this crate
//!   only calls `live3` and relies on its proof, not on Lenstra's bounds directly.
//! - M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
//!   NP-Completeness*, W. H. Freeman, 1979, ISBN 0-7167-1044-7 (a book, no DOI), Appendix,
//!   sec. A7.1 "Divisibility problems", p. 249, problem AN2, SIMULTANEOUS INCONGRUENCES, read
//!   2026-11-20 in a scan of a later printing (an "Update for the Current Printing", p. 339,
//!   lists corrections; AN2 is not among them), kept outside the repository: "INSTANCE:
//!   Collection {(a_1,b_1), ..., (a_n,b_n)} of ordered pairs of positive integers, with a_i <=
//!   b_i for 1 <= i <= n. QUESTION: Is there an integer x such that, for 1 <= i <= n, x !≡ a_i
//!   (mod b_i)? Reference: [Stockmeyer and Meyer, 1973]. Transformation from 3SAT." The
//!   appendix lists NP-complete problems, so AN2 is NP-complete, and its complement (every
//!   integer meets some `a_i mod b_i`) is co-NP-complete. Two consequences used in this crate,
//!   each proved here: (1) AN2 over a window `[l, e]` is as hard, since `x` may be taken
//!   modulo the product `P` of the `b_i`, so the window `[0, P - 1]`, whose ends have
//!   polynomially many bits, holds a solution exactly when one exists; (2) deciding that a
//!   clause of congruences holds for every `x`, the clause `x mod b_1 == a_1 || ... || x mod
//!   b_n == a_n` (with `a_i = b_i` read as residue 0), is co-NP-hard, since it holds for
//!   every `x` exactly when the AN2 instance has no solution; deciding that a clause is
//!   implied by others includes this case (no others). Used where an exact projection of
//!   congruences is given up (`presburger/extend.rs`) and where `sweep_bounded` refuses
//!   (`presburger/modular.rs`). The entry's source, L. J. Stockmeyer and A. R. Meyer, "Word
//!   problems requiring exponential time (Preliminary Report)", STOC 1973, pp. 1-9,
//!   doi:10.1145/800125.804029, read 2026-11-21 in the publisher's PDF (LibGen, kept outside
//!   the repository): Theorem 6.1, inequivalence of regular expressions over the one-letter
//!   alphabet `{0}` with union, concatenation and star is NP-complete. The hardness proof is
//!   AN2's: for a 3SAT formula with `n` variables take the first `n` primes `p_i`; `z`
//!   encodes an assignment when `z mod p_i` is 0 or 1 for every `i`; `E_0` matches the `0^z`
//!   with some `z mod p_k` in `2..p_k - 1`, and for conjunct `k` over variables `r, s, t`,
//!   `E_k = 0^{z_k} (0^{p_r p_s p_t})*`, where `z_k` (by the Chinese remainder theorem) is the
//!   residue of the one assignment of `r, s, t` that falsifies the conjunct. The formula is
//!   satisfiable exactly when some `z` lies in none of these residue classes, that is, when
//!   `E_0 ∪ E_1 ∪ ... ∪ E_m` differs from `0*`; each class is one pair `(a_i, b_i)` of AN2.
//!
//! ## Graphs and constraint networks
//!
//! - A. B. Kahn, "Topological sorting of large networks", CACM 5(11), 1962, pp. 558-562,
//!   doi:10.1145/368996.369025: repeatedly take a node with no edge into it from the nodes not
//!   yet taken ("Kahn's order"). Read 2026-11-21 in the publisher's PDF (Sci-Hub mirror; copy
//!   kept outside the repository). Sec. "Algorithm": keep for each event "a count of the
//!   number of immediate predecessors"; number the events whose count is zero, decrement
//!   their successors' counts, and repeat; when a pass finds no new zero, either every event is
//!   numbered or "there is an illegal loop in the network". Kahn scans the whole count list
//!   on each pass, so his time is the number of passes times `n`. Departure: `zed_graph::kahn`
//!   keeps the ready nodes in a list, so each node and edge is handled once, O(n + m); the
//!   order it gives is still one Kahn's rule allows, and a node left unnumbered still means a
//!   cycle. The uses name which ready node goes first (first ready, or last ready).
//! - E. W. Dijkstra, "A note on two problems in connexion with graphs", Numerische Mathematik
//!   1(1), 1959, pp. 269-271, doi:10.1007/bf01386390; R. Bellman, "On a routing problem",
//!   Quarterly of Applied Mathematics 16(1), 1958, pp. 87-90, doi:10.1090/qam/102435
//!   (Bellman-Ford, the tests' reference for difference rows). Both read 2026-11-21 in the
//!   publisher's PDFs (Sci-Hub mirrors; copies kept outside the repository). Dijkstra, Problem
//!   2: nodes join set A "in order of increasing minimum path length" from P; step 1 relaxes the
//!   branches of the node just added, step 2 moves the node of set B with least tentative
//!   distance into A. He gives no proof beyond the remark that a prefix of a shortest path is
//!   a shortest path, assumes branch lengths are not negative, and picks the least node by a
//!   scan, O(n^2); the uses keep set B in a binary heap, O(m log n), and run it on weights made
//!   non-negative by a potential (`difference_hulls` and the multi-source search near it).
//!   Bellman, sec. 3: the times `f_i` to city N satisfy `f_i = min_j (t_ij + f_j)`, `f_N = 0`;
//!   sec. 4 proves the solution unique, using `t_ij > 0`; sec. 5 iterates from `f_i = t_iN`
//!   and states that "at most (N - 1) iterations are required". The paper assumes positive
//!   times and does not treat negative cycles; the negative-cycle test the tests use is proved
//!   at `presburger::difference_rows::negative_cycle`.
//! - J. Holm, K. de Lichtenberg and M. Thorup, "Poly-logarithmic deterministic fully-dynamic
//!   algorithms for connectivity, minimum spanning tree, 2-edge, and biconnectivity", J. ACM
//!   48(4), 2001, pp. 723-760, doi:10.1145/502090.502095: named in `conjuncts` (`peel`) as the
//!   bound not taken. Read 2026-11-21 (publisher's PDF, Sci-Hub mirror; copy kept outside the
//!   repository). Theorem 23: "There exists a deterministic fully dynamic algorithm for
//!   maintaining biconnectivity in a graph, using O(log5 n) amortized time per operation."
//!   Proof sketch (sec. 7): as for 2-edge connectivity (sec. 6, O(log⁴ n)), a spanning forest
//!   is kept in O(log n) levels, an edge's level only rising, so each edge is charged O(log n)
//!   times; biconnectivity is transitive over edges, not vertices, so each nontree edge marks
//!   the triples `xyz` of its tree cycle as covered; covering a triple costs O(log³ n), which
//!   makes `Clean` and `Split` O(log³ n) against O(log² n) in 2-edge connectivity, one more
//!   factor of log n in every operation.
//!   Its queries say whether two vertices are biconnected; `peel` needs each block's conjuncts
//!   listed, which the theorem does not give.
//!
//! - R. E. Tarjan, "Depth-first search and linear graph algorithms", SIAM J. Comput. 1(2), 1972,
//!   pp. 146-160, doi:10.1137/0201010: biconnected components and strongly connected components
//!   in linear time by depth-first search with low links. Read 2026-11-21 in the publisher's
//!   PDF (LibGen; copy kept outside the repository). Sec. 3: Lemma 3 defines the biconnected
//!   components as the classes of edges under "belong to a common cycle", and states that each
//!   is a maximal biconnected subgraph and that an articulation point lies in more than one;
//!   Lemma 5: for a tree edge `(a, v)`, `a` is an articulation point when `LOWPT(v) >= a`
//!   (proved by the subtree of `v` holding every path from `v` that avoids `a`); procedure
//!   BICONNECT stacks the edges and pops a component when the test succeeds; Theorems 7 and 8
//!   give O(V + E) time and correctness. Sec. 4 does strong components with LOWLINK (Theorems
//!   13 and 14). The block-cut tree used in `presburger::local` is not in the paper; its proof
//!   is short: a cycle through blocks `B_1, c_1, ..., B_k, c_k` would make their union
//!   biconnected (each cut node `c_i` then has a second route around it), so the union would be
//!   a biconnected subgraph larger than `B_1`, against the maximality in Lemma 3 (ii).
//! - E. C. Freuder, "A sufficient condition for backtrack-free search", J. ACM 29(1), 1982,
//!   pp. 24-32, doi:10.1145/322290.322292: a tree-structured network made arc consistent is
//!   solved without backtracking in an order from the root. Read 2026-11-21 (the publisher's
//!   PDF, OpenAlex's cached copy, verification only). Theorem 1 (sec. 2): "A vertical search
//!   order is backtrack-free if the level of strong consistency is greater than the width of
//!   the corresponding ordered constraint graph"; proof: a variable checks against at most
//!   `j` earlier ones, `j` the width at its node, and `k >= j + 1` consistency gives it a
//!   value meeting any consistent choice for those `j`. Sec. 4, Theorem 3: "a constraint graph
//!   has width <= 1 iff it is a forest", a preorder (or breadth-first) order giving width 1,
//!   since each node then has only its parent before it; so "Strong 2-consistency is
//!   sufficient to guarantee the existence of a backtrack-free vertical search order for
//!   constraint problems whose constraint graphs are forests." Rooting each tree at any atom,
//!   every value left by arc consistency extends to a whole solution, which is the uses'
//!   claim. Departure: the paper's domains are finite sets; the uses keep each domain as an
//!   interval or a union of intervals and revise them exactly over the integers, which the
//!   theorem's proof does not depend on. Test: `presburger::exact::tests::
//!   certified_forests_match_enumerated_points_without_questions` compares the domains with
//!   enumerated points, which catches a value kept with no point or dropped with one; it cannot
//!   catch a graph wrongly taken for a forest on shapes it does not draw.
//! - R. Dechter, "Bucket elimination: a unifying framework for reasoning", Artificial
//!   Intelligence 113(1-2), 1999, pp. 41-85, doi:10.1016/s0004-3702(99)00059-4. S. L. Lauritzen
//!   and D. J. Spiegelhalter, "Local computations with probabilities on graphical structures and
//!   their application to expert systems", J. Royal Statistical Society B 50(2), 1988,
//!   pp. 157-194, doi:10.1111/j.2517-6161.1988.tb01721.x. Both read 2026-11-21: Dechter in
//!   OpenAlex's cached copy of the publisher's PDF, which holds only its first 10 of 45 pages,
//!   and Lauritzen and Spiegelhalter in the publisher's PDF (Sci-Hub mirror; both copies kept
//!   outside the repository). Dechter, sec. 2: bucket elimination puts each constraint in the
//!   bucket of its latest variable in an order `d` and eliminates the buckets from the last;
//!   Theorem 2, adaptive consistency costs O(n exp(w*(d))) for the induced width `w*(d)`; sec.
//!   2.3: on linear inequalities the same scheme is Fourier elimination, whose cost "is not
//!   bounded exponentially by the induced-width", since the inequalities over `i` variables
//!   are not bounded in number by a function of `i`. Lauritzen and Spiegelhalter, sec. 9.2:
//!   order the cliques of the triangulated graph with the running intersection property and
//!   marginalize the last clique's residual `R_p = C_p \ S_p` out, repeating down to `p = 1`;
//!   sec. 9.3, "recursively in the opposite direction", `p(C_i) = p(R_i | S_i) p(S_i)`: the
//!   two passes. Departures, at `presburger.rs` `projected_each`: the tree is a balanced tree
//!   of halves over the symbols' places, not a chain of cliques; the operation is existential
//!   projection over the integers, not summing probabilities, and it is exact for the same
//!   reason (an atom held by no row outside a subtree can be removed inside it), proved at the
//!   use; and as Dechter says of Fourier elimination, the rows passed are not bounded by the
//!   width, so no O(n exp(w)) bound carries over.
//! - A. Darwiche and P. Marquis, "A knowledge compilation map", J. Artificial Intelligence
//!   Research 17, 2002, pp. 229-264, doi:10.1613/jair.989, arXiv 1106.1819. Read 2026-11-21
//!   (arXiv's copy, the authors' PostScript, converted to text) for secs. 2, 4 and 5. Sec. 2,
//!   "Decomposability": "if C_1, ..., C_n are the children of and-node C, then Vars(C_i) ∩
//!   Vars(C_j) = ∅ for i != j"; DNNF is NNF with it (Definition 2.5). Sec. 4, Definition 4.1:
//!   a language satisfies CO when consistency is decided in polytime; DNNF satisfies it (Table
//!   5): an and-node of parts on disjoint variables is consistent exactly when each part is,
//!   so one bottom-up pass decides it. Sec. 5, Definition 5.6, forgetting `∃X.Σ`, and
//!   Definition 5.7 (FO); Proposition 5.1, Table 7: DNNF satisfies FO, which the appendix
//!   (proof of Proposition 5.1) takes from Darwiche 2001a. Correction: the use in
//!   `presburger/exact.rs` (the cover of a decomposable tree of blocks) said "sec. 4" for its
//!   two passes; the projection is forgetting, sec. 5, and the paper gives neither pass's
//!   details; the top-down pass (`ctx` and `esc`) and its proof are this crate's own, written
//!   at that use. Departure: the paper's leaves are literals; the uses' leaves are blocks of
//!   integer rows with exact projections.
//! - E. Cuthill and J. McKee, "Reducing the bandwidth of sparse symmetric matrices", Proc. 24th
//!   ACM National Conference, 1969, pp. 157-172, doi:10.1145/800195.805928. C. H. Papadimitriou,
//!   "The NP-completeness of the bandwidth minimization problem", Computing 16(3), 1976,
//!   pp. 263-270, doi:10.1007/bf02280884. Both read 2026-11-21 in the publisher's PDFs
//!   (Sci-Hub mirror; copies kept outside the repository). Cuthill and McKee, p. 158: number a
//!   start node 1, then its neighbors "in the order of their increasing degree", then level by
//!   level, so that each node's neighbors lie in its own level or the next or previous one;
//!   p. 159: "starting with a node of lowest degree is good strategy" but not always optimal,
//!   so their program tries every start of degree in `[D_min, D_min + (D_max - D_min)/M]` and
//!   keeps the best. They give no proof of quality; the method is a heuristic. They do not
//!   start from the node a first search reaches last: that start is from Gibbs, Poole and
//!   Stockmeyer, below. Papadimitriou, Theorem 2: the bandwidth minimization problem is
//!   NP-complete (by reduction from his Theorem 1, the linear arrangement problem LAP, itself
//!   from 3-partition; not re-derived here). The uses in `row_sums` minimize the number of rows
//!   open at once, the vertex separation of the order, not its bandwidth; it is at most the
//!   bandwidth `b` (a row numbered at most `i` with a neighbor past `i` is numbered after
//!   `i - b`), so a narrow band bounds it, but Papadimitriou's theorem is not about it.
//! - N. E. Gibbs, W. G. Poole and P. K. Stockmeyer, "An algorithm for reducing the bandwidth and
//!   profile of a sparse matrix", SIAM J. Numer. Anal. 13(2), 1976, pp. 236-250,
//!   doi:10.1137/0713023; A. George and J. W. H. Liu, "An implementation of a pseudoperipheral
//!   node finder", ACM TOMS 5(3), 1979, pp. 284-295, doi:10.1145/355841.355845. Both read
//!   2026-11-21 in the publisher's PDFs (Sci-Hub mirror; copies kept outside the repository).
//!   Gibbs, Poole and Stockmeyer, sec. 4.1, Algorithm I: from a vertex `v` of least degree,
//!   build the level structure rooted at `v`, and try the vertices of its last level ("those
//!   vertices which are farthest away from v"); if one has a deeper level structure, restart
//!   from it. George and Liu, sec. 3, give the same loop for a "pseudoperipheral node" with a
//!   shrunk last level. Departure: `presburger.rs` `by_structure` and `projected_each`'s symbol
//!   order run one search only, from the first disjunction or the least symbol, and start from
//!   a node it reaches last, without the restart loop, so the start is not always as eccentric;
//!   a chain is ordered from one end either way, since the node a search reaches last on a path
//!   is an end of the path.
//! - B. Baetz and D. R. Wood, "Brooks' vertex-colouring theorem in linear time", arXiv
//!   1401.8023, 2014. Read 2026-11-20 (the arXiv PDF): Lemma 1, colorings of the biconnected
//!   components combine in O(|V| + |E|); Lemma 2, two vertices `a`, `b` at distance 2 with
//!   `G - {a, b}` connected give a Δ-coloring by coloring `a` and `b` alike and the rest in the
//!   reverse of a search order from a common neighbor; Lemma 3, such `a`, `b` are found in
//!   linear time in a biconnected graph that is neither complete nor a cycle. Not on Crossref
//!   (no journal version found); the arXiv DOI doi:10.48550/arXiv.1401.8023 (DataCite)
//!   resolves to the listing (checked 2026-11-20).
//! - C. Berkholz, P. Bonsma and M. Grohe, "Tight lower and upper bounds for the complexity of
//!   canonical colour refinement", Theory of Computing Systems 60(4), 2017, pp. 581-614,
//!   doi:10.1007/s00224-016-9686-0, arXiv 1509.08251: sec. 3, "A fast canonical colour
//!   refinement algorithm". Crossref; the arXiv PDF read for the section's title and number.
//!   J. Cardon and M. Crochemore, "Partitioning a graph in O(|A| log2 |V|)", Theoretical
//!   Computer Science 19(1), 1982, pp. 85-98, doi:10.1016/0304-3975(82)90016-0. R. Paige and
//!   R. E. Tarjan, "Three partition refinement algorithms", SIAM J. Comput. 16(6), 1987,
//!   pp. 973-989, doi:10.1137/0216062. Both read 2026-11-21 in the publishers' PDFs (LibGen
//!   copies, kept outside the repository). Cardon and Crochemore, abstract: the aim is "the
//!   unique coarsest regular congruence ... (an equivalence ... is a regular congruence if for
//!   any vertices u and v equivalent modulo [it], then u and v have the same number of
//!   successors by each type of arc in each equivalence class)"; Theorem 1, the algorithm of
//!   their Fig. 2 computes it; Theorem 2, it runs in time `|A| (log2(|V| - #classes + 1) + 1)`,
//!   since a vertex is in a "significant" class at most `log2(|V| - #classes + 1)` times (a
//!   significant class is at most half the class it came from). Paige and Tarjan, end of
//!   sec. 3 (pp. 982-983): a partition is size-stable with respect to `S` if all elements of
//!   a block have the same number of successors in `S`; "S-Refine. Remove from L its first set
//!   S. Replace Q by s-split(S, Q). Whenever a block B in Q splits into two or more nonempty
//!   blocks, add all but the largest to the back of L"; correct because refining by all but
//!   one part of `S` gives stability with respect to the last; "an O(m log n) time bound ...
//!   follows from the observation that a given element y can be in only log2 n + 1 sets
//!   removed from L" (each set it is in after the first is at most half the one before). Used
//!   at `presburger.rs` `stable_colors`' doc (Berkholz, Bonsma and Grohe's refinement). J.
//!   Hopcroft, "An n log n
//!   algorithm for minimizing states in a finite automaton", Theory of Machines and
//!   Computations, Academic Press, 1971, pp. 189-196, doi:10.1016/b978-0-12-417750-5.50022-1,
//!   read 2026-11-21 in a scan of the chapter (LibGen, kept outside the repository). P. 190:
//!   "once we have partitioned on a block and an input symbol, we need never partition on that
//!   block and input symbol again until the block is split and then we need only partition on
//!   one of the two subblocks. Since the time needed to partition on a block is proportional to
//!   the transitions into the block and since we can always select the half with fewer
//!   transitions, the total number of steps in the algorithm is bounded by n log n." Step 7c
//!   (p. 191): after block `j` splits into `j` and `k`, for each input `a`, add `j` to the
//!   waiting list `L(a)` if `j` is not already there and has the smaller inverse image, and add
//!   `k` otherwise, so when `j` was waiting both halves end up waiting. The proof (pp. 193-194)
//!   bounds the time for one input `a` by a potential: with `a_j` the size of the inverse image
//!   of block `j`, `T = k (sum over waiting j of a_j log a_j + sum over the others of
//!   a_j log(a_j / 2))`. Splitting a block never raises `T` (for a block not waiting, the
//!   smaller part `c < b/2` is the one added), and processing a waiting block costs `k a_i`
//!   and lowers its term by exactly that, from `a_i log a_i` to `a_i log(a_i / 2)`; at the
//!   start `T <= k n log n`. Hopcroft splits in two;
//!   the uses split a class into many and wait on all but the largest, the form Paige and Tarjan
//!   and Cardon and Crochemore use.
//!
//! ## Sets, trees and persistence
//!
//! - R. E. Tarjan, "Efficiency of a good but not linear set union algorithm", J. ACM 22(2),
//!   1975, pp. 215-225, doi:10.1145/321879.321884, and R. E. Tarjan and J. van Leeuwen,
//!   "Worst-case analysis of set union algorithms", J. ACM 31(2), 1984, pp. 245-281,
//!   doi:10.1145/62.2160, both read 2026-11-21 in the publisher's PDFs (copies kept outside
//!   the repository). Tarjan 1975, abstract and Theorems 13 and 16: `m >= n` finds and `n - 1`
//!   unions with compression cost Θ(m α(m, n)). Tarjan and van Leeuwen, sec. 3, Theorem 3:
//!   linking by rank or by size with compression, splitting or halving runs in
//!   O(n + m α(m + n, n)) for any `m` and `n`. Sec. 2, Lemma 1: "If x is any node in a forest
//!   built from single nodes by a sequence of link-by-size operations, size(x) >= 2^rank(x)"
//!   (rank = height). Proof by induction on links: a node's height grows only when a root
//!   `y` of height `h` is linked under it, and then its new size is at least twice `y`'s, which
//!   is at least `2^h`. Corollary 2: no path is longer than `log n` (base 2), so, the length
//!   being an integer, at most `floor(log2 n)`; Lemma 2 gives the same for linking by rank. The
//!   use in `presburger/modular.rs` links by size without compression and relies on
//!   Corollary 2 alone.
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
//!   pp. 253-264, doi:10.1145/2935764.2935768, arXiv 1602.02120 (titled there "Parallel
//!   ordered sets using join"): union, intersection and
//!   difference of sets of sizes `m <= n` by `join` in O(m log(n/m + 1)) work. M. R. Brown and
//!   R. E. Tarjan, "A fast merging algorithm", J. ACM 26(2), 1979, pp. 211-226,
//!   doi:10.1145/322123.322127, the same bound for merging. F. K. Hwang and S. Lin, "A simple
//!   algorithm for merging two disjoint linearly ordered sets", SIAM J. Comput. 1(1), 1972,
//!   pp. 31-39, doi:10.1137/0201004. E. D. Demaine, A. López-Ortiz and J. I. Munro, "Adaptive
//!   set intersections, unions, and differences", SODA 2000, pp. 743-752,
//!   doi:10.5555/338219.338634. All four read 2026-11-21: Blelloch et al. in the arXiv LaTeX
//!   source, Brown and Tarjan and Hwang and Lin in the publishers' PDFs (copies kept outside
//!   the repository), Demaine et al. in the authors' PostScript (erikdemaine.org). Blelloch
//!   et al., sec. 4, "Main Theorem": union, intersection or difference of balanced trees of
//!   sizes `m <= n` by `join` has work O(m log(n/m + 1)) and span O(log n log m), proved in
//!   sec. 5. Brown and Tarjan, abstract: merging height-balanced trees of lengths `m <= n` "runs
//!   in O(m log(n/m)) steps, which is the same order as the lower bound on all comparison-based
//!   algorithms"; sec. 4, p. 225: with such a merge "one can sort in O(n log n) time by
//!   starting with singleton sets, and merging ordered sets in an arbitrary order until one set
//!   remains", stated there without proof. Proof: a merge of `m` into `n` keys costs
//!   O(m log((n + m)/m)) <= O(log2 C(n + m, m)); over a merge tree with `N` singleton leaves the
//!   product of these binomials is the multinomial `N! / (1! ... 1!) = N!`, so the total is
//!   O(log2 N!) = O(N log N) whatever the order (`conjuncts.rs` relies on this). Hwang and
//!   Lin, sec. 4: the generalized binary algorithm compares the last
//!   element of the shorter list with the element `2^t` places from the end of the longer
//!   (`t = floor(log2(n/m))`), dropping that block or binary-searching inside it; Theorem 1
//!   gives its worst case `(2 + t) m + p - 1` comparisons (`n = 2^t m + 2^t p + θ`), and
//!   Theorem 2 (sec. 5) puts it within `m - 1` of the information bound `log2 C(m + n, m)`.
//!   Demaine et
//!   al. measure an instance by the cost of its shortest proof of the answer; sec. 5 finds
//!   proofs by galloping (doubling then binary search from the last position) in each set,
//!   within a constant factor of that cost (Theorems 5.1 and 5.2), and sec. 6 builds the
//!   answer (Theorem 6.1: the difference of `k` sets in read-only B-trees in O(kG) time). The
//!   use, `presburger.rs` `cells_without`, gallops from the end of the last gap, which is the
//!   two-list case of Demaine et al.'s search, with Hwang and Lin's O(m log(n/m + 1)) bound.
//! - J. R. Driscoll, N. Sarnak, D. D. Sleator and R. E. Tarjan, "Making data structures
//!   persistent", J. Computer and System Sciences 38(1), 1989, pp. 86-124,
//!   doi:10.1016/0022-0000(89)90034-2. N. Sarnak and R. E. Tarjan, "Planar point location using
//!   persistent search trees", CACM 29(7), 1986, pp. 669-679, doi:10.1145/6138.6151. Both
//!   read 2026-11-21 (Driscoll et al. in a PDF from LibGen, Sarnak and Tarjan in the
//!   publisher's PDF from the Sci-Hub mirror; copies kept outside the repository). The crate's
//!   persistent maps, sets and treaps (`imbl`, `hull::rows`, `extend::images::intervals`) use
//!   path copying: an update copies the nodes on the path from the root to what it changes and
//!   shares the rest, O(log n) time and space per update in a balanced tree (expected, for a
//!   treap). Neither paper's own method is that. Sarnak and Tarjan, sec. 2, name path copying
//!   after Myers, Krijnen and Meertens, Reps, Teitelbaum and Demers, and Swart, with "an
//!   O(log m) time bound per operation and an O(log m) space bound per update", and note that
//!   it works for any balanced tree and for lists; their sec. 3, limited node copying, gets
//!   O(1) amortized space per update for sorted sets but not lists. Driscoll et al., sec. 2:
//!   the fat node method (O(1) space, O(log m) time per step) and the node-copying method for
//!   structures of bounded in-degree (O(1) amortized time and space per update step), by a
//!   potential of the live nodes' full fields; sec. 4 says path copying "requires O(log n)
//!   space and time in the worst case per insertion or deletion", a factor of log n more space
//!   than theirs. The crate pays that factor for a copy in O(1) that any version may update
//!   (full persistence) with no version stamps.
//! - O. Liljenzin, "Confluently persistent sets and maps", arXiv 1301.3388,
//!   2013, doi:10.48550/arXiv.1301.3388, read 2026-11-21 in the arXiv PDF (the author gave no
//!   LaTeX source). Treaps whose priorities are hashes of the keys, with hash-consed nodes, so
//!   that each set has one tree and equal sets are compared by address in O(1) (abstract and
//!   introduction). Union, intersection, difference and symmetric difference are Blelloch and
//!   Reid-Miller's split-and-recurse with one added exit, "if t1 is t2" (p. 6); with `n` and
//!   `m` the larger and smaller sizes, `d = |t1 ∆ t2|` and `k = min(d, m)`, the paper claims
//!   expected cost O(k log(n/k)). Its argument is a sketch: the call tree is fixed by the
//!   higher-priority operand and pruned where the other operand or the symmetric difference
//!   is empty, so "substituting S' by S'' will not change G"; no lemma bounds the pruned tree.
//!   The uses (`presburger.rs` `met_atoms` and `catalog_live`) compare this with what the code
//!   does and use none of it.
//! - D. D. Sleator and R. E. Tarjan, "A data structure for dynamic trees", J. Computer and System
//!   Sciences 26(3), 1983, pp. 362-391, doi:10.1016/0022-0000(83)90006-5 (STOC 1981,
//!   pp. 114-122); D. D. Sleator and R. E. Tarjan, "Self-adjusting binary search trees", J. ACM
//!   32(3), 1985, pp. 652-686, doi:10.1145/3828.3835. Both read 2026-11-21 in the publisher's
//!   PDFs (Sci-Hub mirror; copies kept outside the repository). The 1983 paper splits each tree
//!   into solid paths, with `expose` and `splice`; Theorems 1 and 2 bound the splices of `m`
//!   operations by `m (3 floor(lg n) + 1)` through heavy and light edges (an edge is heavy when
//!   the child holds more than half its parent's subtree; a path crosses at most `lg n` light
//!   edges); each solid path is a biased binary tree, which gives O(log n) amortized per
//!   operation, and a variant gives it in the worst case. It does not splay: the splay form,
//!   which the uses keep, is the 1985 paper's sec. 6: a "virtual tree" of solid subtrees joined
//!   by dashed edges, splayed in three passes (splay in each solid subtree, splice, splay),
//!   with the potential twice the sum of the ranks, for 12 log n + 2 amortized rotations per
//!   splay. Departures, at
//!   `presburger.rs` `CellForest`: no `evert`, and a path is ordered shallow to deep, the
//!   mirror image of the 1985 paper's.
//! - K. Mehlhorn, R. Sundar and C. Uhrig, "Maintaining dynamic sequences under equality tests in
//!   polylogarithmic time", Algorithmica 17(2), 1997, pp. 183-198, doi:10.1007/bf02522825,
//!   read 2026-11-21 in the publisher's PDF (a LibGen copy, kept outside the repository).
//!   Sec. 2, Lemma 1: for every `N` a function `f` decides from `a_{i-log*N-6} ... a_{i+4}`
//!   alone whether position `i` of a sequence over `[0..N-1]` with no two neighbors equal
//!   starts a block, such that among two adjacent positions at most one starts a block and
//!   among four adjacent ones at least one does; "no block has length exceeding 4 and ... all
//!   but the first and last block have length at least 2". Sec. 2.2 builds `f`: a six-coloring
//!   by Cole and Vishkin's deterministic coin tossing (each round, the new color is the lowest
//!   index where the old color differs from its predecessor's, followed by the bit there;
//!   Lemma 2, after Goldberg, Plotkin and Shannon), reduced to three colors by Three-Colors
//!   (Lemma 3), then "d_i = 1 iff the color of a_i ... is a local maximum in the sequence of
//!   colors" (Lemma 4: no two maxima are adjacent since neighbors differ in color; among four
//!   colors from {0, 1, 2} there is a 2 or a 0 1 0). Sec. 3: `shrink(s)` first replaces each
//!   run `a^l` by one signature (`elpow`), then each block by one signature, so the depth is
//!   O(log n); sec. 4 shows a join changes only the blocks near it, O(log* m) of them at each
//!   level in the deterministic scheme. Where the use (`presburger/deep/canon.rs`) departs:
//!   it stops at the six-coloring after four rounds, enough for 64-bit symbol numbers, and
//!   marks local maxima of the six colors, so a chunk is at most 10 symbols long (between
//!   two maxima the colors fall then rise, at most 5 steps each) rather than 4; chunks still
//!   have at least 2 symbols but the first and last, so the depth stays O(log n). Tests:
//!   `canon::tests::a_sequence_joined_anywhere_has_the_root_of_its_parse_from_scratch` (the
//!   parse does not depend on how the sequence was joined) and
//!   `canon::tests::sequences_compare_as_written_out`; neither measures chunk length or depth.
//!   A. Jeż, "Faster fully compressed pattern matching by recompression", ACM Trans.
//!   Algorithms 11(3), 2015, article 20, doi:10.1145/2631920, arXiv 1111.3244, read
//!   2026-11-21 in the arXiv LaTeX source: Theorem 1, pattern matching with both strings given
//!   as straight-line programs of sizes `n` and `m` "runs in O((n+m) log M) time" for a
//!   pattern of length `M`, assuming numbers of size `M` take constant time; sec. 2 tests
//!   equality the same way, "similar to the one of Mehlhorn et al."; sec. 1 notes that
//!   Mehlhorn, Sundar and Uhrig's method applied directly to equality of straight-line
//!   programs gives "a nearly cubic algorithm (as observed by Gawrychowski)". The use had
//!   cited Jeż's J. ACM 63(1), 2016, doi:10.1145/2743014, which is about word equations, not
//!   comparing compressed strings; T. I's paper below cites this one for that.
//!   T. I, "Longest common extensions with recompression", CPM 2017, LIPIcs 78, article 18,
//!   doi:10.4230/LIPIcs.CPM.2017.18, arXiv 1611.05359, read 2026-11-21 in the publisher's
//!   open PDF: Theorem 2, from a straight-line program of size `n` for a string of length
//!   `N`, a structure answering longest-common-extension queries in O(lg N) time is built in
//!   O(n lg(N/n)) time; it is deterministic and always correct.
//! - D. Chambi, D. Lemire, O. Kaser and R. Godin, "Better bitmap performance with Roaring
//!   bitmaps", Software: Practice and Experience 46(5), 2016, pp. 709-719, doi:10.1002/spe.2325,
//!   and D. Lemire, G. Ssi-Yan-Kai and O. Kaser, "Consistently faster and smaller compressed
//!   bitmaps with Roaring", ibid. 46(11), 2016, pp. 1547-1569, doi:10.1002/spe.2402. Both read
//!   2026-11-21 in their arXiv versions (1402.6407v10 and 1603.06549v4). The first, sec. 2:
//!   keys are split into chunks of 2^16 by their high 16 bits; "When a chunk contains no more
//!   than 4096 integers, we use a sorted array of packed 16-bit integers. When there are more
//!   than 4096 integers, we use a 2^16-bit bitmap", so no key costs more than 16 bits. The
//!   second, sec. 4, adds run containers, `2 + 4r` bytes for `r` runs, kept only where smaller
//!   than the array (`2c + 2` bytes) or the bitmap (8,192 bytes) that would hold the same
//!   keys, and made on request (`runOptimize`). Used at `presburger/row_sums.rs` `Lits`, whose
//!   runs of nonzero 64-bit words need no threshold: a run costs a step per word holding a key,
//!   at most the smaller of one per key and one per 64 keys of the range.
//! - P. M. Fenwick, "A new data structure for cumulative frequency tables", Software: Practice
//!   and Experience 24(3), 1994, pp. 327-336, doi:10.1002/spe.4380240306: node `i` covers the
//!   `i & -i` entries ending at `i`, so a prefix query or an update visits O(log n) nodes.
//!   Read 2026-11-21 in the publisher's PDF (LibGen; copy kept outside the repository), pages
//!   327-336 confirmed. Sec. "Principles": "if the index contains a '2 bit' we include two
//!   frequencies, if it has an '8 bit' we include 8 frequencies"; element 6 holds frequencies 5
//!   and 6, and a prefix sum at 11 reads `V[11] + V[10] + V[8] + V[0]`, stripping the least
//!   significant 1 bit each step (`ix AND (ix - 1)`), so at most one step per bit. The `i & -i`
//!   isolation is his, for two's complement numbers. His table counts from index 0 with a
//!   separate `V[0]`; the zed-collections type's own head comment says how it indexes.
//! - J.-P. Aumasson and D. J. Bernstein, "SipHash: a fast short-input PRF", INDOCRYPT 2012,
//!   LNCS 7668, pp. 489-508, doi:10.1007/978-3-642-34931-7_28: the standard library's default
//!   hash, named where the shared hashers of `zed_kernel::digest` replace it (`presburger.rs`
//!   `Numbered`, `colored`, the `Digest` maps): `DigestMap`, unseeded, for keys the compiler
//!   draws, and `TextMap` and `TextSet`, foldhash seeded at random, for keys that hold a
//!   program's names. (This entry once named FxHash, which the crate does not use.) Read
//!   2026-11-21 in the authors' PDF (cr.yp.to, dated 2012-09-18; copy kept outside the
//!   repository). Sec. 2: SipHash-c-d, a 128-bit key, four 64-bit words of state, `c` rounds
//!   of SipRound per 8-byte word of input and `d` at the end; sec. 3: "SipHash-c-d with c ≥ 2
//!   and d ≥ 4 is expected to provide the maximum PRF security possible", so the authors'
//!   proposal is SipHash-2-4; sec. 1 names the purpose, tables "protected against
//!   hash-flooding denial-of-service attacks". The standard library runs SipHash-1-3, fewer
//!   rounds than the paper proposes, a choice of the library and not of the paper. What the
//!   replacement keeps of it is the seed: a program cannot choose names that collide without
//!   it. The unseeded `DigestMap` relies instead on its keys being drawn by the compiler.
//!
//! ## Geometry
//!
//! - A. M. Andrew, "Another efficient algorithm for convex hulls in two dimensions", Information
//!   Processing Letters 9(5), 1979, pp. 216-219, doi:10.1016/0020-0190(79)90072-3: the monotone
//!   chain hull of sorted points in linear time. Read 2026-11-21 in the publisher's PDF
//!   (LibGen; copy kept outside the repository; the scan's text is damaged in places). Sec. 3:
//!   order the points "in terms of one of the Cartesian coordinates, say the y-coordinate",
//!   divide them by the line joining the lowest point to the highest into two chains, and run
//!   Graham's point elimination on each, so that one chain becomes each side of the hull; sec. 2:
//!   the ordering is O(n log n) and the elimination O(n), each point entering and leaving a
//!   chain at most once. Departure: the uses sort by `x` and keep the upper chain only (the
//!   textbook "monotone chain" form), or run the same elimination on lines for an upper
//!   envelope, which is the dual statement; neither changes the O(n) count after sorting.
//! - B. Chazelle and D. P. Dobkin, "Intersection of convex objects in two and three dimensions",
//!   J. ACM 34(1), 1987, pp. 1-27, doi:10.1145/7531.24036. M. I. Shamos and D. Hoey, "Geometric
//!   intersection problems", FOCS 1976, pp. 208-215, doi:10.1109/sfcs.1976.16. Chazelle and
//!   Dobkin read 2026-11-21 (the publisher's PDF, OpenAlex's cached copy) for sec. 2.3: Theorem
//!   3, "The intersection of an infinite line with a convex polygon with p vertices can be
//!   computed in O(log p) time", with Lemma 1 (the signed distance of the corners from a line
//!   is bimodal around a convex polygon) and Lemma 2 (the extrema of a bimodal sequence in
//!   O(log n) evaluations); the uses' "Theorem 3" is right, and the proof is sketched at
//!   `presburger/exact/guarded/two_pins.rs`, `clip`. Shamos and Hoey read 2026-11-21 in the
//!   publisher's PDF (Sci-Hub mirror; copy kept outside the repository; the scan's text is
//!   damaged in places), sec. V: Theorem 9, "The common intersection of N half-planes can be
//!   found in O(N log N) time, and this is optimal". The proof divides the half-planes into two
//!   halves, intersects each half recursively into a convex polygon of at most `N/2` sides, and
//!   intersects the two polygons in O(N), so `T(N) = 2 T(N/2) + O(N)`; optimality is by a
//!   reduction from sorting. Departure: `two_pins.rs` `edges` gets the same bound another way,
//!   by sorting the half-planes on the angle of the normal and keeping a double-ended queue,
//!   which the paper does not describe.
//! - G. Montúfar, R. Pascanu, K. Cho and Y. Bengio, "On the number of linear regions of deep
//!   neural networks", NIPS 2014, arXiv 1402.1869. Read 2026-11-21 (arXiv PDF, v2). Theorem 4:
//!   a rectifier network with `n0` inputs and `L` hidden layers of widths `n_i ≥ n0` computes
//!   functions with at least `(Π_{i=1}^{L-1} floor(n_i/n0)^n0) · Σ_{j=0}^{n0} C(n_L, j)` linear
//!   regions; Corollary 5, `Ω((n/n0)^((L-1)n0) n^n0)` for width `n`. Proof sketch (sec. 2 and
//!   the appendix): each of the first `L - 1` layers maps `floor(n_i/n0)^n0` regions of its
//!   input onto one common image (it folds the space), so the last layer's hyperplane
//!   arrangement, with `Σ_j C(n_L, j)` regions, is repeated in every fold. `two_pins.rs` uses it
//!   only as an example of composed piecewise linear choices with exponentially many pieces,
//!   which is why it reads each cell; it is not a bound on the guards there.
//! - T. Zaslavsky, "Facing up to arrangements: face-count formulas for partitions of space by
//!   hyperplanes", Memoirs of the AMS 1(154), 1975, doi:10.1090/memo/0154: `c` lines in the
//!   plane cut it into at most `1 + c + c(c-1)/2` regions, with equality in general position.
//!   Not read: on 2026-11-21 allpapers-locate (paperclip, arXiv, Unpaywall, OpenAlex, CORE,
//!   dblp) found no free copy, the Sci-Hub mirrors and sci.bban.top had none, LibGen's DOI
//!   index had none and its title search found two PDFs and a DjVu whose downloads failed with
//!   HTTP 503 after retries at 15 s, 45 s, 90 s and 3 min, and Anna's Archive's md5 route did
//!   not answer on .org or .se (.li served an unrelated page).
//!   The count used does not depend on the memoir: the `k`-th line crosses at most `k - 1`
//!   earlier lines at distinct points, which cut it into at most `k` pieces, each splitting
//!   one region in two, so `c` lines make at most `1 + Σ_{k≤c} k = 1 + c + c(c-1)/2` regions,
//!   with equality when no two lines are parallel and no three meet at a point.
//!
//! ## Numbers and sums
//!
//! - D. J. Bernstein, "Factoring into coprimes in essentially linear time", J. Algorithms 54(1),
//!   2005, pp. 1-30, doi:10.1016/j.jalgor.2004.04.009. Read 2026-11-20: the author's text of
//!   2004-04-04 (cr.yp.to/lineartime/dcba-20040404.pdf), whose numbering the uses follow:
//!   Algorithm 11.4, `(gcd, ppg, pple)(a, b)`; 13.2, the natural coprime base `cb{a, b}`; 16.2,
//!   `cb(P ∪ {b})` for coprime `P`; 17.3, `cb(P ∪ Q)` for coprime `P` and `Q`; 18.1, `cb S` by
//!   halving `S` and merging with 17.3; 21.2, factoring over a coprime base. The journal print
//!   was read 2026-11-21 (publisher's PDF from the Sci-Hub mirror; copy kept outside the
//!   repository): it has Algorithms 11.4, 13.2, 16.2, 17.3, 18.1 and 21.2 under the same
//!   numbers and statements, so the numbers at the uses hold for both.
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
//!   Computations, 1972, pp. 85-103, doi:10.1007/978-1-4684-2001-2_9. L. A. Levin, "Universal
//!   sequential search problems", Problems of Information Transmission 9(3), 1973 (not on
//!   Crossref), read in the English translation printed in B. A. Trakhtenbrot, "A survey of
//!   Russian approaches to perebor (brute-force search) algorithms", IEEE Annals of the History
//!   of Computing 6(4), 1984, doi:10.1109/MAHC.1984.10036. All but Bellman's book read
//!   2026-11-21 (publisher's PDFs from the Sci-Hub mirror; Koiliaris and Xu and Bringmann in
//!   their arXiv versions 1507.02318 and 1610.04712; copies kept outside the repository).
//!   Horowitz and Sahni: Algorithm 1(b), steps 1 and 2, the bound pruning (abort a partial sum
//!   the numbers left cannot raise to `M`, or the next number takes past `M`), which they call
//!   "well known"; Algorithm 2(b), the meet in the middle: all sums of each half, kept sorted,
//!   paired by one walk from opposite ends, O(max(2^(r/2), rQ)) for `Q` answers, Theorem 2
//!   proving it finds every partition. Pisinger, Proposition 3: "balsub", subset sum by
//!   dynamic programming over balanced fillings only, O(nW) for weights at most `W`. Galil and
//!   Margalit, Theorem 5.1: `m > 100 ℓ^0.5 log₂ ℓ` distinct numbers in `(0, ℓ]` make every
//!   target in `(L, S_A - L)`, `L = S_A/6 + 2ℓ^1.5`, solvable after O(ℓ log ℓ + m log² ℓ)
//!   preprocessing; sec. 3: the sums there form one interval when no small number divides
//!   almost all the numbers, and otherwise progressions of the step `d0` of Theorem 3.4. The
//!   uses had said "every sum in the middle is reached" without these conditions, and that
//!   the paper hides its constants; both are corrected at `presburger/row_sums/classes.rs`.
//!   Koiliaris and Xu, Theorem 2.7: all subset sums of `n` numbers of total σ in
//!   O(σ log σ log n), halving and one FFT sumset (Lemma 2.3, O(u log u)) per level. Bringmann,
//!   Theorem 1.1: O~(n + t), randomized with one-sided error. Karp: problem 18, KNAPSACK,
//!   "Σ a_j x_j = b has a 0-1 solution", NP-complete by reduction from EXACT COVER. Levin,
//!   Theorem 2: every search problem has an algorithm optimal up to a constant factor and an
//!   additive term; the paper does not describe it (Trakhtenbrot's survey says so), so the
//!   "universal search" by alternation with doubling allowances that `row_sums` names is the
//!   later reading, not the 1973 text.
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
