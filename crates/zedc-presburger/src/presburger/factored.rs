//! The factored products solver (row PRES-products-factored-solver, QUESTIONS A225 parts A and
//! D): which products of pairs of factor rows [`super::products`] forms, decided without
//! listing every pair of the rows on the two factors of a product. The design, with every proof,
//! is docs/studies/products-factored.md ("the design" below); the prototype it was measured on
//! is stage2.rs of b22-factored1 (/home/luke/Work/wt/proto-b22-factored1/, functions
//! `stage_a2`, `J`, `cone2`), of which this module is a port: i128 cross products and ratio
//! comparisons there are exact [`Int`] arithmetic here.
//!
//! Each product `a ⊗ b >= 0` of two linear rows `a >= 0`, `b >= 0` is read linearly, each
//! product atom `w * z` an integer atom of its own. An atom no premise, goal or definition
//! mentions is **free**: only product rows hold it.
//!
//! **Theorem D** (design sec. 2, proved there). Let L be the pairs in play and D ⊆ L. If an
//! integer vector u on the free atoms has `c_r(u) >= 0` for every pair r of L and `> 0` for
//! every r of D (`c_r(u)` the sum of r's coefficients on the free atoms times u), then the base
//! rows and L have an integer point iff the base rows and L ∖ D have one. Proof sketch: from a
//! point x of L ∖ D, `x + t u` for a large enough integer t satisfies every row (free atoms are
//! in no base row; each row of D grows by at least t). Applied repeatedly, the verdict on all
//! the pairs equals the verdict on the residual R this module returns. Dropping a pair only
//! removes a premise, so no step here can make a false proof; a wrong drop could only lose a
//! proof, which the tests check against expanding every product.
//!
//! Stage A' (design sec. 3), each step a function below:
//! 0. The start of [`solve`]: rows divided by the gcd of their coefficients, one row per
//!    class, the least constant per linear part on each side, and the 2-D cone rule ([`cone`]).
//! 1. Components with parity over rows and side nodes ([`Parity`]).
//! 2. Two frames ([`frame`]): blocks of a signed bipartite graph, its unbalanced blocks Z0,
//!    and a 2-coloring ρ of the rest.
//! 3. Three sign predicates, glob, frame+ and frame− ([`State`]); Def(r) is the variables of
//!    row r with a sign. A pair whose Def sets hold an incidence `w * z` with `w * z` free is
//!    dropped along `u_{wz} = ±σ_w σ_z` (design sec. 3, step 3, proved there).
//! 4. Pass 1 per wanted product without listing pairs ([`solve`]).
//! 5. The joint fixpoint ([`Joint`]): delta rechecks of the Def sets, the count rules P2, P3,
//!    P4, then the exact single-holder peel.
//!
//! Complexity tradeoff: the naive method lists every pair of `on[x] × on[y]` for each wanted
//! product `x * y` and expands each, Θ(Σ |a||b|) over all pairs, which is Θ(k²) for one row of k
//! factors paired with a row on each (the list main had, presburger.rs before this row). Here
//! steps 0 to 4 cost O(k log k) on the measured families except exception 1 of A225 (pass 1 on
//! the orthogonal-vectors family, design sec. 5.3), the output is |R|, and step 5 costs
//! exceptions 3 (the exact peel, Σ|a||b| over the pairs left) and 4 (the worklist on
//! `wlgrow_g`, ratio 34 at 8n, test `tests::the_worklist_of_wlgrow_g_scales`, which fails and is
//! listed under A225 in COMPLEXITY.md). Boolean matrix multiplication reduces to step 5 (design
//! sec. 5.3, test `tests::the_residual_of_the_bmm_reduction_is_the_zeros_of_a_f`), so no
//! combinatorial algorithm for step 5 beats n^3 / polylog unless that does.
//!
//! **The exact peel and its lower bound** (row PERF-factored-peel-wlisted, b22-factored3,
//! 2026-11-24). The peel lists the free atoms of each pair the count rules leave, W_listed =
//! Σ |a||b| over them, which is W_R + W_drop: the pairs left, whose products `products` then
//! writes term by term (O(|a| × |b| × log) each, presburger.rs), so W_R is output; and the pairs
//! the peel drops. On wlgrow the peel drops no pair, so its 47.20 times at 8n is the growth of
//! the output (test `tests::the_peel_on_wlgrow_is_bounded_by_its_output`). W_drop cannot be
//! brought under the input's order:
//!
//! *Claim.* Unless the orthogonal vectors hypothesis (OVH) fails, no algorithm finds the pairs the
//! single-holder rule leaves (its fixpoint, which the peel computes) in time O(N^{2−ε} + W_R)
//! for any ε > 0, N the input size (rows, side lists, mentioned atoms).
//!
//! *Proof.* OV: given u_1..u_n, v_1..v_n in {0,1}^d, is some u_a · v_b = 0? Build (test helper
//! `tests::build_ov`, O(nd)): variables w_u, z_v, s_i, t_i; rows P = Σ w_u + Σ s_i, Q = Σ z_v,
//! and for each dimension i with some v_b,i = 1, A_i = −Σ_{u_a,i = 1} w_a − s_i and B_i =
//! −Σ_{v_b,i = 1} z_b − t_i; products (P, Q) and each (A_i, B_i); mentioned atoms s_i * z_b for
//! v_b,i = 0 and t_i with each variable of A_i. So N = O(nd).
//! 1. No atom cancels: the two rows of each pair share no variable, so each incidence `x * y`,
//!    x in a, y in b, has the coefficient a_x b_y ≠ 0.
//! 2. The free atoms of (A_i, B_i) are w_a * z_b with u_a,i = v_b,i = 1, and s_i * z_b with
//!    v_b,i = 1; (P, Q) holds each of them too. So while (P, Q) is live, no atom of an (A_i,
//!    B_i) has a single holder.
//! 3. (P, Q) alone holds w_a * z_b iff no i has u_a,i = v_b,i = 1, i.e. u_a · v_b = 0; its
//!    atoms s_i * z_b are held by (A_i, B_i) too, or mentioned.
//! 4. With an orthogonal pair, (P, Q) goes; then each s_i * z_b (v_b,i = 1, which exists for
//!    every i with a pair) has the single holder (A_i, B_i), so every pair goes: W_R = 0.
//!    Without one, by 2 and 3 no atom has a single holder and the rule drops nothing.
//! 5. An algorithm of time C (N^{2−ε} + W_R), stopped after C N^{2−ε} steps, then decides OV:
//!    stopped means no orthogonal pair (W_R = 0 otherwise); finished, (P, Q) is left iff there
//!    is none. That is time O((nd)^{2−ε}), n^{2−ε} polylog n at d = c log n, which OVH rules
//!    out (OVH follows from the strong exponential time hypothesis: Williams, "A new algorithm
//!    for optimal 2-constraint satisfaction and its implications", Theor. Comput. Sci. 348(2-3),
//!    2005, DOI 10.1016/j.tcs.2005.09.023, title and DOI checked with allpapers-locate
//!    2026-11-24; the full text was not read). ∎
//!
//! Prior work (literature search of 2026-11-24, P324: paperclip semantic search and Gemini
//! web search on decremental unique coverage, peeling of degree-1 vertices and OV-hard set
//! questions; logs kept in the agent's scratch directory): the peeling methods found (the
//! peeling decoder of erasure codes, 2-cores of random hypergraphs, invertible Bloom lookup
//! tables) all take the hypergraph explicitly and run in time linear in its incidences, which
//! here is O(W_listed), what the peel costs. No method was found for an implicit hypergraph
//! whose edges are products. The nearest result has the same shape as the claim above: an
//! exact minimum degree ordering, computed over an implicit (fill) graph, needs O(n m^{1−ε})
//! time unless SETH fails, "This fine-grained reduction goes through the orthogonal vectors
//! problem" (Cummings, Fahrbach and Fatehpuria, "A Fast Minimum Degree Algorithm and Matching
//! Lower Bound", SODA 2021, DOI 10.1137/1.9781611976465.45, abstract read through paperclip
//! 2026-11-24).
//!
//! For the whole solver the sign predicates must drop nothing either when there is no
//! orthogonal pair. Under glob every w_a, z_b and s_i has both signs (+ in P or Q, − in A_i or
//! B_i), and t_i, signed, has only mentioned atoms, so no Def set pair holds a free incidence
//! [proved]; under the frames this is not proved, and the test
//! `tests::the_peel_decides_orthogonal_vectors` checks it with the whole solver on random
//! instances (both answers occur), with the control `no_peel`. The peel costs O(W_listed) =
//! O(n² d) on this family, so it is within a factor d = O(log n) of the bound (test
//! `tests::the_peel_on_orthogonal_vectors_follows_its_listed_incidences`, the output empty).
//! Exception 3 of A225 therefore stands with this reason: the peel is O(W_R + W_drop), and no
//! method makes it O(N^{2−ε} + W_R) unless OVH fails.

use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};

use zedc_int::int::Int;

use super::formula::{Atom, Con, Factor, Lin, Rel};

#[cfg(test)]
mod tests;

/// A row: its variables in increasing order, each with a nonzero coefficient.
type Row = Vec<(usize, Int)>;

/// The problem: rows over dense variable ids, their constants, the distinct side lists (rows by
/// index), the wanted products as pairs of list ids, and the partners of each variable (sorted).
pub(super) struct Prob {
    rows: Vec<Row>,
    consts: Vec<Int>,
    lists: Vec<Vec<usize>>,
    bic: Vec<(usize, usize)>,
    partners: Vec<Vec<usize>>,
}

impl Prob {
    /// Whether the atom `u * v` is mentioned. O(log d(u)).
    fn mentioned(&self, u: usize, v: usize) -> bool {
        self.partners[u].binary_search(&v).is_ok()
    }

    /// The number of atoms `u * _` mentioned.
    fn deg(&self, u: usize) -> usize {
        self.partners[u].len()
    }

    fn nv(&self) -> usize {
        self.partners.len()
    }
}

/// The pairs of `rows` (indices) whose products [`super::products`] forms: for each wanted
/// product `x * y`, the pairs of `on[x] × on[y]` left by stage A' (module doc), sorted, each
/// once as `(a, b)` with `a <= b`. A pair may stand for others: a row of a class of rows equal
/// up to a positive factor stands for its class, and a row with a weaker constant is dominated
/// (step 0); their products follow from those kept and the factor rows.
pub(super) fn kept_pairs(
    rows: &[&Lin],
    on: &BTreeMap<Factor, Vec<usize>>,
    wanted: &BTreeSet<(Factor, Factor)>,
    partners: &HashMap<Factor, Vec<Factor>>,
) -> Vec<(usize, usize)> {
    solve(&Prob::of(rows, on, wanted, partners), Opts::default()).left
}

/// How [`written`] writes the pairs of a row: the smaller of the two forms, or always direct
/// (the reference the tests compare with).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Form {
    Smaller,
    Direct,
}

/// The constraints [`super::products`] writes for the pairs `kept` of `rows` (each `(a, b)`
/// once), in the form of docs/studies/products-factored.md sec. 4 (row
/// PRES-products-shared-output, b22-factored3, 2026-11-24), and the number of auxiliary
/// variables it adds, numbered from `fresh` up. Every row is linear (its atoms factors), as
/// [`kept_pairs`] requires.
///
/// For each pair, `a` is its row with fewer terms, ties by content (`Lin`'s order: the sorted
/// terms, then the constant), so the choice depends on the rows alone. For each such `a`, with
/// partners b (the other rows of its pairs), |a| its terms and a_0 its constant:
/// - **direct**: each product `a × b ≥ 0` expanded, size Σ_b (|a||b| + aff(a, b) + 1),
///   aff(a, b) = [b_0 ≠ 0]·|a| + [a_0 ≠ 0]·|b|;
/// - **shared** (|a| ≥ 2): one variable s_{a,z} = Σ_{w∈a} a_w (w * z) per atom z of N(a), the
///   union of the partners' terms, as the equation s − Σ_w a_w (w * z) = 0 (|a| + 1 terms), and
///   each product as a_0 b_0 + a_0 Σ_z b_z z + b_0 Σ_w a_w w + Σ_z b_z s_{a,z} ≥ 0, size
///   |N(a)|·(|a| + 1) + Σ_b (|b| + aff(a, b) + 1).
///
/// The shared form is written when its size is strictly smaller (a rule on the written size,
/// with no constant); with one partner it never is (it is larger by 2|b|).
///
/// *Exactness* [proved]: expanding, a × b = a_0 b_0 + a_0 Σ_z b_z z + b_0 Σ_w a_w w +
/// Σ_z b_z Σ_w a_w (w * z), and the last sum is Σ_z b_z s_{a,z} wherever the equations hold.
/// Each s is fixed by its equation, an integer combination of integer atoms, so every point of
/// the direct system extends to exactly one point of the shared one (an integer one), and every
/// point of the shared one restricted to the old atoms is a point of the direct one. The s
/// atoms are new (numbered above every auxiliary variable of the premises, goal and
/// definitions, [`super::first_free_aux`]), so no other constraint reads them, and the two
/// systems are satisfiable together with the same formulas exactly when either is. A product
/// atom `w * z` is the same atom however its factors are ordered (`Atom::product_of`), so a
/// row sharing atoms with its partner (`(x + y)(x − y)`) is written the same way in both.
/// Test: `tests::the_shared_form_gives_the_verdicts_of_the_direct_form` (closed_rL and
/// moment_curve, both forms through `satisfiable`).
///
/// Cost: O(Σ_a (|N(a)| |a| + Σ_b (|a| + |b|)) × log) when the shared form is written, and the
/// direct form's O(Σ |a||b| × log) otherwise, each no more than the direct form; the sizes are
/// counted from term counts alone, O(Σ_a (Σ_b |b| + |N(a)| log)). Test:
/// `tests::the_written_size_of_closed_rl_scales` (sizes at n and 8n against the direct form).
pub(super) fn written(
    rows: &[&Lin],
    kept: &[(usize, usize)],
    fresh: u32,
    form: Form,
) -> (Vec<Con>, u32) {
    // The pairs of each row a, a's partners b in the order of `kept`, the rows a by content.
    let mut of: BTreeMap<(&Lin, usize), Vec<usize>> = BTreeMap::new();
    for &(i, j) in kept {
        let (a, b) = if (rows[i].terms.len(), rows[i]) <= (rows[j].terms.len(), rows[j]) {
            (i, j)
        } else {
            (j, i)
        };
        of.entry((rows[a], a)).or_default().push(b);
    }
    let mut out = BTreeSet::new();
    let mut next = fresh;
    for ((a, _), bs) in of {
        let la = a.terms.len();
        let a0 = !a.constant.is_zero();
        let aff =
            |b: &Lin| usize::from(!b.constant.is_zero()) * la + usize::from(a0) * b.terms.len();
        let direct: usize = bs
            .iter()
            .map(|&b| la * rows[b].terms.len() + aff(rows[b]) + 1)
            .sum();
        let n: BTreeSet<&Atom> = bs.iter().flat_map(|&b| rows[b].terms.keys()).collect();
        let shared: usize = n.len() * (la + 1)
            + bs.iter()
                .map(|&b| rows[b].terms.len() + aff(rows[b]) + 1)
                .sum::<usize>();
        if form == Form::Direct || la < 2 || shared >= direct {
            for &b in &bs {
                if let Some(p) = a.product(rows[b]) {
                    out.insert(Con {
                        lin: p,
                        rel: Rel::Ge,
                    });
                }
            }
            continue;
        }
        let factor = |x: &Atom| Factor::of(x).expect("a factor row is linear");
        let mut s: BTreeMap<&Atom, Atom> = BTreeMap::new();
        for z in n {
            let v = Atom::Aux(next);
            next += 1;
            let mut eq = Lin::atom(v.clone());
            for (w, c) in &a.terms {
                eq.plus_assign(&Lin::atom(Atom::product_of(factor(w), factor(z))).times(-c));
            }
            out.insert(Con {
                lin: eq,
                rel: Rel::Eq,
            });
            s.insert(z, v);
        }
        let lin_a = Lin {
            terms: a.terms.clone(),
            constant: Int::ZERO,
        };
        for &b in &bs {
            let b = rows[b];
            let mut row = Lin::constant(&a.constant * &b.constant);
            row.plus_assign(
                &Lin {
                    terms: b.terms.clone(),
                    constant: Int::ZERO,
                }
                .times(a.constant.clone()),
            );
            row.plus_assign(&lin_a.times(b.constant.clone()));
            for (z, c) in &b.terms {
                row.plus_assign(&Lin::atom(s[z].clone()).times(c.clone()));
            }
            out.insert(Con {
                lin: row,
                rel: Rel::Ge,
            });
        }
    }
    (out.into_iter().collect(), next - fresh)
}

impl Prob {
    /// The problem of [`kept_pairs`]: each factor a dense id, in the order of factors, so ids
    /// depend on the input alone.
    fn of(
        rows: &[&Lin],
        on: &BTreeMap<Factor, Vec<usize>>,
        wanted: &BTreeSet<(Factor, Factor)>,
        partners: &HashMap<Factor, Vec<Factor>>,
    ) -> Prob {
        let factor = |a: &super::formula::Atom| {
            Factor::of(a).expect("a factor row is linear: each atom a symbol or an auxiliary")
        };
        let mut all: BTreeSet<Factor> = BTreeSet::new();
        for r in rows {
            all.extend(r.terms.keys().map(factor));
        }
        for (u, vs) in partners {
            all.insert(u.clone());
            all.extend(vs.iter().cloned());
        }
        let id: HashMap<Factor, usize> = all.into_iter().enumerate().map(|(i, f)| (f, i)).collect();
        let rows_: Vec<Row> = rows
            .iter()
            .map(|r| {
                let mut v: Row = (r.terms.iter())
                    .map(|(a, c)| (id[&factor(a)], c.clone()))
                    .collect();
                v.sort_unstable_by_key(|t| t.0);
                v
            })
            .collect();
        let consts = rows.iter().map(|r| r.constant.clone()).collect();
        let mut lists = Vec::new();
        let mut list_of: HashMap<&Factor, usize> = HashMap::new();
        let mut bic = Vec::with_capacity(wanted.len());
        for (x, y) in wanted {
            let mut ids = [0; 2];
            for (i, f) in [x, y].into_iter().enumerate() {
                ids[i] = *list_of.entry(f).or_insert_with(|| {
                    lists.push(on.get(f).cloned().unwrap_or_default());
                    lists.len() - 1
                });
            }
            bic.push((ids[0], ids[1]));
        }
        let mut ps = vec![Vec::new(); id.len()];
        for (u, vs) in partners {
            let p: &mut Vec<usize> = &mut ps[id[u]];
            p.extend(vs.iter().map(|v| id[v]));
        }
        for p in &mut ps {
            zed_collections::sorted::sort_dedup(p);
        }
        Prob {
            rows: rows_,
            consts,
            lists,
            bic,
            partners: ps,
        }
    }
}

/// Switches for tests: each is a control (a mutant the tests must catch) or a choice the tests
/// show changes no result. The default is the solver.
#[derive(Default, Clone, Copy)]
struct Opts {
    /// Mutant (unsound for completeness): a variable whose frame parts conflict takes a sign.
    frame_bad: bool,
    /// Mutant: no predicate gives any variable a sign (only the count rules and the peel drop).
    no_def: bool,
    /// Step 0 without the cone rule.
    no_cone: bool,
    /// Mutant: the cone rule drops one extreme row and keeps the row after the other.
    cone_bad: bool,
    /// Pass 1 without stripping universal variables.
    no_strip: bool,
    /// Pass 1's group test: 0 by the cost estimates, 1 the walk, 2 the complement method.
    method: u8,
    /// Mutant (weaker, still sound): no exact single-holder peel after the count rules.
    no_peel: bool,
    /// Record each drop (for the replay in the tests) and the listed pairs.
    log: bool,
}

/// A drop: the pair, the rule (0, 1, 2 the worklist under glob, frame+, frame−; 9 a single
/// holder; 10, 11, 12 pass 1 under that predicate) and the signs then (worklist drops only).
type Drop = ((usize, usize), u8, Vec<i8>);

/// What [`solve`] found, with its work in steps 0 to 4 (`pass1`), the Def-set rechecks of step
/// 5 (`worklist`) and the count rules and peel (`single`).
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "`products` reads only `left`; the tests read the work, the log and the drops"
    )
)]
struct Out {
    left: Vec<(usize, usize)>,
    listed: Vec<(usize, usize)>,
    pass1: u64,
    worklist: u64,
    single: u64,
    log: Vec<Drop>,
    sig_pass1: [Vec<i8>; 3],
    /// With `log`: the pairs of the lists step 0 reduced (class representatives, the cone
    /// rule), and the pairs of the given lists not among them.
    step0: Vec<(usize, usize)>,
    dominated: Vec<(usize, usize)>,
}

/// Union-find with union by rank and the parity of each node to its parent (step 1). A path's
/// parity is the xor of its edges', so path compression keeps each node's parity to the root
/// by xoring the parities along the path. O(α(n)) amortized a step (Tarjan and van Leeuwen,
/// "Worst-case analysis of set union algorithms", J. ACM 31(2), 1984, doi:10.1145/62.2160,
/// cited at `products`' union-find; the parity is a label carried along, which changes no
/// step's count). zed-graph's `UnionFind` keeps no label on an edge, so it is not reused.
struct Parity {
    up: Vec<usize>,
    rank: Vec<u8>,
    par: Vec<u8>,
}

impl Parity {
    fn new(n: usize) -> Parity {
        Parity {
            up: (0..n).collect(),
            rank: vec![0; n],
            par: vec![0; n],
        }
    }

    /// The root of `x` and the parity of `x` to it.
    fn find(&mut self, x: usize) -> (usize, u8) {
        let mut path = Vec::new();
        let mut y = x;
        while self.up[y] != y {
            path.push(y);
            y = self.up[y];
        }
        let mut acc = 0;
        for &z in path.iter().rev() {
            acc ^= self.par[z];
            self.par[z] = acc;
            self.up[z] = y;
        }
        (y, if path.is_empty() { 0 } else { self.par[x] })
    }

    /// Joins `a` and `b` with parity(a) xor parity(b) = d; false on a conflict.
    fn union(&mut self, a: usize, b: usize, d: u8) -> bool {
        let ((ra, pa), (rb, pb)) = (self.find(a), self.find(b));
        if ra == rb {
            return pa ^ pb == d;
        }
        let (hi, lo) = if self.rank[ra] >= self.rank[rb] {
            (ra, rb)
        } else {
            (rb, ra)
        };
        self.up[lo] = hi;
        self.par[lo] = pa ^ pb ^ d;
        if self.rank[ra] == self.rank[rb] {
            self.rank[hi] += 1;
        }
        true
    }
}

/// A frame of step 2: each row's component and parity (`flip`, 0 for frame+), whether it is
/// left out (`excl`: a row of an odd component under frame−), and each component's part and
/// color ρ.
struct Frame {
    comp: Vec<usize>,
    flip: Vec<u8>,
    excl: Vec<bool>,
    part: Vec<usize>,
    rho: Vec<i8>,
}

/// Step 2: the frame of the live rows. H is the bipartite multigraph between components and
/// variables, one edge (comp(r), w) of sign sgn(r_w) xor flip(r) per live row r not left out
/// and w in r. Its blocks are found by Tarjan's depth-first search with an edge stack (Tarjan,
/// "Depth-first search and linear graph algorithms", SIAM J. Comput. 1(2):146-160, 1972,
/// doi:10.1137/0201010; iterative here, the parent skipped by edge id since H is a multigraph);
/// a block is unbalanced when a 2-coloring by edge signs fails (Harary, "On the notion of
/// balance of a signed graph", Michigan Math. J. 2(2):143-146, 1953, doi:10.1307/mmj/1028989917:
/// a signed graph is balanced iff its nodes 2-color with negative edges between the colors).
/// Z0 is the variables of unbalanced blocks; the parts are the connected pieces of H − Z0, and
/// ρ colors each part's components so that every edge's sign times σ_w is ρ. H − Z0 is balanced
/// (design sec. 3, step 2, proved: a cycle of H − Z0 lies in one block and holds a variable
/// outside Z0, so that block is balanced), so the coloring is consistent; checked in debug
/// builds. O(|H|) = O(Σ |r|).
#[expect(
    clippy::too_many_arguments,
    reason = "the frame reads each of the step-1 results; a struct for one call would only rename them"
)]
fn frame(
    rows: &[Row],
    nv: usize,
    live_row: &[bool],
    comp_of: &[usize],
    ncomp: usize,
    flip: Vec<u8>,
    excl: Vec<bool>,
    work: &mut u64,
) -> Frame {
    let nn = ncomp + nv;
    let mut edges: Vec<(usize, usize, u8)> = Vec::new();
    for (r, row) in rows.iter().enumerate() {
        if !live_row[r] || excl[r] {
            continue;
        }
        for (v, c) in row {
            edges.push((comp_of[r], ncomp + v, u8::from(c.is_negative()) ^ flip[r]));
        }
    }
    *work += edges.len() as u64;
    let mut adj: Vec<Vec<(usize, usize)>> = vec![Vec::new(); nn];
    for (e, &(u, v, _)) in edges.iter().enumerate() {
        adj[u].push((v, e));
        adj[v].push((u, e));
    }
    let mut disc = vec![usize::MAX; nn];
    let mut low = vec![0usize; nn];
    let mut t = 0usize;
    let mut estack: Vec<usize> = Vec::new();
    let mut z0 = vec![false; nv];
    let mut stack: Vec<(usize, usize, usize)> = Vec::new();
    let check_block = |blk: &[usize], z0: &mut [bool], work: &mut u64| {
        let mut col: HashMap<usize, u8> = HashMap::new();
        let mut badj: HashMap<usize, Vec<(usize, u8)>> = HashMap::new();
        for &e in blk {
            let (u, v, s) = edges[e];
            badj.entry(u).or_default().push((v, s));
            badj.entry(v).or_default().push((u, s));
        }
        *work += 2 * blk.len() as u64;
        let mut balanced = true;
        let start = edges[blk[0]].0;
        col.insert(start, 0);
        let mut q = vec![start];
        while let Some(u) = q.pop() {
            let cu = col[&u];
            for &(v, s) in &badj[&u] {
                match col.get(&v) {
                    Some(&cv) => balanced &= cv == cu ^ s,
                    None => {
                        col.insert(v, cu ^ s);
                        q.push(v);
                    }
                }
            }
        }
        if !balanced {
            for &e in blk {
                z0[edges[e].1 - ncomp] = true;
            }
        }
    };
    for s in 0..nn {
        if disc[s] != usize::MAX || adj[s].is_empty() {
            continue;
        }
        disc[s] = t;
        low[s] = t;
        t += 1;
        stack.push((s, usize::MAX, 0));
        while let Some(&mut (v, pe, ref mut i)) = stack.last_mut() {
            if *i < adj[v].len() {
                let (w, e) = adj[v][*i];
                *i += 1;
                *work += 1;
                if e == pe {
                    continue;
                }
                if disc[w] == usize::MAX {
                    estack.push(e);
                    disc[w] = t;
                    low[w] = t;
                    t += 1;
                    stack.push((w, e, 0));
                } else if disc[w] < disc[v] {
                    estack.push(e);
                    low[v] = low[v].min(disc[w]);
                }
            } else {
                stack.pop();
                if let Some(&(u, _, _)) = stack.last() {
                    low[u] = low[u].min(low[v]);
                    if low[v] >= disc[u] {
                        let mut blk = Vec::new();
                        while let Some(e) = estack.pop() {
                            blk.push(e);
                            if e == pe {
                                break;
                            }
                        }
                        check_block(&blk, &mut z0, work);
                    }
                }
            }
        }
    }
    let mut part = vec![usize::MAX; ncomp];
    let mut rho = vec![1i8; ncomp];
    let mut np = 0;
    let mut vsign = vec![0i8; nv];
    for c0 in 0..ncomp {
        if part[c0] != usize::MAX {
            continue;
        }
        part[c0] = np;
        let mut q = vec![c0];
        while let Some(c) = q.pop() {
            for &(vn, e) in &adj[c] {
                *work += 1;
                let v = vn - ncomp;
                if z0[v] {
                    continue;
                }
                let s = if edges[e].2 == 1 { -rho[c] } else { rho[c] };
                if vsign[v] == 0 {
                    vsign[v] = s;
                    for &(c2, e2) in &adj[vn] {
                        *work += 1;
                        if part[c2] == usize::MAX {
                            part[c2] = np;
                            rho[c2] = if edges[e2].2 == 1 { -s } else { s };
                            q.push(c2);
                        }
                    }
                }
            }
        }
        np += 1;
    }
    debug_assert!(
        edges.iter().all(|&(c, vn, s)| {
            let v = vn - ncomp;
            z0[v] || vsign[v] == if s == 1 { -rho[c] } else { rho[c] }
        }),
        "H − Z0 is balanced (design sec. 3, step 2), so ρ colors it consistently"
    );
    Frame {
        comp: comp_of.to_vec(),
        flip,
        excl,
        part,
        rho,
    }
}

/// The sign counts of each variable over the live rows (step 3): its holders of each sign, and
/// for each frame the holders in each part by the side of ρ they give (a row of an odd
/// component counts on both sides, under a key of its own).
struct State {
    pos: Vec<u32>,
    neg: Vec<u32>,
    parts: [Vec<HashMap<usize, (u32, u32)>>; 2],
}

impl State {
    fn new(nv: usize) -> State {
        State {
            pos: vec![0; nv],
            neg: vec![0; nv],
            parts: [vec![HashMap::new(); nv], vec![HashMap::new(); nv]],
        }
    }

    /// Adds row `r` (`up`) or takes it away. O(|r|).
    fn add(&mut self, fr: &[Frame; 2], r: usize, row: &Row, up: bool) {
        let step = |x: &mut u32| {
            if up {
                *x += 1;
            } else {
                *x -= 1;
            }
        };
        for (v, k) in row {
            let (v, neg) = (*v, k.is_negative());
            step(if neg {
                &mut self.neg[v]
            } else {
                &mut self.pos[v]
            });
            for (fi, f) in fr.iter().enumerate() {
                let c = f.comp[r];
                let (key, both, on) = if f.excl[r] {
                    (usize::MAX, true, 0)
                } else {
                    let on = (f.rho[c] < 0) ^ neg ^ (f.flip[r] == 1);
                    (f.part[c], false, u8::from(on))
                };
                let e = self.parts[fi][v].entry(key).or_insert((0, 0));
                if both || on == 0 {
                    step(&mut e.0);
                }
                if both || on == 1 {
                    step(&mut e.1);
                }
                if *e == (0, 0) {
                    self.parts[fi][v].remove(&key);
                }
            }
        }
    }

    fn sig_glob(&self, v: usize) -> i8 {
        match (self.pos[v] > 0, self.neg[v] > 0) {
            (true, false) => 1,
            (false, true) => -1,
            _ => 0,
        }
    }

    fn sig_frame(&self, fi: usize, v: usize, o: &Opts) -> i8 {
        let m = &self.parts[fi][v];
        if o.frame_bad {
            return match m.iter().min_by_key(|e| e.1.0) {
                Some((_, &(a, _))) => {
                    if a > 0 {
                        1
                    } else {
                        -1
                    }
                }
                None => 0,
            };
        }
        let mut it = m.values();
        match (it.next(), it.next()) {
            (Some(&(a, b)), None) => match (a > 0, b > 0) {
                (true, false) => 1,
                (false, true) => -1,
                _ => 0,
            },
            _ => 0,
        }
    }

    /// σ_v under predicate `kind`: 0 glob, 1 frame+, 2 frame−.
    fn sig(&self, o: &Opts, kind: usize, v: usize) -> i8 {
        if o.no_def {
            return 0;
        }
        match kind {
            0 => self.sig_glob(v),
            1 => self.sig_frame(0, v, o),
            _ => self.sig_frame(1, v, o),
        }
    }
}

/// One side list in pass 1: its rows by their three Def set ids, and per predicate the
/// distinct sets (groups), the nonempty ones by key, and the empty one if present.
struct Side {
    by_rkey: BTreeMap<[usize; 3], Vec<usize>>,
    by_kind: [BTreeMap<usize, Vec<[usize; 3]>>; 3],
    groups: [Vec<usize>; 3],
    by_key: [HashMap<usize, Vec<usize>>; 3],
    empty: [Option<usize>; 3],
}

/// Interned variable sets (sorted), each with its key (the member with the fewest partners,
/// ties by the least id: a cost choice only), F_S memoized, and the all-mentioned test
/// memoized per unordered pair of set ids. Equal sets have equal ids: the id is that of the
/// exact sorted list, no hash value stands for a set (design sec. 3, "Set identity").
struct Sets<'a> {
    p: &'a Prob,
    intern: HashMap<Vec<usize>, usize>,
    sets: Vec<Vec<usize>>,
    key: Vec<Option<usize>>,
    f: HashMap<usize, HashSet<usize>>,
    closed: HashMap<(usize, usize), bool>,
    work: u64,
}

impl Sets<'_> {
    fn id(&mut self, s: Vec<usize>) -> usize {
        self.work += s.len() as u64 + 1;
        if let Some(&i) = self.intern.get(&s) {
            return i;
        }
        let n = self.sets.len();
        self.key
            .push(s.iter().copied().min_by_key(|&w| (self.p.deg(w), w)));
        self.sets.push(s.clone());
        self.intern.insert(s, n);
        n
    }

    /// F_S = {z : w * z mentioned for every w of S}, from the partners of key(S).
    fn fset(&mut self, s: usize) {
        if self.f.contains_key(&s) {
            return;
        }
        let Some(w0) = self.key[s] else {
            self.f.insert(s, HashSet::new());
            return;
        };
        let mut h = HashSet::new();
        for &z in &self.p.partners[w0] {
            self.work += 1;
            let mut all = true;
            for &w in &self.sets[s] {
                self.work += 1;
                if !self.p.mentioned(w, z) {
                    all = false;
                    break;
                }
            }
            if all {
                h.insert(z);
            }
        }
        self.f.insert(s, h);
    }

    /// Every atom of S × T mentioned, by |S||T| lookups at most, memoized.
    fn direct(&mut self, s: usize, t: usize) -> bool {
        let key = (s.min(t), s.max(t));
        self.work += 1;
        if let Some(&b) = self.closed.get(&key) {
            return b;
        }
        let mut r = true;
        'o: for &w in &self.sets[s] {
            for &z in &self.sets[t] {
                self.work += 1;
                if !self.p.mentioned(w, z) {
                    r = false;
                    break 'o;
                }
            }
        }
        self.closed.insert(key, r);
        r
    }

    /// Every atom of S × T mentioned: the smaller set inside F of the larger. Memoized with
    /// [`Sets::direct`].
    fn all_mentioned(&mut self, s: usize, t: usize) -> bool {
        let key = (s.min(t), s.max(t));
        self.work += 1;
        if let Some(&b) = self.closed.get(&key) {
            return b;
        }
        let (a, b) = if self.sets[s].len() <= self.sets[t].len() {
            (t, s)
        } else {
            (s, t)
        };
        self.fset(a);
        let fs = &self.f[&a];
        let r = self.sets[b].iter().all(|z| fs.contains(z));
        self.work += self.sets[b].len() as u64;
        self.closed.insert(key, r);
        r
    }
}

/// Relevance for step 5 (design sec. 3, step 5). A listed pair joins rows of one component: in
/// an even component a row of parity p only with rows of parity 1 − p, in an odd one with any
/// row of it. w is relevant iff some row r holding w can be paired with a row holding a z with
/// `w * z` not mentioned. An irrelevant w never makes an incidence free, so it is left out of
/// the Def sets. Each w has the budget 2 d(w) + 2 lookups, past which it counts as relevant
/// (safe: that only adds tests), so the whole costs O(k log k) for the sorts.
fn relevant(
    p: &Prob,
    comp_of: &[usize],
    parity: &[u8],
    excl: &[bool],
    work: &mut u64,
) -> Vec<bool> {
    let mut rel = vec![false; p.nv()];
    let key = |r: usize| (comp_of[r], if excl[r] { 2 } else { parity[r] });
    let mut uni: BTreeMap<(usize, u8), Vec<usize>> = BTreeMap::new();
    let mut wk: Vec<(usize, (usize, u8))> = Vec::new();
    for (r, row) in p.rows.iter().enumerate() {
        if comp_of[r] == usize::MAX {
            continue;
        }
        for &(v, _) in row {
            *work += 1;
            uni.entry(key(r)).or_default().push(v);
            wk.push((v, key(r)));
        }
    }
    for u in uni.values_mut() {
        *work += u.len() as u64;
        zed_collections::sorted::sort_dedup(u);
    }
    *work += wk.len() as u64;
    zed_collections::sorted::sort_dedup(&mut wk);
    let mut budget: Vec<usize> = (0..p.nv()).map(|w| 2 * p.deg(w) + 2).collect();
    for (w, (c, par)) in wk {
        *work += 1;
        if rel[w] {
            continue;
        }
        let opp = if par == 2 { 2 } else { 1 - par };
        let Some(u) = uni.get(&(c, opp)) else {
            continue;
        };
        if p.deg(w) < u.len() || budget[w] < u.len() {
            rel[w] = true;
            continue;
        }
        budget[w] -= u.len();
        rel[w] = u.iter().any(|&z| {
            *work += 1;
            !p.mentioned(w, z)
        });
    }
    rel
}

/// Stage A' (module doc).
fn solve(p: &Prob, o: Opts) -> Out {
    let nr = p.rows.len();
    let nv = p.nv();
    let rows = &p.rows;
    let mut work1: u64 = rows.iter().map(|r| r.len() as u64 + 1).sum();
    // Step 0. g: the gcd of each row's coefficients (1 for a row with none); the normalized
    // linear part's id; the constant c/g as a reduced fraction (denominator > 0).
    let g: Vec<Int> = (rows.iter())
        .map(|r| {
            let g = r.iter().fold(Int::ZERO, |a, (_, c)| a.gcd(c));
            if g.is_zero() { Int::ONE } else { g }
        })
        .collect();
    let mut lin_id: HashMap<Vec<(usize, Int)>, usize> = HashMap::new();
    let lid: Vec<usize> = (0..nr)
        .map(|r| {
            let n = lin_id.len();
            let l = rows[r]
                .iter()
                .map(|(v, c)| (*v, c.div_floor(&g[r])))
                .collect();
            *lin_id.entry(l).or_insert(n)
        })
        .collect();
    let cq: Vec<(Int, Int)> = (0..nr)
        .map(|r| {
            let q = p.consts[r].gcd(&g[r]);
            (p.consts[r].div_floor(&q), g[r].div_floor(&q))
        })
        .collect();
    // One row per class (equal normalized part and constant): the least g stands for it, so
    // the choice depends on content only (ties by the least g are rows equal outright).
    let mut rep: HashMap<(usize, &(Int, Int)), usize> = HashMap::new();
    for r in 0..nr {
        let e = rep.entry((lid[r], &cq[r])).or_insert(r);
        if g[r] < g[*e] {
            *e = r;
        }
    }
    let canon: Vec<usize> = (0..nr).map(|r| rep[&(lid[r], &cq[r])]).collect();
    // c_a / g_a < c_b / g_b, exactly (both denominators positive).
    let less = |a: usize, b: usize| &cq[a].0 * &cq[b].1 < &cq[b].0 * &cq[a].1;
    let side = |s: &[usize], work: &mut u64| -> Vec<usize> {
        let mut best: BTreeMap<usize, usize> = BTreeMap::new();
        for &r in s {
            let r = canon[r];
            *work += 1;
            let e = best.entry(lid[r]).or_insert(r);
            if less(r, *e) {
                *e = r;
            }
        }
        let mut v: Vec<usize> = best.into_values().collect();
        v.sort_unstable();
        if o.no_cone {
            v
        } else {
            cone(v, p, o.cone_bad, work)
        }
    };
    // Equal lists are reduced once.
    let mut raw_id: HashMap<&[usize], usize> = HashMap::new();
    let mut raw: Vec<Vec<usize>> = Vec::new();
    let mut rb: Vec<(usize, usize)> = Vec::with_capacity(p.bic.len());
    for &(a, b) in &p.bic {
        work1 += 1;
        let mut ids = [0usize; 2];
        for (i, s) in [&p.lists[a], &p.lists[b]].into_iter().enumerate() {
            let n = raw.len();
            let id = *raw_id.entry(&s[..]).or_insert(n);
            if id == n {
                raw.push(side(s, &mut work1));
            }
            ids[i] = id;
        }
        rb.push((ids[0], ids[1]));
    }
    let (step0, dominated) = if o.log {
        let all = expand_pairs(
            p.bic
                .iter()
                .map(|&(a, b)| (&p.lists[a][..], &p.lists[b][..])),
        );
        let kept = expand_pairs(rb.iter().map(|&(a, b)| (&raw[a][..], &raw[b][..])));
        let set: BTreeSet<(usize, usize)> = kept.iter().copied().collect();
        let dominated = all.into_iter().filter(|e| !set.contains(e)).collect();
        (kept, dominated)
    } else {
        (Vec::new(), Vec::new())
    };
    // A product with an empty side forms no pair; equal reduced lists are one side node.
    let mut side_id: BTreeMap<&[usize], usize> = BTreeMap::new();
    let mut sides: Vec<&[usize]> = Vec::new();
    let mut raw_side: Vec<Option<usize>> = vec![None; raw.len()];
    let mut bset: BTreeSet<(usize, usize)> = BTreeSet::new();
    for &(ra, rb_) in &rb {
        work1 += 1;
        if raw[ra].is_empty() || raw[rb_].is_empty() {
            continue;
        }
        let mut node = |x: usize, work1: &mut u64| {
            *raw_side[x].get_or_insert_with(|| {
                *work1 += raw[x].len() as u64 + 1;
                let n = sides.len();
                let id = *side_id.entry(&raw[x][..]).or_insert(n);
                if id == n {
                    sides.push(&raw[x]);
                }
                id
            })
        };
        let (x, y) = (node(ra, &mut work1), node(rb_, &mut work1));
        bset.insert((x.min(y), x.max(y)));
    }
    let bic: Vec<(usize, usize)> = bset.into_iter().collect();
    let ns = sides.len();
    // Step 1. Components with parity: rows 0..nr, side nodes nr..nr+ns.
    let mut uf = Parity::new(nr + ns);
    let mut live_row = vec![false; nr];
    let mut conflicts = Vec::new();
    for (s, rs) in sides.iter().enumerate() {
        for &r in *rs {
            live_row[r] = true;
            if !uf.union(r, nr + s, 0) {
                conflicts.push(r);
            }
        }
    }
    for &(x, y) in &bic {
        work1 += 1;
        if !uf.union(nr + x, nr + y, 1) {
            conflicts.push(nr + x);
        }
    }
    let odd: HashSet<usize> = conflicts.iter().map(|&x| uf.find(x).0).collect();
    let mut cidx: BTreeMap<usize, usize> = BTreeMap::new();
    let mut comp_of = vec![usize::MAX; nr];
    let mut parity = vec![0u8; nr];
    let mut excl = vec![false; nr];
    for r in 0..nr {
        if live_row[r] {
            let (root, pr) = uf.find(r);
            let n = cidx.len();
            comp_of[r] = *cidx.entry(root).or_insert(n);
            parity[r] = pr;
            excl[r] = odd.contains(&root);
        }
    }
    work1 += nr as u64;
    let ncomp = cidx.len();
    // Step 2.
    let fr = [
        frame(
            rows,
            nv,
            &live_row,
            &comp_of,
            ncomp,
            vec![0; nr],
            vec![false; nr],
            &mut work1,
        ),
        frame(
            rows,
            nv,
            &live_row,
            &comp_of,
            ncomp,
            parity.clone(),
            excl.clone(),
            &mut work1,
        ),
    ];
    // Step 3.
    let mut st = State::new(nv);
    for r in 0..nr {
        if live_row[r] {
            st.add(&fr, r, &rows[r], true);
        }
    }
    let sig_pass1 = if o.log {
        [0, 1, 2].map(|kind| (0..nv).map(|v| st.sig(&o, kind, v)).collect())
    } else {
        Default::default()
    };
    // Step 4.
    let mut sets = Sets {
        p,
        intern: HashMap::new(),
        sets: Vec::new(),
        key: Vec::new(),
        f: HashMap::new(),
        closed: HashMap::new(),
        work: 0,
    };
    let mut rkey = vec![[0usize; 3]; nr];
    let mut supp = vec![0usize; nr];
    for r in 0..nr {
        if !live_row[r] {
            continue;
        }
        for (kind, k) in rkey[r].iter_mut().enumerate() {
            let def = rows[r]
                .iter()
                .map(|t| t.0)
                .filter(|&v| st.sig(&o, kind, v) != 0);
            *k = sets.id(def.collect());
        }
        supp[r] = sets.id(rows[r].iter().map(|t| t.0).collect());
    }
    let mut six: Vec<Side> = Vec::with_capacity(ns);
    for s in &sides {
        let mut d = Side {
            by_rkey: BTreeMap::new(),
            by_kind: Default::default(),
            groups: Default::default(),
            by_key: Default::default(),
            empty: [None; 3],
        };
        for &r in *s {
            work1 += 1;
            d.by_rkey.entry(rkey[r]).or_default().push(r);
        }
        for k in d.by_rkey.keys() {
            for kind in 0..3 {
                work1 += 1;
                d.by_kind[kind].entry(k[kind]).or_default().push(*k);
            }
        }
        for kind in 0..3 {
            for &t in d.by_kind[kind].keys() {
                d.groups[kind].push(t);
                match sets.key[t] {
                    Some(z) => d.by_key[kind].entry(z).or_default().push(t),
                    None => d.empty[kind] = Some(t),
                }
            }
        }
        six.push(d);
    }
    let tsize: Vec<[usize; 3]> = (six.iter())
        .map(|d| [0, 1, 2].map(|k| d.groups[k].iter().map(|&t| sets.sets[t].len()).sum()))
        .collect();
    work1 += (six.iter())
        .map(|d| d.groups.iter().map(Vec::len).sum::<usize>() as u64)
        .sum::<u64>();
    let mut kx: HashMap<(usize, usize, usize), Vec<usize>> = HashMap::new();
    // Per side and predicate: the universe U (the union of the groups) and Σ_{w∈U} d(w).
    let uinfo: Vec<[(Vec<usize>, usize); 3]> = (six.iter())
        .map(|d| {
            [0, 1, 2].map(|k| {
                let u: BTreeSet<usize> = (d.groups[k].iter())
                    .flat_map(|&g| sets.sets[g].iter().copied())
                    .collect();
                let dsum = u.iter().map(|&w| p.deg(w)).sum();
                (u.into_iter().collect(), dsum)
            })
        })
        .collect();
    work1 += tsize
        .iter()
        .map(|t| t.iter().sum::<usize>() as u64)
        .sum::<u64>();
    let mut listed: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut log = Vec::new();
    for &(sa, sb) in &bic {
        let sd = [sa, sb];
        let mut surv: [HashSet<(usize, usize)>; 3] = Default::default();
        let mut stripped = [false; 3];
        let mut strip: [[HashMap<usize, usize>; 2]; 3] = Default::default();
        let mut all: [[HashSet<usize>; 2]; 3] = Default::default();
        let mut inv: [[BTreeMap<usize, Vec<usize>>; 2]; 3] = Default::default();
        for kind in 0..3 {
            for i in 0..2 {
                if let Some(e) = six[sd[i]].empty[kind] {
                    all[kind][i].insert(e);
                }
            }
            let gflip = six[sa].groups[kind].len() > six[sb].groups[kind].len();
            let (x, y) = if gflip { (sb, sa) } else { (sa, sb) };
            work1 += 1;
            // Complexity tradeoff: the plain walk costs about est_plain, stripping about
            // est_strip (design sec. 3, step 4, "Estimates"); the smaller runs. Either alone
            // is superlinear on a family the other handles in O(k log k) (design sec. 5.2).
            let est_plain: usize = (six[x].groups[kind].iter())
                .filter_map(|&g| {
                    let w = sets.key[g]?;
                    Some(sets.sets[g].len() * p.deg(w).min(tsize[y][kind]))
                })
                .sum::<usize>()
                + six[x].groups[kind].len();
            work1 += six[x].groups[kind].len() as u64;
            let (ua, ub) = (&uinfo[sa][kind], &uinfo[sb][kind]);
            let prod = ua.0.len() * ub.0.len();
            let est_strip = tsize[sa][kind]
                + tsize[sb][kind]
                + ua.1.min(prod)
                + ub.1.min(prod)
                + six[sa].groups[kind].len()
                + six[sb].groups[kind].len();
            stripped[kind] = !o.no_strip && (o.method != 0 || est_strip < est_plain);
            if !stripped[kind] {
                // The plain walk over the side with fewer groups: when the other side's
                // groups are no larger in total than d(key S), each T is tested directly
                // (Gemini's guard); otherwise the candidates are the T whose key is a partner
                // of key(S), the partners cut once per (key, side, predicate) to the other
                // side's keys (Claude's key cut).
                let orient = |g: usize, t: usize| if gflip { (t, g) } else { (g, t) };
                for gi in 0..six[x].groups[kind].len() {
                    let g = six[x].groups[kind][gi];
                    work1 += 1;
                    let Some(w0) = sets.key[g] else {
                        continue;
                    };
                    if tsize[y][kind] <= p.deg(w0) {
                        for &t in &six[y].groups[kind] {
                            if sets.key[t].is_some() && sets.direct(g, t) {
                                surv[kind].insert(orient(g, t));
                            }
                        }
                        continue;
                    }
                    let cut = kx.entry((w0, y, kind)).or_insert_with(|| {
                        let mut v = Vec::new();
                        for &z in &p.partners[w0] {
                            work1 += 1;
                            if six[y].by_key[kind].contains_key(&z) {
                                v.push(z);
                            }
                        }
                        v
                    });
                    for &z in cut.iter() {
                        work1 += 1;
                        for &t in &six[y].by_key[kind][&z] {
                            if sets.direct(g, t) {
                                surv[kind].insert(orient(g, t));
                            }
                        }
                    }
                }
                continue;
            }
            // H_i: the variables of U_i not mentioned with every variable of the other
            // universe; one with fewer partners than |U_other| is in H at once, otherwise the
            // lookups stop at the first unmentioned atom.
            let mut h: [HashSet<usize>; 2] = Default::default();
            for i in 0..2 {
                let (ui, uo) = (&uinfo[sd[i]][kind].0, &uinfo[sd[1 - i]][kind].0);
                for &w in ui {
                    work1 += 1;
                    let universal = p.deg(w) >= uo.len()
                        && uo.iter().all(|&z| {
                            work1 += 1;
                            p.mentioned(w, z)
                        });
                    if !universal {
                        h[i].insert(w);
                    }
                }
            }
            all[kind] = Default::default();
            for i in 0..2 {
                for &g in &six[sd[i]].groups[kind] {
                    let v: Vec<usize> = (sets.sets[g].iter().copied())
                        .filter(|w| h[i].contains(w))
                        .collect();
                    let s = sets.id(v);
                    strip[kind][i].insert(g, s);
                    inv[kind][i].entry(s).or_default().push(g);
                    if sets.sets[s].is_empty() {
                        all[kind][i].insert(s);
                    }
                }
            }
            let ne = |i: usize| -> Vec<usize> {
                (inv[kind][i].keys().copied())
                    .filter(|s| !all[kind][i].contains(s))
                    .collect()
            };
            let (g0, g1) = (ne(0), ne(1));
            let flip = g0.len() > g1.len();
            let (gx, gy, hx, hy) = if flip {
                (g1, g0, &h[1], &h[0])
            } else {
                (g0, g1, &h[0], &h[1])
            };
            let orient = |g: usize, t: usize| if flip { (t, g) } else { (g, t) };
            if gx.is_empty() || gy.is_empty() {
                continue;
            }
            let key_of = |sets: &Sets, s: usize| sets.key[s].expect("a nonempty set has a key");
            let ty: usize = gy.iter().map(|&t| sets.sets[t].len()).sum();
            let est_walk: usize = (gx.iter())
                .map(|&g| sets.sets[g].len() * p.deg(key_of(&sets, g)).min(ty))
                .sum::<usize>()
                + ty;
            // The complement's cost: Free(w) for w in H_x, Miss for each T, and at most
            // |gx||gy| candidate checks, plus Σ_S Σ_{w∈S} |Free(w)| known once Free is built,
            // when the choice is made again; a wrong first guess costs the walk's estimate
            // once more at most.
            let est_comp = hx.len() * hy.len() + gy.len() * hy.len() + gx.len() * gy.len();
            work1 += (gx.len() + gy.len()) as u64;
            let mut comp = match o.method {
                1 => false,
                2 => true,
                _ => est_comp < est_walk,
            };
            let mut hyv: Vec<usize> = hy.iter().copied().collect();
            hyv.sort_unstable();
            let mut free: HashMap<usize, Vec<usize>> = HashMap::new();
            if comp {
                for &w in hx {
                    let f: Vec<usize> = (hyv.iter().copied())
                        .filter(|&z| {
                            work1 += 1;
                            !p.mentioned(w, z)
                        })
                        .collect();
                    free.insert(w, f);
                }
                if o.method == 0 {
                    let fsum: usize = (gx.iter())
                        .map(|&g| sets.sets[g].iter().map(|w| free[w].len()).sum::<usize>())
                        .sum();
                    work1 += gx.iter().map(|&g| sets.sets[g].len() as u64).sum::<u64>();
                    comp = est_comp + fsum < est_walk;
                }
            }
            if comp {
                // The complement method (Claude F4): Free(w) = H_y minus the partners of w,
                // Miss(z) the groups T lacking z; S survives with T iff T ∩ Free(S) = ∅.
                let mut miss: HashMap<usize, Vec<usize>> = HashMap::new();
                let mut tset: HashMap<usize, HashSet<usize>> = HashMap::new();
                for &t in &gy {
                    let ts: HashSet<usize> = sets.sets[t].iter().copied().collect();
                    for &z in &hyv {
                        work1 += 1;
                        if !ts.contains(&z) {
                            miss.entry(z).or_default().push(t);
                        }
                    }
                    tset.insert(t, ts);
                }
                for &g in &gx {
                    let mut fs: BTreeSet<usize> = BTreeSet::new();
                    for w in &sets.sets[g] {
                        work1 += 1 + free[w].len() as u64;
                        fs.extend(free[w].iter().copied());
                    }
                    let Some(&z0) = fs
                        .iter()
                        .min_by_key(|z| (miss.get(z).map_or(0, Vec::len), **z))
                    else {
                        for &t in &gy {
                            work1 += 1;
                            surv[kind].insert(orient(g, t));
                        }
                        continue;
                    };
                    for &t in miss.get(&z0).map_or(&[][..], |v| &v[..]) {
                        work1 += 1;
                        if fs.iter().all(|z| {
                            work1 += 1;
                            !tset[&t].contains(z)
                        }) {
                            surv[kind].insert(orient(g, t));
                        }
                    }
                }
            } else {
                // The walk on the stripped groups, with the keys of this product.
                let mut by_key: HashMap<usize, Vec<usize>> = HashMap::new();
                for &t in &gy {
                    by_key.entry(key_of(&sets, t)).or_default().push(t);
                }
                let mut kl: HashMap<usize, Vec<usize>> = HashMap::new();
                for &g in &gx {
                    work1 += 1;
                    let w0 = key_of(&sets, g);
                    if ty <= p.deg(w0) {
                        for &t in &gy {
                            if sets.direct(g, t) {
                                surv[kind].insert(orient(g, t));
                            }
                        }
                        continue;
                    }
                    let cut = kl.entry(w0).or_insert_with(|| {
                        let mut v = Vec::new();
                        for &z in &p.partners[w0] {
                            work1 += 1;
                            if by_key.contains_key(&z) {
                                v.push(z);
                            }
                        }
                        v
                    });
                    for &z in cut.iter() {
                        work1 += 1;
                        for &t in &by_key[&z] {
                            if sets.direct(g, t) {
                                surv[kind].insert(orient(g, t));
                            }
                        }
                    }
                }
            }
        }
        // A pair of groups survives predicate k iff a stripped side is empty or the stripped
        // pair survived; a pair of rows is listed iff its groups survive all three.
        let sid = |k: usize, i: usize, g: usize| if stripped[k] { strip[k][i][&g] } else { g };
        let ok = |k: usize, ga: usize, gb: usize| {
            let (x, y) = (sid(k, 0, ga), sid(k, 1, gb));
            all[k][0].contains(&x) || all[k][1].contains(&y) || surv[k].contains(&(x, y))
        };
        let keys = |k: usize, i: usize| -> Vec<usize> {
            if stripped[k] {
                inv[k][i].keys().copied().collect()
            } else {
                six[sd[i]].groups[k].clone()
            }
        };
        let nkeys = |k: usize, i: usize| {
            if stripped[k] {
                inv[k][i].len()
            } else {
                six[sd[i]].groups[k].len()
            }
        };
        let cnt = |k: usize| {
            surv[k].len() + all[k][0].len() * nkeys(k, 1) + nkeys(k, 0) * all[k][1].len()
        };
        let dk = (0..3).min_by_key(|&k| cnt(k)).unwrap_or(0);
        let mut sv: BTreeSet<(usize, usize)> = surv[dk].iter().copied().collect();
        if !all[dk][0].is_empty() {
            let ys = keys(dk, 1);
            for &x in &all[dk][0] {
                sv.extend(ys.iter().map(|&y| (x, y)));
            }
        }
        if !all[dk][1].is_empty() {
            let xs = keys(dk, 0);
            for &y in &all[dk][1] {
                sv.extend(xs.iter().map(|&x| (x, y)));
            }
        }
        work1 += sv.len() as u64;
        for (x, y) in sv {
            let (xs, ys) = if stripped[dk] {
                (inv[dk][0][&x].clone(), inv[dk][1][&y].clone())
            } else {
                (vec![x], vec![y])
            };
            for &s in &xs {
                for &t in &ys {
                    let (Some(al), Some(bl)) =
                        (six[sa].by_kind[dk].get(&s), six[sb].by_kind[dk].get(&t))
                    else {
                        continue;
                    };
                    for ak in al {
                        for bk in bl {
                            work1 += 1;
                            if !(0..3).all(|k| ok(k, ak[k], bk[k])) {
                                continue;
                            }
                            for &x in &six[sa].by_rkey[ak] {
                                for &y in &six[sb].by_rkey[bk] {
                                    work1 += 1;
                                    listed.insert((x.min(y), x.max(y)));
                                }
                            }
                        }
                    }
                }
            }
        }
        if o.log {
            for (ak, ar) in &six[sa].by_rkey {
                for (bk, br) in &six[sb].by_rkey {
                    if let Some(k) = (0..3).find(|&k| !ok(k, ak[k], bk[k])) {
                        for &x in ar {
                            for &y in br {
                                log.push(((x.min(y), x.max(y)), 10 + k as u8, Vec::new()));
                            }
                        }
                    }
                }
            }
        }
    }
    // A listed pair whose supports have every atom mentioned is closed: kept, in no live list.
    let mut open: Vec<(usize, usize)> = Vec::new();
    let mut closed: Vec<(usize, usize)> = Vec::new();
    for &(a, b) in &listed {
        if sets.all_mentioned(supp[a], supp[b]) {
            closed.push((a, b));
        } else {
            open.push((a, b));
        }
    }
    work1 += sets.work;
    let np = open.len();
    let rel = relevant(p, &comp_of, &parity, &excl, &mut work1);
    let mut j = Joint::new(p, &fr, o, st, open, rel);
    for r in 0..nr {
        if live_row[r] && j.opp[r].is_empty() {
            j.kill(r, false);
        }
    }
    j.run();
    log.append(&mut j.log);
    let mut left: Vec<(usize, usize)> = (0..np)
        .filter(|&e| j.live[e])
        .map(|e| j.pairs[e])
        .chain(closed.iter().copied())
        .collect();
    left.sort_unstable();
    Out {
        left,
        listed: if o.log {
            listed.into_iter().collect()
        } else {
            Vec::new()
        },
        pass1: work1,
        worklist: j.work,
        single: j.work3,
        log,
        sig_pass1,
        step0,
        dominated,
    }
}

/// Every pair of the lists, each once as (min, max) (the naive listing: tests and logs only).
fn expand_pairs<'a>(bic: impl Iterator<Item = (&'a [usize], &'a [usize])>) -> Vec<(usize, usize)> {
    let mut s = BTreeSet::new();
    for (a, b) in bic {
        for &x in a {
            for &y in b {
                s.insert((x.min(y), x.max(y)));
            }
        }
    }
    s.into_iter().collect()
}

/// The joint fixpoint of step 5 on the open listed pairs (design sec. 3, step 5).
struct Joint<'a> {
    p: &'a Prob,
    fr: &'a [Frame; 2],
    o: Opts,
    st: State,
    pairs: Vec<(usize, usize)>,
    live: Vec<bool>,
    /// The live pairs of each row as (other row, pair), removed by swap; `pos[e]` the place of
    /// pair e in each of its rows' lists.
    opp: Vec<Vec<(usize, usize)>>,
    pos: Vec<[usize; 2]>,
    holders: Vec<Vec<usize>>,
    /// Def sets per predicate and row (relevant variables only), in insertion order (`dl`) for
    /// the delta test, and their exact identity: the root of a hash-consed binary trie over
    /// variable ids, a node keyed by the exact triple (height, left, right), node 0 the empty
    /// set and node 1 the full leaf. Equal ids mean equal sets.
    dset: [Vec<BTreeSet<usize>>; 3],
    dl: [Vec<Vec<usize>>; 3],
    root: [Vec<u32>; 3],
    tn: Vec<(u32, u32)>,
    tid: HashMap<(u8, u32, u32), u32>,
    th: u8,
    rel: Vec<bool>,
    /// Per open pair and predicate: the prefix lengths of dl(a), dl(b) already tested.
    tested: Vec<[(usize, usize); 3]>,
    memo: HashMap<(u32, u32), bool>,
    dirty: VecDeque<(usize, usize)>,
    isdirty: [Vec<bool>; 3],
    // The count rules P2, P3, P4.
    sum: Vec<usize>,
    heap: Vec<BinaryHeap<(usize, usize)>>,
    hcount: Vec<usize>,
    min_m: Vec<Option<usize>>,
    uniq: Vec<Option<usize>>,
    queue: VecDeque<usize>,
    queued: Vec<bool>,
    p3q: VecDeque<usize>,
    over: Vec<usize>,
    cand: Vec<BinaryHeap<(usize, usize)>>,
    vqueue: VecDeque<usize>,
    vqueued: Vec<bool>,
    // The exact peel.
    expanded: bool,
    pair_atoms: Vec<Vec<usize>>,
    count: Vec<usize>,
    aholders: Vec<Vec<usize>>,
    aq: Vec<usize>,
    work: u64,
    work3: u64,
    log: Vec<Drop>,
}

impl<'a> Joint<'a> {
    fn new(
        p: &'a Prob,
        fr: &'a [Frame; 2],
        o: Opts,
        st: State,
        pairs: Vec<(usize, usize)>,
        rel: Vec<bool>,
    ) -> Joint<'a> {
        let rows = &p.rows;
        let (nr, nv, np) = (rows.len(), p.nv(), pairs.len());
        let mut j = Joint {
            p,
            fr,
            o,
            st,
            live: vec![true; np],
            opp: vec![Vec::new(); nr],
            pos: vec![[0; 2]; np],
            holders: vec![Vec::new(); nv],
            dset: std::array::from_fn(|_| vec![BTreeSet::new(); nr]),
            dl: std::array::from_fn(|_| vec![Vec::new(); nr]),
            root: std::array::from_fn(|_| vec![0; nr]),
            tn: vec![(0, 0), (1, 1)],
            tid: HashMap::new(),
            th: u8::try_from(usize::BITS - nv.max(1).leading_zeros())
                .expect("a bit count fits in u8"),
            rel,
            tested: vec![[(0, 0); 3]; np],
            memo: HashMap::new(),
            dirty: VecDeque::new(),
            isdirty: std::array::from_fn(|_| vec![false; nr]),
            sum: vec![0; nr],
            heap: vec![BinaryHeap::new(); nr],
            hcount: vec![0; nv],
            min_m: vec![None; nr],
            uniq: vec![None; nr],
            queue: VecDeque::new(),
            queued: vec![false; nr],
            p3q: VecDeque::new(),
            over: vec![0; nv],
            cand: vec![BinaryHeap::new(); nv],
            vqueue: VecDeque::new(),
            vqueued: vec![false; nv],
            expanded: false,
            pair_atoms: Vec::new(),
            count: Vec::new(),
            aholders: Vec::new(),
            aq: Vec::new(),
            work: 0,
            work3: 0,
            log: Vec::new(),
            pairs,
        };
        let len = |r: usize| rows[r].len();
        for e in 0..np {
            let (a, b) = j.pairs[e];
            j.work += 1;
            let ends = if a == b { 1 } else { 2 };
            for (side, (r, other)) in [(a, b), (b, a)].into_iter().enumerate().take(ends) {
                j.pos[e][side] = j.opp[r].len();
                j.opp[r].push((other, e));
                j.sum[r] += len(other);
                j.heap[r].push((len(other), e));
            }
        }
        for r in 0..nr {
            j.work += 1;
            if j.opp[r].is_empty() {
                continue;
            }
            for &(v, _) in &rows[r] {
                j.work += 1;
                j.holders[v].push(r);
                j.hcount[v] += 1;
                for kind in 0..3 {
                    if j.rel[v] && j.st.sig(&o, kind, v) != 0 && j.dset[kind][r].insert(v) {
                        j.dl[kind][r].push(v);
                        j.root[kind][r] = j.tput(j.root[kind][r], j.th, v, true);
                    }
                }
            }
        }
        for v in 0..nv {
            j.work3 += 1;
            if j.hcount[v] == 1 {
                let r = j.holders[v][0];
                j.unique(r, v);
            }
        }
        // P4 without its gate: O(W4 log), W4 = Σ over open listed pairs of min(|a|, |b|).
        for (r, row) in rows.iter().enumerate() {
            for &(v, _) in row {
                j.work3 += 1;
                j.over[v] += j.sum[r];
            }
        }
        for e in 0..np {
            let (a, b) = j.pairs[e];
            if a == b {
                continue;
            }
            for (q, pp) in [(a, b), (b, a)] {
                if len(q) > len(pp) {
                    continue;
                }
                for &(w, _) in &rows[q] {
                    j.work3 += 1;
                    if rows[pp].binary_search_by_key(&w, |x| x.0).is_err() {
                        j.cand[w].push((len(pp), e));
                    }
                }
            }
        }
        for v in 0..nv {
            j.wake_var(v);
        }
        j
    }

    fn sig(&self, kind: usize, v: usize) -> i8 {
        self.st.sig(&self.o, kind, v)
    }

    fn mark(&mut self, r: usize, kind: usize) {
        if !self.isdirty[kind][r] {
            self.isdirty[kind][r] = true;
            self.dirty.push_back((r, kind));
        }
    }

    /// Row r leaves the live rows: its sign counts drop, and a variable that gains a sign adds
    /// itself to the Def sets of its live holders, which become dirty. Live holders only
    /// shrink, so a sign is never lost or flipped at a live holder (design sec. 3, step 3,
    /// "Monotonicity", proved); checked in debug builds. With `peel`, the holder counts of the
    /// count rules drop too.
    fn kill(&mut self, r: usize, peel: bool) {
        let rows = &self.p.rows;
        let row = &rows[r];
        let old: Vec<(usize, [i8; 3])> = (row.iter())
            .map(|&(v, _)| (v, [self.sig(0, v), self.sig(1, v), self.sig(2, v)]))
            .collect();
        self.st.add(self.fr, r, row, false);
        for (v, s0) in old {
            self.work += 1;
            let s1 = [self.sig(0, v), self.sig(1, v), self.sig(2, v)];
            if s1 == s0 {
                continue;
            }
            for i in 0..self.holders[v].len() {
                let r2 = self.holders[v][i];
                self.work += 1;
                if self.opp[r2].is_empty() || !self.rel[v] {
                    continue;
                }
                for kind in 0..3 {
                    if s1[kind] == s0[kind] {
                        continue;
                    }
                    if self.o.frame_bad && s1[kind] == 0 {
                        // The mutant only: a sign lost, after which the delta record is reset.
                        if self.dset[kind][r2].remove(&v) {
                            self.dl[kind][r2].retain(|&x| x != v);
                            self.root[kind][r2] = self.tput(self.root[kind][r2], self.th, v, false);
                            for i in 0..self.opp[r2].len() {
                                let e = self.opp[r2][i].1;
                                self.tested[e][kind] = (0, 0);
                            }
                        }
                        continue;
                    }
                    debug_assert!(
                        self.o.frame_bad || (s0[kind] == 0 && s1[kind] != 0),
                        "a sign is never lost or flipped at a live holder (design sec. 3)"
                    );
                    if self.dset[kind][r2].insert(v) {
                        self.dl[kind][r2].push(v);
                        self.root[kind][r2] = self.tput(self.root[kind][r2], self.th, v, true);
                        self.mark(r2, kind);
                    }
                }
            }
        }
        if peel {
            for &(v, _) in &rows[r] {
                self.work3 += 1;
                self.hcount[v] -= 1;
                if self.hcount[v] == 1 {
                    let holder = (self.holders[v].iter().copied()).find(|&h| {
                        self.work3 += 1;
                        !self.opp[h].is_empty()
                    });
                    if let Some(s) = holder {
                        self.unique(s, v);
                    }
                }
            }
        }
    }

    /// The trie node at height `h` equal to `node` with `v` put in (`add`) or taken out. O(h).
    fn tput(&mut self, node: u32, h: u8, v: usize, add: bool) -> u32 {
        self.work += 1;
        if h == 0 {
            return u32::from(add);
        }
        let (l, r) = if node == 0 {
            (0, 0)
        } else {
            self.tn[node as usize]
        };
        let (l, r) = if (v >> (h - 1)) & 1 == 0 {
            (self.tput(l, h - 1, v, add), r)
        } else {
            (l, self.tput(r, h - 1, v, add))
        };
        if l == 0 && r == 0 {
            return 0;
        }
        if let Some(&id) = self.tid.get(&(h, l, r)) {
            return id;
        }
        let id = u32::try_from(self.tn.len()).expect("trie nodes fit in u32");
        self.tn.push((l, r));
        self.tid.insert((h, l, r), id);
        id
    }

    /// Def(a) × Def(b) holds an incidence whose atom is free. Memoized per exact set ids; for
    /// an open pair e (live, so every incidence tested before had its atom mentioned), only the
    /// incidences new since its last test are tested: (new a × all b) and (old a × new b),
    /// cost (la − pa) lb + pa (lb − pb).
    fn has_free(&mut self, kind: usize, a: usize, b: usize, e: usize) -> bool {
        let (ga, gb) = (self.root[kind][a], self.root[kind][b]);
        let key = (ga.min(gb), ga.max(gb));
        self.work += 1;
        let (la, lb) = (self.dl[kind][a].len(), self.dl[kind][b].len());
        let now = if self.pairs[e].0 == a {
            (la, lb)
        } else {
            (lb, la)
        };
        if let Some(&h) = self.memo.get(&key) {
            if !h {
                self.tested[e][kind] = now;
            }
            return h;
        }
        let (pa, pb) = if self.pairs[e].0 == a {
            self.tested[e][kind]
        } else {
            let t = self.tested[e][kind];
            (t.1, t.0)
        };
        let p = self.p;
        let any_free = |xs: &[usize], ys: &[usize], work: &mut u64| {
            xs.iter().any(|&x| {
                ys.iter().any(|&y| {
                    *work += 1;
                    !p.mentioned(x, y)
                })
            })
        };
        let (da, db) = (&self.dl[kind][a], &self.dl[kind][b]);
        let mut h = la > pa && any_free(&da[pa..], db, &mut self.work);
        if !h && lb > pb {
            h = any_free(&da[..pa], &db[pb..], &mut self.work);
        }
        self.tested[e][kind] = now;
        self.memo.insert(key, h);
        h
    }

    fn remove(&mut self, e: usize) {
        if !self.live[e] {
            return;
        }
        self.live[e] = false;
        let rows = &self.p.rows;
        let (a, b) = self.pairs[e];
        let ends = if a == b { 1 } else { 2 };
        for (side, (r, other)) in [(a, b), (b, a)].into_iter().enumerate().take(ends) {
            let i = self.pos[e][side];
            self.opp[r].swap_remove(i);
            if let Some(&(_, moved)) = self.opp[r].get(i) {
                let s = usize::from(self.pairs[moved].0 != r);
                self.pos[moved][s] = i;
            }
            let (lo, lr) = (rows[other].len(), rows[r].len());
            self.sum[r] -= lo;
            self.work3 += 1;
            if lo >= lr {
                for &(v, _) in &rows[r] {
                    self.work3 += 1;
                    self.over[v] -= lo;
                    self.wake_var(v);
                }
            }
            if self.opp[r].is_empty() {
                self.kill(r, true);
            } else {
                self.wake(r);
            }
        }
        if self.expanded {
            for i in 0..self.pair_atoms[e].len() {
                let t = self.pair_atoms[e][i];
                self.work3 += 1;
                self.count[t] -= 1;
                if self.count[t] == 1 {
                    self.aq.push(t);
                }
            }
        }
    }

    fn drop_pair(&mut self, e: usize, rule: u8) {
        if self.o.log {
            let s = if rule < 3 {
                (0..self.p.nv()).map(|x| self.sig(rule.into(), x)).collect()
            } else {
                Vec::new()
            };
            self.log.push((self.pairs[e], rule, s));
        }
        self.remove(e);
    }

    fn wake(&mut self, r: usize) {
        if self.min_m[r].is_some() && !self.queued[r] {
            self.queued[r] = true;
            self.queue.push_back(r);
        }
    }

    fn wake_var(&mut self, v: usize) {
        if !self.cand[v].is_empty() && !self.vqueued[v] {
            self.vqueued[v] = true;
            self.vqueue.push_back(v);
        }
    }

    /// Row r is the one live row holding v.
    fn unique(&mut self, r: usize, v: usize) {
        let m = self.p.deg(v);
        self.min_m[r] = Some(self.min_m[r].map_or(m, |x| x.min(m)));
        if self.uniq[r].is_none() {
            self.p3q.push_back(r);
        }
        self.uniq[r] = Some(self.uniq[r].map_or(v, |u| u.min(v)));
        self.wake(r);
    }

    /// The recheck of a dirty row: each live pair once.
    fn recheck(&mut self, r: usize, kind: usize) {
        self.isdirty[kind][r] = false;
        self.work += 1;
        if self.opp[r].is_empty() || self.dset[kind][r].is_empty() {
            return;
        }
        let es = self.opp[r].clone();
        self.work += es.len() as u64;
        for (b, e) in es {
            if !self.live[e] || self.dset[kind][b].is_empty() {
                continue;
            }
            if self.has_free(kind, r, b, e) {
                self.drop_pair(e, u8::try_from(kind).expect("three predicates"));
            }
        }
    }

    /// P3: w held only by r and z only by b (among rows with a live pair), `w * z` free. The
    /// pair {r, b} is then the only one holding `w * z`, with the coefficient r_w b_z ≠ 0
    /// (r_z = b_w = 0 when r ≠ b; when r = b, z = w), so it is a single holder.
    fn p3(&mut self, r: usize) {
        let Some(w) = self.uniq[r] else {
            return;
        };
        let es = self.opp[r].clone();
        self.work3 += es.len() as u64 + 1;
        for (b, e) in es {
            if !self.live[e] {
                continue;
            }
            if let Some(z) = self.uniq[b]
                && (b != r || z == w)
                && !self.p.mentioned(w, z)
            {
                self.drop_pair(e, 9);
            }
        }
    }

    /// P2: r alone holds w, m the atoms `w * _` mentioned. The pair {r, q} holds the |q| atoms
    /// `w * z`, z in q, each with the coefficient r_w q_z ≠ 0 (no other row holds w). Another
    /// live pair holds one of them only as {r, s} with z in s: at most `sum[r]` − |q| of them;
    /// at most m are mentioned. So when 2|q| > m + `sum[r]`, some `w * z` is free and held by
    /// {r, q} alone, and the pair goes by the single-holder rule (Theorem D, u = ±e).
    fn p2(&mut self, r: usize) {
        self.queued[r] = false;
        let Some(m) = self.min_m[r] else {
            return;
        };
        while let Some(&(len, id)) = self.heap[r].peek() {
            self.work3 += 1;
            if !self.live[id] {
                self.heap[r].pop();
            } else if 2 * len > m + self.sum[r] {
                self.heap[r].pop();
                self.drop_pair(id, 9);
            } else {
                break;
            }
        }
    }

    /// P4: P2 for a w held by several rows. `over[w]` bounds from above the incidences (pair,
    /// atom `w * z`) of the live pairs on rows holding w (it is decreased only when the other
    /// row is no shorter, so it may stay larger: that only keeps pairs); a candidate {q, p}
    /// has w in q, w not in p, so it holds the |p| atoms `w * z`, z in p, with the coefficient
    /// q_w p_z ≠ 0, and the argument of P2 applies with `over[w]` for `sum[r]`.
    fn p4(&mut self, w: usize) {
        self.vqueued[w] = false;
        let m = self.p.deg(w);
        while let Some(&(len, id)) = self.cand[w].peek() {
            self.work3 += 1;
            if !self.live[id] {
                self.cand[w].pop();
            } else if 2 * len > m + self.over[w] {
                self.cand[w].pop();
                self.drop_pair(id, 9);
            } else {
                break;
            }
        }
    }

    /// The exact peel's start: the free atoms of every live pair, Σ |a||b| over them
    /// (exception 3 of A225).
    fn expand(&mut self) {
        self.expanded = true;
        let np = self.pairs.len();
        self.pair_atoms = vec![Vec::new(); np];
        let mut aid: HashMap<(usize, usize), usize> = HashMap::new();
        for e in 0..np {
            if !self.live[e] {
                continue;
            }
            let (a, b) = self.pairs[e];
            self.work3 += (self.p.rows[a].len() * self.p.rows[b].len()) as u64;
            for t in free_atoms(self.p, a, b).into_keys() {
                let n = aid.len();
                let id = *aid.entry(t).or_insert(n);
                if id == n {
                    self.count.push(0);
                    self.aholders.push(Vec::new());
                }
                self.count[id] += 1;
                self.aholders[id].push(e);
                self.pair_atoms[e].push(id);
            }
        }
        self.aq = (0..self.count.len())
            .filter(|&t| self.count[t] == 1)
            .collect();
        self.aq.reverse();
    }

    fn peel_atom(&mut self, t: usize) {
        self.work3 += 1;
        if self.count[t] != 1 {
            return;
        }
        let holder = (self.aholders[t].iter().copied()).find(|&e| {
            self.work3 += 1;
            self.live[e]
        });
        if let Some(e) = holder {
            self.drop_pair(e, 9);
        }
    }

    /// The joint fixpoint: Def-set rechecks first, then P3, P2, P4, then the exact peel; any
    /// drop can wake any of them. The rules are monotone, so the pairs left do not depend on
    /// the order (design sec. 3, "Monotonicity and unique fixpoint", proved).
    fn run(&mut self) {
        loop {
            if let Some((r, kind)) = self.dirty.pop_front() {
                self.recheck(r, kind);
            } else if let Some(r) = self.p3q.pop_front() {
                self.p3(r);
            } else if let Some(r) = self.queue.pop_front() {
                self.p2(r);
            } else if let Some(v) = self.vqueue.pop_front() {
                self.p4(v);
            } else if !self.expanded && !self.o.no_peel {
                self.expand();
            } else if let Some(t) = self.aq.pop() {
                self.peel_atom(t);
            } else {
                break;
            }
        }
    }
}

/// The free atoms of the product of rows a and b with their nonzero coefficients, sorted.
fn free_atoms(p: &Prob, a: usize, b: usize) -> BTreeMap<(usize, usize), Int> {
    let mut prod: BTreeMap<(usize, usize), Int> = BTreeMap::new();
    for (u, cu) in &p.rows[a] {
        for (v, cv) in &p.rows[b] {
            let e = prod
                .entry(((*u).min(*v), (*u).max(*v)))
                .or_insert(Int::ZERO);
            *e = &*e + &(cu * cv);
        }
    }
    prod.retain(|&(u, v), c| !c.is_zero() && !p.mentioned(u, v));
    prod
}

/// The 2-D cone rule of step 0 (design sec. 3, step 0, proved there). On one side list, the
/// rows whose homogenized vector (coefficients and constant) has exactly two nonzero
/// coordinates are grouped by those two. When a group of n >= 3 rows fits in an open
/// half-plane (exactly one circular gap between neighbors by angle has a negative cross
/// product), each row strictly between the two extreme directions is λ_1 e_1 + λ_2 e_2 with
/// λ_i >= 0 rational (Cramer's rule), so by bilinearity its product with any row b is λ_1 (e_1
/// ⊗ b) + λ_2 (e_2 ⊗ b), and its pairs are dropped. Other groups are left as they are. Cross
/// products are exact [`Int`] products (the prototype's i128 could overflow on wide
/// coefficients). O(r log r) a group of r rows, for the sort. Tests:
/// `tests::the_cone_rule_keeps_the_verdict_on_lists_shared_by_products` (with the mutant
/// `cone_bad` as control).
fn cone(v: Vec<usize>, p: &Prob, bad: bool, work: &mut u64) -> Vec<usize> {
    type Dir<'a> = (&'a Int, &'a Int, usize);
    let mut planes: BTreeMap<(usize, usize), Vec<Dir>> = BTreeMap::new();
    let mut out = Vec::new();
    for r in v {
        let row = &p.rows[r];
        *work += row.len() as u64 + 1;
        let c = &p.consts[r];
        match (&row[..], c.is_zero()) {
            ([(x, a), (y, b)], true) => planes.entry((*x, *y)).or_default().push((a, b, r)),
            ([(x, a)], false) => planes.entry((*x, usize::MAX)).or_default().push((a, c, r)),
            _ => out.push(r),
        }
    }
    let cross = |a: &Dir, b: &Dir| &(a.0 * b.1) - &(a.1 * b.0);
    // The upper half-plane (with the positive first axis) first, then the lower.
    let half = |a: &Dir| !(a.1.is_positive() || (a.1.is_zero() && a.0.is_positive()));
    for (_, mut vs) in planes {
        let n = vs.len();
        *work += n as u64 * (u64::from(usize::BITS - n.leading_zeros()) + 1);
        vs.sort_by(|a, b| {
            (half(a).cmp(&half(b)))
                .then_with(|| Int::ZERO.cmp(&cross(a, b)))
                .then(a.2.cmp(&b.2))
        });
        let gaps: Vec<usize> = (0..n)
            .filter(|&i| n > 1 && cross(&vs[i], &vs[(i + 1) % n]).is_negative())
            .collect();
        if let [i] = gaps[..]
            && n >= 3
        {
            let (first, last) = ((i + 1) % n, i);
            for (j, x) in vs.iter().enumerate() {
                let keep = if bad {
                    j == first || j == (first + 1) % n
                } else {
                    j == first || j == last
                };
                if keep {
                    out.push(x.2);
                }
            }
        } else {
            out.extend(vs.iter().map(|x| x.2));
        }
    }
    out.sort_unstable();
    out
}
