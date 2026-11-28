//! A sound test that rows of at most two variables each (TVPI rows, `a·x + b·y + k >= 0` and
//! `c·x + k >= 0`) have no integer point, by propagating bounds along Shostak's graph
//! (FAIL-one-way-torus-growth-refusal). `true` shows the rows empty; `false` says only that this
//! test found no proof. Rows of more terms are left out, which keeps every answer sound: the
//! points of all the rows are points of those read.
//!
//! # The graph
//!
//! Each variable `x` has two nodes, the lower node for `z = x` and the upper node for `z = -x`;
//! a node's value is a lower bound on its `z`, so the upper node's value is minus an upper bound
//! on `x`, and the rows are empty once some variable has `lower + upper > 0`. The row
//! `c·x + k >= 0` gives the node of `x` whose `z` is `sign(c)·x` the value `ceil(-k / |c|)`. The
//! row `a·x + b·y + k >= 0` gives two edges. Written as `b·y >= -a·x - k`, it says
//! `z_y >= (|a|·z_x - k) / |b|` with `z_x = -sign(a)·x` and `z_y = sign(b)·y`: the edge from the
//! node of `z_x` to the node of `z_y`, of gain `|a| / |b|`; and the same with `x` and `y`
//! swapped. Since `|a| > 0`, a lower bound `l` on `z_x` gives the lower bound
//! `ceil((|a|·l - k) / |b|)` on `z_y` at every integer point, the rounding up being valid because
//! `z_y` is an integer. This is the graph of Shostak \[S\] as Aspvall and Shiloach \[AS\] give it,
//! with each variable split into its two signs, so that every edge reads a lower bound and
//! writes one.
//!
//! # The search
//!
//! The values start at the bounds of the one-variable rows and are raised along edges in the
//! order of a queue (Bellman, Ford and Moore's search, as in `zed_graph::worklist`), each raise
//! recording its edge as the node's parent. After every `nodes` raises the parents are walked;
//! a cycle of parent edges, followed from a node `v` back to itself, composes to
//! `z_v >= G·z_v + H`, with `G` the product of the gains (positive) and `H` from the constants:
//! across an edge `z_w >= g·z_u + h` the map so far `z_v >= G·z_w + H` becomes
//! `z_v >= (G·g)·z_u + (G·h + H)`. This is the loop inequality of \[AS\] (`(a_P + b_P)x <= c_P`,
//! here `(1 - G)·z_v >= H`), and
//!
//! - `G = 1` and `H > 0`: no point (the infeasible loop of \[AS\]);
//! - `G < 1`: `z_v >= ceil(H / (1 - G))`, and `v` is raised to that bound when it is higher, its
//!   parent cleared;
//! - `G > 1`: `z_v <= floor(H / (1 - G))`, and the rows are empty when the value of `v` is
//!   higher. The bound on `-z_v` is not written to the other node of `v` (see below).
//!
//! The search ends with `false` when the queue is empty, and with `false` when its edge scans
//! pass `(nodes + 1)·(edges + nodes)`, the work of Bellman's `nodes + 1` passes, each over every
//! edge, plus a walk of the parents per pass.
//!
//! # Proof
//!
//! Let `T` map values (integers or `-∞` or `+∞` at each node) to the values raised by every edge
//! once and kept at least the one-variable bounds; `T` is monotone, so it has a least fixed point
//! `F` (Knaster–Tarski), and `F` is the least `w` with `T(w) <= w`. Claims:
//!
//! 1. Every value is a lower bound on its `z` at every integer point of the rows (sound): the
//!    one-variable bounds and each edge by the rounding above; a cycle's bound because it
//!    composes valid inequalities with positive gains, and `z_v` is an integer.
//! 2. Every value is at most `F`: true at the start; an edge from `u` writes at most
//!    `ceil((|a|·F(u) - k) / |b|) <= F(to)`, since `F = T(F)`; for a cycle with `G < 1` and
//!    `F(v)` finite, `F` meets every edge of the cycle, so composing (rounding up only raises)
//!    gives `F(v) >= G·F(v) + H`, so `F(v) >= H / (1 - G)` and, an integer, `F(v) >= ceil(...)`.
//! 3. Every `true` shows `F` crossing (some `F(lower) + F(upper) > 0`, by 2 and monotonicity) or
//!    infinite at a node: for `G = 1, H > 0`, `F(v) >= F(v) + H` holds only at `+∞`; for
//!    `G > 1` with value above `floor(H / (1 - G))`, so above `H / (1 - G)` and `F(v)` too,
//!    a finite `F(v)` would give `(1 - G)·F(v) >= H`, so `F(v) <= H / (1 - G)`, which it is not.
//!    An infinite `F(v)` shows the rows empty too, since by 1 every value is a valid bound.
//! 4. When the queue empties, every node was scanned after its last raise, so the values `w`
//!    have `T(w) <= w`, hence `w >= F`; with 2, `w = F`. Every raise was tested for crossing,
//!    so `F` does not cross and is finite, and the answer `false` is again "F crosses or is
//!    infinite".
//!
//! So whenever the search ends before its bound on scans, the answer is whether `F` crosses or
//! is infinite, which `T`, and so the rows alone, defines: renaming the variables renames the
//! nodes and changes nothing else, and the order of the rows changes only the order of the
//! queue. Only a search stopped by the bound can answer by the order. That is also why a
//! `G > 1` bound is not written to the other node of `v`: the bound is valid, but which cycles
//! the parents show depends on the order, so writing it would make the values, and an answer,
//! depend on the order, where testing it only reaches sooner an answer 3 shows is `F`'s.
//!
//! # Complexity tradeoff
//!
//! Naive version: Fourier–Motzkin elimination, which on TVPI rows stays TVPI but can multiply
//! the rows, or a complete TVPI test: \[AS\] in `O(m·n³·I)`, Hochbaum and Naor \[HN\] in
//! `O(m·n²·log m)`, which decide rational feasibility exactly. Used: one bound propagation in the
//! manner of Procedure 2.1 of \[AS\] as \[HN\] states it (`O(m·n)` operations), with the loop
//! inequalities of the cycles it meets: at most `(n' + 1)·(m' + n')` edge scans for `n'` nodes
//! and `m'` edges, so `O(m·n)` arithmetic operations, and a walk of `O(n')` per `n'` raises.
//! Numbers grow by at most the bits of one coefficient per raise, so the cost is polynomial in the
//! size of the rows; where the bounds settle or a cycle shows them crossing in a few rounds, as
//! on the capped one-way torus (every node raised twice, then one walk), the cost is linear in the
//! rows. What is given up: completeness. Rows empty only over the rationals through a cycle of
//! gain above 1 that no bound pushes past its fixed point, or through nodes no bound reaches
//! (the search starts only at nodes a one-variable row gives a value, so `x - y >= 1`,
//! `y - x >= 1` alone is not shown empty, though its loop has gain 1), are not found, nor is
//! integer emptiness beyond the rounding of each edge. A complete test costs
//! `n` searches like this one at least (\[HN\] runs Procedure 2.1 inside a binary search per
//! variable). Trigger: none; every TVPI row is read. Tests: `tvpi::tests` and
//! `l01_38_omega_test::names::a_capped_one_way_torus_is_decided`, with the scaling benchmarks
//! `decide_on_a_one_way_torus_scales` and `tvpi_on_a_one_way_torus_scales` in
//! `l01_38_omega_test::bench::names`.
//!
//! # References
//!
//! "Read" names the copy read on 2026-11-28 (verification only, kept outside the repository);
//! the record is in verification/bib.md.
//!
//! \[S\]: R. Shostak, "Deciding linear inequalities by computing loop residues", J. ACM 28(4),
//! 1981, pp. 769–779, doi:10.1145/322276.322288. Not read (the mirror answered 503); cited
//! through \[AS\], which states its lemma and theorem.
//! \[AS\]: B. Aspvall and Y. Shiloach, "A polynomial time algorithm for solving systems of linear
//! inequalities with two variables per inequality", SIAM J. Comput. 9(4), 1980, pp. 827–845,
//! doi:10.1137/0209063. Read (PDF from LibGen; p. 829 checked on the page image). Lemma 1
//! (Shostak), p. 829: "If P is an admissible path with initial vertex x, final vertex y, and
//! residue ⟨a_P, b_P, c_P⟩, then any point (i.e., assignment of rational values to variables)
//! that satisfies the inequalities that label the edges of P satisfies a_P x + b_P y <= c_P."
//! p. 829: "An admissible loop P with initial vertex x is infeasible if a_P + b_P = 0 and
//! c_P < 0, since by Lemma 1 any solution of S must satisfy the unsatisfiable loop inequality
//! (a_P + b_P)x <= c_P." Theorem 1 (Shostak): S is satisfiable "if and only if G(S') has no
//! infeasible simple loop", `S'` adding `(a_P + b_P)x <= c_P` for every admissible simple loop
//! with `a_P + b_P != 0`; and "the number of simple cycles in a graph on n vertices can be
//! exponential in n". Here the loops are only those the parents show, so the test is sound and
//! not complete.
//! \[HN\]: D. S. Hochbaum and J. Naor, "Simple and fast algorithms for linear and integer programs
//! with two variables per inequality", SIAM J. Comput. 23(6), 1994, pp. 1179–1192,
//! doi:10.1137/s0097539793251876. Read (PDF from LibGen; abstract checked on the page image).
//! Abstract: "an O(mn² log m) algorithm for solving feasibility in linear programs with up to
//! two variables per inequality which is derived directly from the Fourier–Motzkin elimination
//! method". Procedure 2.1, p. 1182: "it can be decided in O(mn) operations" where a value lies
//! against a variable's feasible range, by "propagating the implications of the equality
//! x_i = λ in a manner very similar to the Bellman-Ford algorithm".

use std::collections::VecDeque;

use super::linear::Term;
use zedc_int::int::Int;
use zedc_int::q::Q;

/// An edge `from → to`: every integer point has `z[to] >= (num·z[from] - k) / den`.
struct Edge {
    from: usize,
    to: usize,
    num: Int,
    den: Int,
    k: Int,
}

/// Whether the rows `Σ a·x + k >= 0` of at most two terms each show the system empty (module
/// doc); rows of more terms are not read. `true` is a proof that no integer point exists;
/// `false` is no answer.
pub fn empty<'r>(rows: impl IntoIterator<Item = (&'r [Term], &'r Int)>) -> bool {
    search(rows) == Some(true)
}

/// The answer of [`empty`], `None` when the search stopped at its bound on scans, where the
/// answer may depend on the order of the rows (module doc, "Proof").
fn search<'r>(rows: impl IntoIterator<Item = (&'r [Term], &'r Int)>) -> Option<bool> {
    let rows: Vec<(&[Term], &Int)> = rows.into_iter().filter(|(a, _)| a.len() <= 2).collect();
    let mut vars: Vec<usize> = rows
        .iter()
        .flat_map(|(a, _)| a.iter().map(|t| t.0))
        .collect();
    vars.sort_unstable();
    vars.dedup();
    let place = |x: usize| vars.binary_search(&x).expect("a variable of the rows");
    // The node of `z = x` (`lower`) or of `z = -x`.
    let node = |x: usize, lower: bool| 2 * place(x) + usize::from(!lower);
    let nodes = 2 * vars.len();
    let mut val: Vec<Option<Int>> = vec![None; nodes];
    let mut edges = Vec::new();
    for (a, k) in rows {
        // Two terms of one variable are one term of the summed coefficient.
        let merged;
        let a = match a {
            [(x, a), (y, b)] if x == y => {
                merged = [(*x, a + b)];
                &merged[..usize::from(!merged[0].1.is_zero())]
            }
            _ => a,
        };
        match a {
            [] if k.is_negative() => return Some(true),
            [(x, c)] if !c.is_zero() => {
                let b = (-k).div_ceil(&c.abs());
                let v = &mut val[node(*x, c.is_positive())];
                if v.as_ref().is_none_or(|old| b > *old) {
                    *v = Some(b);
                }
            }
            [(x, a), (y, b)] if x != y && !a.is_zero() && !b.is_zero() => {
                for ((x, a), (y, b)) in [((x, a), (y, b)), ((y, b), (x, a))] {
                    edges.push(Edge {
                        from: node(*x, a.is_negative()),
                        to: node(*y, b.is_positive()),
                        num: a.abs(),
                        den: b.abs(),
                        k: k.clone(),
                    });
                }
            }
            _ => {}
        }
    }
    edges.sort_unstable_by_key(|e| e.from);
    let mut first = vec![0; nodes + 1];
    for e in &edges {
        first[e.from + 1] += 1;
    }
    for u in 0..nodes {
        first[u + 1] += first[u];
    }
    Search {
        edges,
        first,
        val,
        parent: vec![None; nodes],
        queue: VecDeque::new(),
        queued: vec![false; nodes],
        stamp: vec![0; nodes],
        walks: 0,
    }
    .run()
}

/// The state of the search of [`empty`].
struct Search {
    /// The edges, by `from`.
    edges: Vec<Edge>,
    /// The edges out of `u` are `edges[first[u]..first[u + 1]]`.
    first: Vec<usize>,
    /// The lower bound on each node's `z`, `None` for none.
    val: Vec<Option<Int>>,
    /// The edge that last raised each node, `None` for a node not raised by an edge since its
    /// last raise by a cycle or since the start.
    parent: Vec<Option<usize>>,
    queue: VecDeque<usize>,
    queued: Vec<bool>,
    /// The walk that last reached each node, 0 for none ([`Search::cycles`]).
    stamp: Vec<usize>,
    walks: usize,
}

impl Search {
    /// `Some(true)` for rows shown empty, `Some(false)` when the bounds settled, `None` when the
    /// scans passed their bound.
    fn run(&mut self) -> Option<bool> {
        let nodes = self.val.len();
        for v in 0..nodes {
            if self.val[v].is_some() {
                if self.crosses(v) {
                    return Some(true);
                }
                self.push(v);
            }
        }
        let budget = (nodes + 1).saturating_mul(self.edges.len() + nodes);
        let (mut scans, mut raised) = (0usize, 0usize);
        while let Some(u) = self.queue.pop_front() {
            self.queued[u] = false;
            let zu = self.val[u]
                .clone()
                .expect("only a node with a bound is queued");
            for e in self.first[u]..self.first[u + 1] {
                scans += 1;
                if scans > budget {
                    return None;
                }
                let edge = &self.edges[e];
                let to = edge.to;
                let c = (&(&edge.num * &zu) - &edge.k).div_ceil(&edge.den);
                if self.val[to].as_ref().is_none_or(|old| c > *old) {
                    self.val[to] = Some(c);
                    self.parent[to] = Some(e);
                    if self.crosses(to) {
                        return Some(true);
                    }
                    self.push(to);
                    raised += 1;
                }
            }
            if raised >= nodes {
                raised = 0;
                if self.cycles() {
                    return Some(true);
                }
            }
        }
        Some(false)
    }

    fn push(&mut self, v: usize) {
        if !self.queued[v] {
            self.queued[v] = true;
            self.queue.push_back(v);
        }
    }

    /// Whether the variable of node `v` has its lower bound above its upper bound.
    fn crosses(&self, v: usize) -> bool {
        match (&self.val[v & !1], &self.val[v | 1]) {
            (Some(lo), Some(up)) => (lo + up).is_positive(),
            _ => false,
        }
    }

    /// Walks the parents from each node, each node once: a walk that comes back to a node it
    /// reached closes a cycle, which [`Search::close`] reads. `true` when a cycle shows the rows
    /// empty. In time linear in the nodes, plus the cycles' arithmetic.
    fn cycles(&mut self) -> bool {
        let start = self.walks + 1;
        for s in 0..self.val.len() {
            if self.stamp[s] >= start {
                continue;
            }
            self.walks += 1;
            let w = self.walks;
            let mut v = s;
            let closed = loop {
                if self.stamp[v] >= start {
                    break self.stamp[v] == w;
                }
                self.stamp[v] = w;
                match self.parent[v] {
                    Some(e) => v = self.edges[e].from,
                    None => break false,
                }
            };
            if closed && self.close(v) {
                return true;
            }
        }
        false
    }

    /// Reads the cycle of parents through `v` as `z_v >= G·z_v + H` (module doc): `true` when
    /// it shows the rows empty; a cycle of gain below 1 may raise `v`.
    fn close(&mut self, v: usize) -> bool {
        let (mut g, mut h) = (Q::of(Int::ONE), Q::of(Int::ZERO));
        let mut w = v;
        loop {
            let e = &self.edges[self.parent[w].expect("a node on a cycle of parents")];
            h = h.add(&g.mul(&Q::new(-&e.k, e.den.clone())));
            g = g.mul(&Q::new(e.num.clone(), e.den.clone()));
            w = e.from;
            if w == v {
                break;
            }
        }
        let one = Q::of(Int::ONE);
        let now = self.val[v]
            .as_ref()
            .expect("a node with a parent has a bound");
        match g.cmp(&one) {
            std::cmp::Ordering::Equal => h.is_positive(),
            std::cmp::Ordering::Greater => *now > h.div(&one.sub(&g)).floor(),
            std::cmp::Ordering::Less => {
                let b = h.div(&one.sub(&g)).ceil();
                if b > *now {
                    self.val[v] = Some(b);
                    self.parent[v] = None;
                    if self.crosses(v) {
                        return true;
                    }
                    self.push(v);
                }
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Int, Term, empty, search};
    use crate::seed::Rng;

    fn answer(rs: &[(Vec<Term>, Int)]) -> Option<bool> {
        search(rs.iter().map(|(a, k)| (&a[..], k)))
    }

    /// The rows `(coefficients, k)` as [`empty`] reads them.
    fn rows(rs: &[(&[(usize, i64)], i64)]) -> Vec<(Vec<Term>, Int)> {
        rs.iter()
            .map(|(a, k)| {
                let a = a.iter().map(|&(x, c)| (x, Int::from(c))).collect();
                (a, Int::from(*k))
            })
            .collect()
    }

    fn is_empty(rs: &[(Vec<Term>, Int)]) -> bool {
        empty(rs.iter().map(|(a, k)| (&a[..], k)))
    }

    /// The capped one-way torus of FAIL-one-way-torus-growth-refusal, on a `t × t` torus:
    /// `3·v[i][j+1] >= v[i][j] + 10`, `3·v[i+1][j] >= v[i][j] + 10` and `v[i][j] <= top`. At
    /// top 4 the bound `-v >= -4` goes round as `-v >= 3·(-4) + 10 = -2` and up from there; a
    /// cycle of `L` edges has gain `3^L` and fixed point -5, and a value above it shows the rows
    /// empty. At top 5 the bound -5 is the fixed point and nothing is raised.
    fn torus(t: usize, top: i64) -> Vec<(Vec<Term>, Int)> {
        let v = |i: usize, j: usize| (i % t) * t + j % t;
        let mut rs = Vec::new();
        for i in 0..t {
            for j in 0..t {
                for next in [v(i, j + 1), v(i + 1, j)] {
                    rs.push((
                        vec![(next, Int::from(3)), (v(i, j), Int::from(-1))],
                        Int::from(-10),
                    ));
                }
                rs.push((vec![(v(i, j), Int::from(-1))], Int::from(top)));
            }
        }
        rs
    }

    #[test]
    fn the_capped_one_way_torus_is_empty_at_top_4_only() {
        for t in 1..=12 {
            for top in [4, 5] {
                let rs = torus(t, top);
                let want = Some(top == 4);
                assert_eq!(answer(&rs), want, "t = {t}, top {top}");
                // The variables in the reverse order and the rows reversed.
                let back: Vec<(Vec<Term>, Int)> = rs
                    .iter()
                    .rev()
                    .map(|(a, k)| {
                        let a = a.iter().map(|(j, c)| (t * t - 1 - j, c.clone())).collect();
                        (a, k.clone())
                    })
                    .collect();
                assert_eq!(answer(&back), want, "t = {t}, top {top}, reversed");
            }
        }
    }

    #[test]
    fn a_cycle_of_gain_1_and_positive_constant_is_empty() {
        // x - y >= 1 and y - x >= 1 with x <= 100: the bound goes round and the loop gives
        // `-x >= -x + 2`.
        let cap = (&[(0, -1)][..], 100);
        let cycle = [(&[(0, 1), (1, -1)][..], -1), (&[(1, 1), (0, -1)][..], -1)];
        assert_eq!(answer(&rows(&[cycle[0], cycle[1], cap])), Some(true));
        // With no bound no node has a value, the search starts nowhere and the cycle is not met
        // (module doc, "What is given up"); the stages of the Omega test before it decide such
        // rows.
        assert_eq!(answer(&rows(&cycle)), Some(false));
        // x - y >= 0 and y - x >= 0 have points.
        let flat = [(&[(0, 1), (1, -1)][..], 0), (&[(1, 1), (0, -1)][..], 0)];
        assert_eq!(answer(&rows(&[flat[0], flat[1], cap])), Some(false));
    }

    #[test]
    fn a_cycle_of_gain_below_1_jumps_to_its_fixed_point() {
        // 2x >= y + 10, 2y >= x + 10 from x, y >= 0: the fixed point is x = y = 10, reached only
        // in the limit by the edges, at once by the cycle; with x <= 9 the rows are empty, with
        // x <= 10 they are not.
        let base: [(&[(usize, i64)], i64); 4] = [
            (&[(0, 2), (1, -1)], -10),
            (&[(1, 2), (0, -1)], -10),
            (&[(0, 1)], 0),
            (&[(1, 1)], 0),
        ];
        for (top, want) in [(9, true), (10, false)] {
            let mut rs = base.to_vec();
            let cap: &[(usize, i64)] = &[(0, -1)];
            rs.push((cap, top));
            assert_eq!(is_empty(&rows(&rs)), want, "x <= {top}");
        }
        // The constants scaled by 2^40: the edges alone would take about 40 rounds per bit.
        let big = 1i64 << 40;
        let rs = rows(&[
            (&[(0, 2), (1, -1)], -big),
            (&[(1, 2), (0, -1)], -big),
            (&[(0, 1)], 0),
            (&[(1, 1)], 0),
            (&[(0, -1)], big - 1),
        ]);
        assert!(is_empty(&rs));
    }

    #[test]
    fn rounding_at_each_edge_finds_integer_emptiness() {
        // 2x >= 1 and 2x <= 1: x = 1/2 only, no integer.
        assert!(is_empty(&rows(&[(&[(0, 2)], -1), (&[(0, -2)], 1)])));
        // 2y >= x, 2y <= x, x = 1: y = 1/2.
        assert!(is_empty(&rows(&[
            (&[(1, 2), (0, -1)], 0),
            (&[(1, -2), (0, 1)], 0),
            (&[(0, 1)], -1),
            (&[(0, -1)], 1),
        ])));
    }

    #[test]
    fn rows_of_three_terms_and_constant_rows_are_read_as_given() {
        // x + y + z >= 1 with every variable at most 0 is empty, but a row of three terms is
        // not read; a constant row below zero is.
        let wide = rows(&[
            (&[(0, 1), (1, 1), (2, 1)], -1),
            (&[(0, -1)], 0),
            (&[(1, -1)], 0),
            (&[(2, -1)], 0),
        ]);
        assert!(!is_empty(&wide));
        assert!(is_empty(&rows(&[(&[], -1)])));
        assert!(!is_empty(&rows(&[(&[], 0)])));
        assert!(!is_empty(&[]));
    }

    /// Whether the rows have an integer point with every variable in `-r..=r`.
    fn has_point_in(rs: &[(Vec<Term>, Int)], n: usize, r: i64) -> bool {
        let mut x = vec![-r; n];
        loop {
            let holds = rs.iter().all(|(a, k)| {
                let s = a
                    .iter()
                    .fold(k.clone(), |s, (j, c)| &s + &(c * &Int::from(x[*j])));
                !s.is_negative()
            });
            if holds {
                return true;
            }
            let Some(j) = (0..n).find(|&j| x[j] < r) else {
                return false;
            };
            x[j] += 1;
            x[..j].fill(-r);
        }
    }

    /// Random TVPI rows over at most 4 variables, each boxed in `-r..=r`, checked against the
    /// points of the box (sound: never `true` with a point) and under a renaming and a reversal
    /// of the rows (the same answer where neither search stopped at its bound, module doc
    /// "Proof"). Returns how many were shown empty, and how many searches stopped.
    fn random_rows_agree(rng: &mut Rng, cases: usize) -> (usize, usize) {
        let r = 3;
        let mut shown = (0, 0);
        for case in 0..cases {
            let n = 1 + rng.below(4);
            let mut rs: Vec<(Vec<Term>, Int)> = Vec::new();
            for j in 0..n {
                rs.push((vec![(j, Int::ONE)], Int::from(r)));
                rs.push((vec![(j, Int::from(-1))], Int::from(r)));
            }
            for _ in 0..rng.below(7) {
                let x = rng.below(n);
                let c = |rng: &mut Rng| {
                    let c = rng.int(1, 4);
                    if rng.below(2) == 0 { c } else { -c }
                };
                let a = if rng.below(4) == 0 || n == 1 {
                    vec![(x, Int::from(c(rng)))]
                } else {
                    let y = (x + 1 + rng.below(n - 1)) % n;
                    vec![(x, Int::from(c(rng))), (y, Int::from(c(rng)))]
                };
                rs.push((a, Int::from(rng.int(-8, 8))));
            }
            let got = answer(&rs);
            assert!(
                got != Some(true) || !has_point_in(&rs, n, r),
                "case {case}: {rs:?} has a point"
            );
            let renamed: Vec<(Vec<Term>, Int)> = rs
                .iter()
                .rev()
                .map(|(a, k)| {
                    let a = a
                        .iter()
                        .map(|(j, c)| (7 * (n - 1 - j), c.clone()))
                        .collect();
                    (a, k.clone())
                })
                .collect();
            let other = answer(&renamed);
            if got.is_some() && other.is_some() {
                assert_eq!(other, got, "case {case}: {rs:?} renamed");
            }
            shown.0 += usize::from(got == Some(true));
            shown.1 += usize::from(got.is_none()) + usize::from(other.is_none());
        }
        shown
    }

    #[test]
    fn random_boxed_rows_are_shown_empty_only_without_a_point() {
        let (mut rng, seed) = Rng::fresh("random_boxed_rows_are_shown_empty_only_without_a_point");
        let (shown, stopped) = random_rows_agree(&mut rng, 3000);
        // Measured 2026-11-28 at seeds 1 to 5: 1052, 1008, 1006, 997 and 999 shown empty, and
        // no search stopped at its bound.
        assert!(shown > 800, "seed {seed}: only {shown} of 3000 shown empty");
        assert_eq!(
            stopped, 0,
            "seed {seed}: {stopped} searches stopped at the bound"
        );
    }
}
