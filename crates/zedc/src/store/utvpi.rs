//! Integer feasibility of rows `±x ± y + k >= 0` and `±x + k >= 0` (DESIGN.md sec:domains, step
//! L1.38), by the test of Lahiri and Musuvathi [UTVPI]: such rows have an integer point exactly
//! when their constraint graph has no negative cycle and no zero-weight cycle through both
//! literals of a variable whose part from `+x` to `-x` has odd weight.
//!
//! The graph has a node for each literal, `+x` at `2j` and `-x` at `2j + 1`. The row
//! `l1 + l2 <= k`, with `l1` and `l2` literals, is the two edges `¬l1 → l2` and `¬l2 → l1` of
//! weight `k`, and `l1 <= k` is the edge `¬l1 → l1` of weight `2k`. A rational point `v` of the
//! rows is a potential, `p(+x) = v[x]` and `p(-x) = -v[x]`, under which no edge is shorter than
//! the difference of its ends; so the graph has a negative cycle exactly when the rows have no
//! rational point, and its zero-weight cycles are exactly the cycles of its tight edges, those
//! whose weight is the difference of their ends. Along tight edges the path from `+x` to `-x`
//! weighs `p(-x) - p(+x) = -2·v[x]`, odd exactly when `v[x]` has denominator 2. The test is then
//! one simplex run and one strongly connected components pass over the tight edges.
//!
//! [UTVPI]: S. K. Lahiri and M. Musuvathi, "An Efficient Decision Procedure for UTVPI
//! Constraints", FroCoS 2005.

use super::int::Int;
use super::simplex::{Q, Simplex, Term};

/// Whether the rows, each of one or two terms with unit coefficients, over `n` variables, have
/// no integer point.
pub(crate) fn integer_empty(n: usize, rows: &[(&[Term], &Int)]) -> bool {
    let mut lp = Simplex::new(n, rows.iter().copied());
    if !lp.feasible() {
        return true;
    }
    let p = |node: usize| {
        let v = &lp.val[node / 2];
        if node.is_multiple_of(2) {
            v.clone()
        } else {
            v.neg()
        }
    };
    // The literal `-c·x` of a term `c·x`, as a node.
    let lit = |(j, c): &Term| if c.is_negative() { 2 * j } else { 2 * j + 1 };
    let mut out: Vec<Vec<usize>> = vec![Vec::new(); 2 * n];
    let mut edge = |from: usize, to: usize, w: Q| {
        if p(to) == p(from).add(&w) {
            out[from].push(to);
        }
    };
    for (a, k) in rows {
        match a {
            [t] => {
                let l = lit(t);
                edge(l ^ 1, l, Q::of(*k + *k));
            }
            [s, t] => {
                let (l1, l2) = (lit(s), lit(t));
                edge(l1 ^ 1, l2, Q::of((*k).clone()));
                edge(l2 ^ 1, l1, Q::of((*k).clone()));
            }
            _ => unreachable!("a row of one or two terms"),
        }
    }
    let comp = components(&out);
    (0..n).any(|j| comp[2 * j] == comp[2 * j + 1] && lp.val[j].d == Int::from(2))
}

/// The strongly connected component of each node (Tarjan), with an explicit stack.
fn components(out: &[Vec<usize>]) -> Vec<usize> {
    const NONE: usize = usize::MAX;
    let n = out.len();
    let (mut index, mut low, mut comp) = (vec![NONE; n], vec![0; n], vec![NONE; n]);
    let (mut next, mut comps) = (0, 0);
    let mut held: Vec<usize> = Vec::new();
    // Each frame is a node and the place of the next edge to follow.
    let mut frames: Vec<(usize, usize)> = Vec::new();
    for root in 0..n {
        if index[root] != NONE {
            continue;
        }
        frames.push((root, 0));
        index[root] = next;
        low[root] = next;
        next += 1;
        held.push(root);
        while let Some(&mut (v, ref mut e)) = frames.last_mut() {
            if let Some(&w) = out[v].get(*e) {
                *e += 1;
                if index[w] == NONE {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    held.push(w);
                    frames.push((w, 0));
                } else if comp[w] == NONE {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            frames.pop();
            if let Some(&(u, _)) = frames.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                loop {
                    let w = held.pop().expect("held");
                    comp[w] = comps;
                    if w == v {
                        break;
                    }
                }
                comps += 1;
            }
        }
    }
    comp
}
