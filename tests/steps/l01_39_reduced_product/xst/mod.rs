//! The tests of the cross-review campaign xst, rounds 3 and 4, merged into one set (plan row
//! XST-unified-tests). Each test is one the meta-reviews META3.md and META4.md mark valid,
//! ported from the script or probe that wrote it; its comment names the source.
//!
//! - [`holes`]: `Scope` on names with holes (values left out) linked by difference tests
//!   `x - y <= w`, against enumeration: the named systems CE-A, CE-B and the collective
//!   example in every order, seeded random corpora, unbounded names, and the laps, staircase
//!   and mixed families at `n` and `8n`. Result 1 of META4 (SCC composition) makes every
//!   endpoint and every set exact; tests that main does not pass yet wait for item
//!   ST-holes-moves.
//! - [`holes_model`]: the reference models of result 1 (Codex's SCC composition, and closure
//!   with snapping below a cap) against enumeration, with the negative controls the sources
//!   wrote: the hull of each name's range, snapping once, ends without the interior, and no
//!   snapping.
//! - [`s4`]: `Scope` on disjunctions (S4, results 2 and 3 of META4): the orchestrator's fan-in
//!   and diamond families, the class K counterexamples in both orders, the B4 tests flipped to
//!   their exact answers, B(S) on moving bounds and the round-3 scaling families. Tests that
//!   main does not pass yet wait for item ST-walk-implicit.
//! - [`s4_model`]: the box-only base and greatest fixpoint of S4 on two names, against
//!   enumeration (Claude's model and Codex's), with Property P, order independence,
//!   monotonicity and the controls that break each; Codex's round-3 integer octagon projection
//!   on 6,561 bound choices, the two-hub component with a dominating disjunction and the
//!   implication walk, with their controls.
//! - [`threshold`]: the threshold-implication solver of QUESTIONS A57 (`threshold::solve`)
//!   against enumeration in each sign case, the unbounded hub, A57's reachability reduction,
//!   and the scaling of the walk and of the hub search (ported from `a57.mjs` and `red.mjs`).
//!
//! Rejected by the meta-reviews and not ported: Gemini's patch to `Scope` (round 3 and round
//! 4), the Bellman-Ford condition in C_holes case 3, class K without condition (iii), and
//! C_comb. Where one of these gives a wrong answer on a named case, the test that holds the
//! case says so.

mod holes;
mod holes_model;
mod s4;
mod s4_model;
mod threshold;

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc::store::cell::Premises;
use zedc::store::product::Scope;

use crate::ints;
use crate::nests::{and, int, prim, var};

/// The generator every source used: `state * 6364136223846793005 + 1442695040888963407`,
/// a value below `n` from the high bits.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % n
    }
}

/// A system of names with holes: name `i` lies in `range[i]` and is none of `out[i]`, and
/// each edge `(u, v, w)` is the test `x_v - x_u <= w`.
#[derive(Clone, Debug)]
struct Inst {
    range: Vec<(i64, i64)>,
    out: Vec<Vec<i64>>,
    edges: Vec<(usize, usize, i64)>,
}

/// `x{i}`.
fn nm(i: usize) -> String {
    format!("x{i}")
}

impl Inst {
    fn len(&self) -> usize {
        self.range.len()
    }

    /// The tests of the system: the ranges as one conjunction, then each hole and each edge.
    fn tests(&self) -> (Term, Vec<Term>) {
        let bx = (0..self.len())
            .map(|i| {
                and(
                    prim(Prim::Ge, var(&nm(i)), int(self.range[i].0)),
                    prim(Prim::Le, var(&nm(i)), int(self.range[i].1)),
                )
            })
            .reduce(and)
            .expect("one name");
        let mut ts: Vec<Term> = vec![];
        for (i, vs) in self.out.iter().enumerate() {
            for v in vs {
                ts.push(prim(Prim::Ne, var(&nm(i)), int(*v)));
            }
        }
        for &(u, v, w) in &self.edges {
            ts.push(prim(
                Prim::Le,
                prim(Prim::Sub, var(&nm(v)), var(&nm(u))),
                int(w),
            ));
        }
        (bx, ts)
    }

    /// The scope of the names, known only when the program runs.
    fn scope(&self) -> Scope {
        let ns: Vec<Arc<str>> = (0..self.len()).map(|i| Arc::from(nm(i))).collect();
        ints(&ns)
    }

    /// The scope after the ranges and then the tests in `order`.
    fn in_order(&self, order: &[usize]) -> Scope {
        let p = Premises::new();
        let (bx, ts) = self.tests();
        order
            .iter()
            .fold(self.scope().assume(&bx, true, &p), |s, &i| {
                s.assume(&ts[i], true, &p)
            })
    }

    /// The scope after the ranges and every test as one conjunction.
    fn at_once(&self) -> Scope {
        let p = Premises::new();
        let (bx, ts) = self.tests();
        let all = ts.into_iter().fold(bx, and);
        self.scope().assume(&all, true, &p)
    }

    /// Each name's values in the exact projection, by enumeration of every point of the
    /// ranges.
    fn exact(&self) -> Vec<Vec<i64>> {
        let n = self.len();
        let mut out: Vec<std::collections::BTreeSet<i64>> = vec![Default::default(); n];
        let mut x: Vec<i64> = self.range.iter().map(|r| r.0).collect();
        loop {
            let ok = (0..n).all(|i| !self.out[i].contains(&x[i]))
                && self.edges.iter().all(|&(u, v, w)| x[v] - x[u] <= w);
            if ok {
                for i in 0..n {
                    out[i].insert(x[i]);
                }
            }
            let mut k = 0;
            while k < n && x[k] == self.range[k].1 {
                x[k] = self.range[k].0;
                k += 1;
            }
            if k == n {
                break;
            }
            x[k] += 1;
        }
        out.into_iter().map(|s| s.into_iter().collect()).collect()
    }

    /// Each name's values in `s`, within its range.
    fn values(&self, s: &Scope) -> Vec<Vec<i64>> {
        (0..self.len())
            .map(|i| {
                let p = s.get(&nm(i));
                (self.range[i].0..=self.range[i].1)
                    .filter(|v| p.contains(&Value::Int(*v)))
                    .collect()
            })
            .collect()
    }

    /// Each name's range, every hole ignored: the answer of a method that drops the holes.
    fn hull(&self) -> Vec<Vec<i64>> {
        self.range.iter().map(|r| (r.0..=r.1).collect()).collect()
    }
}

/// The least and greatest value of each set, `None` for an empty set.
fn ends(sets: &[Vec<i64>]) -> Vec<Option<(i64, i64)>> {
    sets.iter()
        .map(|s| Some((*s.first()?, *s.last()?)))
        .collect()
}

/// Every order of `k` items.
fn permutations(k: usize) -> Vec<Vec<usize>> {
    if k == 0 {
        return vec![vec![]];
    }
    let mut out = vec![];
    for p in permutations(k - 1) {
        for i in 0..=p.len() {
            let mut q = p.clone();
            q.insert(i, k - 1);
            out.push(q);
        }
    }
    out
}

/// Every rotation of `0..k` and of its reverse: `2k` orders, which put each item first and
/// last.
fn rotations(k: usize) -> Vec<Vec<usize>> {
    (0..k)
        .flat_map(|s| {
            [
                (0..k).map(|i| (s + i) % k).collect(),
                (0..k).map(|i| (s + k - i) % k).collect(),
            ]
        })
        .collect()
}
