//! Step M0.5: widening and iteration.
//!
//! The store's iteration (DESIGN.md sec:constraints rule 1) is fixed down to the traversal:
//! the weak topological order of the dependency graph, the widening points and delay, the
//! two phases and their budgets, and the tonicity and interval-revision tables. Each piece
//! is checked against an independent implementation written here from the definition:
//! `wto` against the declarative definition of the order, `iteration` against a flattened
//! stack machine and against the concrete least fixpoint, `widening` for the termination
//! bound of every lattice, and `revision` on constraints from ordinary programs.

mod iteration;
mod revision;
mod widening;
mod wto;

use std::collections::BTreeSet;

use zed_tests::instances::Rng;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::iterate::Equations;

/// One term of a cell's transfer: `(cell[from] ⊓ filter) + offset`.
#[derive(Clone, Debug)]
struct Term {
    from: usize,
    filter: IntervalSet,
    offset: i64,
}

/// A system of interval equations, `cell[v] = init[v] ⊔ ⋃ terms[v]`: the shape the store's
/// equations take for loop counters, accumulators and bounds checks.
#[derive(Clone, Debug)]
struct System {
    init: Vec<IntervalSet>,
    terms: Vec<Vec<Term>>,
    reads: Vec<Vec<usize>>,
}

impl System {
    fn new(init: Vec<IntervalSet>, terms: Vec<Vec<Term>>) -> Self {
        let reads = terms
            .iter()
            .map(|ts| {
                let mut r: Vec<usize> = ts.iter().map(|t| t.from).collect();
                r.sort_unstable();
                r.dedup();
                r
            })
            .collect();
        System { init, terms, reads }
    }

    /// A random system of up to 8 cells, each reading up to 3 cells.
    fn random(rng: &mut Rng) -> Self {
        let n = 1 + rng.below(8);
        let mut init = Vec::new();
        let mut terms = Vec::new();
        for _ in 0..n {
            init.push(match rng.below(3) {
                0 => IntervalSet::empty(),
                _ => {
                    let lo = rng.int(-5, 5);
                    IntervalSet::of(lo, lo + rng.int(0, 3))
                }
            });
            let ts = (0..rng.below(4))
                .map(|_| Term {
                    from: rng.below(n),
                    filter: random_filter(rng),
                    offset: rng.int(-2, 2),
                })
                .collect();
            terms.push(ts);
        }
        System::new(init, terms)
    }

    /// The concrete least fixpoint over sets of integers, cut to `window`: every value a
    /// cell takes in an execution that stays in the window. The cut makes it a subset of the
    /// true least fixpoint, so it is a lower bound that every sound solution contains.
    fn concrete(&self, window: (i64, i64)) -> Vec<BTreeSet<i64>> {
        let n = self.init.len();
        let mut cells = vec![BTreeSet::new(); n];
        loop {
            let mut changed = false;
            for v in 0..n {
                let mut next: BTreeSet<i64> = (window.0..=window.1)
                    .filter(|&x| self.init[v].contains(x))
                    .collect();
                for t in &self.terms[v] {
                    for &x in &cells[t.from] {
                        let y = x + t.offset;
                        if t.filter.contains(x) && (window.0..=window.1).contains(&y) {
                            next.insert(y);
                        }
                    }
                }
                if next != cells[v] {
                    cells[v] = next;
                    changed = true;
                }
            }
            if !changed {
                return cells;
            }
        }
    }
}

fn random_filter(rng: &mut Rng) -> IntervalSet {
    match rng.below(4) {
        0 => IntervalSet::top(),
        1 => IntervalSet::range(End::NegInf, End::Fin(rng.int(-3, 8))),
        2 => IntervalSet::range(End::Fin(rng.int(-8, 3)), End::PosInf),
        _ => {
            let lo = rng.int(-6, 4);
            IntervalSet::of(lo, lo + rng.int(0, 6))
        }
    }
}

impl Equations<IntervalSet> for System {
    fn reads(&self) -> &[Vec<usize>] {
        &self.reads
    }
    fn eval(&self, v: usize, cells: &[IntervalSet]) -> IntervalSet {
        self.terms[v].iter().fold(self.init[v].clone(), |acc, t| {
            let moved = cells[t.from]
                .meet(&t.filter)
                .lift1(|(lo, hi)| vec![(shift(lo, t.offset), shift(hi, t.offset))]);
            acc.join(&moved)
        })
    }
}

fn shift(e: End, by: i64) -> End {
    match e {
        End::Fin(v) => End::from_i128(v as i128 + by as i128),
        e => e,
    }
}

/// Whether every cell contains its own projection: a post-fixpoint, which is what phase 1
/// must reach and phase 2 must keep.
fn is_post_fixpoint(eq: &System, cells: &[IntervalSet]) -> bool {
    (0..cells.len()).all(|v| eq.eval(v, cells).is_subset(&cells[v]))
}

/// `[lo, hi]` with `None` for an infinite end, for readable expectations.
fn iv(lo: Option<i64>, hi: Option<i64>) -> IntervalSet {
    IntervalSet::range(
        lo.map_or(End::NegInf, End::Fin),
        hi.map_or(End::PosInf, End::Fin),
    )
}
