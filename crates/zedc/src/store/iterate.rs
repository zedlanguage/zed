//! The store's iteration strategy (DESIGN.md sec:constraints rule 1, fixed by step M0.5).
//!
//! Phase 1 computes a post-fixpoint by forward projections only: Bourdoncle's recursive
//! strategy over the weak topological order of the dependency graph, joining at every cell
//! and widening at the heads of components after a delay. Phase 2 then narrows that
//! post-fixpoint in rounds: in each round every cell is met with its projection computed
//! from the state at the start of the round, until a round changes nothing or the round
//! budget is spent. Every value phase 2 passes through is sound, so the budget can stop it
//! anywhere; phase 1 values below the fixpoint are not, so a component whose head does not
//! stabilize within its bound is set to the top.
//!
//! The specification of these rules is prelude source, `zed/prelude/iteration.zed`; this
//! module is the Rust-hosted checker's copy.

use super::lattice::Lattice;
use super::wto::{Element, weak_topological_order};

/// A head's first changes in one stabilization of its component are joins; from this many
/// on, each change is a widening (step M0.5).
pub const WIDENING_DELAY: u32 = 3;

/// The most times a head is updated in one stabilization of its component; a component still
/// changing after that is set to the top (step M0.5).
pub const HEAD_ITERATIONS: u32 = 64;

/// The most rounds of phase 2 (step M0.5).
pub const NARROWING_ROUNDS: u32 = 64;

/// A system of equations over a lattice: one cell per vertex, `0..n` in source order.
pub trait Equations<L: Lattice> {
    /// For each cell, the cells its projection reads, in source order.
    fn reads(&self) -> &[Vec<usize>];
    /// The forward projection into cell `v` from the current cells.
    fn eval(&self, v: usize, cells: &[L]) -> L;
}

/// The constants of the strategy; [`Strategy::SPEC`] holds the specified ones, and the tests
/// vary them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Strategy {
    /// [`WIDENING_DELAY`].
    pub delay: u32,
    /// [`HEAD_ITERATIONS`].
    pub head_iterations: u32,
    /// [`NARROWING_ROUNDS`].
    pub rounds: u32,
}

impl Strategy {
    /// The specified strategy.
    pub const SPEC: Strategy = Strategy {
        delay: WIDENING_DELAY,
        head_iterations: HEAD_ITERATIONS,
        rounds: NARROWING_ROUNDS,
    };
}

/// The dependency graph: an edge from `u` to every cell that reads `u`, the successors in
/// source order.
pub fn dependency_graph(reads: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut succ = vec![Vec::new(); reads.len()];
    for (v, rs) in reads.iter().enumerate() {
        for &u in rs {
            succ[u].push(v);
        }
    }
    for s in &mut succ {
        s.sort_unstable();
        s.dedup();
    }
    succ
}

/// Phase 1 and then phase 2, from every cell at the bottom.
pub fn solve<L: Lattice>(eq: &impl Equations<L>, strategy: Strategy) -> Vec<L> {
    let order = weak_topological_order(&dependency_graph(eq.reads()));
    let mut cells = phase1(eq, &order, strategy);
    narrow(eq, &mut cells, strategy.rounds);
    cells
}

/// Phase 1 over the given order, from every cell at the bottom.
pub fn phase1<L: Lattice>(eq: &impl Equations<L>, order: &[Element], strategy: Strategy) -> Vec<L> {
    let mut cells = vec![L::bottom(); eq.reads().len()];
    stabilize(eq, order, strategy, &mut cells);
    cells
}

fn stabilize<L: Lattice>(eq: &impl Equations<L>, order: &[Element], s: Strategy, cells: &mut [L]) {
    for element in order {
        match element {
            Element::Vertex(v) => cells[*v] = cells[*v].join(&eq.eval(*v, cells)),
            Element::Component { head, body } => {
                let h = *head;
                let mut changes = 0;
                for i in 0.. {
                    let next = cells[h].join(&eq.eval(h, cells));
                    if i > 0 && next == cells[h] {
                        break;
                    }
                    if i == s.head_iterations {
                        for v in element.vertices() {
                            cells[v] = L::top();
                        }
                        break;
                    }
                    if next != cells[h] {
                        changes += 1;
                        cells[h] = if changes > s.delay {
                            cells[h].widen(&next)
                        } else {
                            next
                        };
                    }
                    stabilize(eq, body, s, cells);
                }
            }
        }
    }
}

/// Phase 2: rounds of meeting every cell with its projection from the state at the start of
/// the round, at most `rounds` of them. Returns the number of rounds that changed a cell.
pub fn narrow<L: Lattice>(eq: &impl Equations<L>, cells: &mut Vec<L>, rounds: u32) -> u32 {
    for round in 0..rounds {
        let next: Vec<L> = (0..cells.len())
            .map(|v| cells[v].meet(&eq.eval(v, cells)))
            .collect();
        if next == *cells {
            return round;
        }
        *cells = next;
    }
    rounds
}
