//! The store's iteration strategy (DESIGN.md sec:constraints rule 1, fixed by step M0.5).
//!
//! Phase 1 computes a post-fixpoint by forward projections only: Bourdoncle's recursive
//! strategy over the weak topological order of the dependency graph, joining at every cell
//! and widening at the heads of components. Phase 2 then narrows that post-fixpoint in rounds:
//! in each round every cell is narrowed by its meet with its projection computed from the
//! state at the start of the round, until a round changes nothing. Both phases end because
//! the widening and the narrowing move bounds only to the program's landmarks and to values
//! already present (module `lattice`), so no delay, no bound on a head's changes and no
//! budget of rounds enters.
//!
//! The specification of these rules is prelude source, `zed/prelude/iteration.zed`; this
//! module is the Rust-hosted checker's copy.

use super::lattice::{Landmarks, Lattice};
use super::wto::{Element, weak_topological_order};

/// A system of equations over a lattice: one cell per vertex, `0..n` in source order.
pub trait Equations<L: Lattice> {
    /// For each cell, the cells its projection reads, in source order.
    fn reads(&self) -> &[Vec<usize>];
    /// The forward projection into cell `v` from the current cells.
    fn eval(&self, v: usize, cells: &[L]) -> L;
    /// The values written in the equations, where a widening or a narrowing stops a bound.
    fn landmarks(&self) -> Landmarks;
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
pub fn solve<L: Lattice>(eq: &impl Equations<L>) -> Vec<L> {
    let order = weak_topological_order(&dependency_graph(eq.reads()));
    let mut cells = phase1(eq, &order);
    narrow(eq, &mut cells);
    cells
}

/// Phase 1 over the given order, from every cell at the bottom.
pub fn phase1<L: Lattice>(eq: &impl Equations<L>, order: &[Element]) -> Vec<L> {
    let n = eq.reads().len();
    let mut w = Walk {
        cells: vec![L::bottom(); n],
        marks: eq.landmarks(),
        dirty: vec![true; n],
        succ: dependency_graph(eq.reads()),
        pos: vec![0; n],
        end: vec![0; n],
        parent: vec![NONE; n],
        inner: vec![NONE; n],
    };
    w.number(order, NONE, &mut 0);
    w.stabilize(eq, order);
    w.cells
}

const NONE: usize = usize::MAX;

/// The state of phase 1. Components are named by their heads. `dirty[h]` says whether a
/// cell that the component reads from outside it has changed since the component last
/// stabilized; a clean component is skipped, which changes nothing, since its cells are then
/// a post-fixpoint of its own equations (in a weak topological order every edge back into the
/// component's cells goes to a head inside it). So a component is stabilized once per change
/// of a cell it reads from outside, not once per change of every enclosing head, and nested
/// loops cost work linear in their number, where restarted counters made it exponential in
/// the depth.
struct Walk<L> {
    cells: Vec<L>,
    marks: Landmarks,
    dirty: Vec<bool>,
    succ: Vec<Vec<usize>>,
    /// Each vertex's place in the flattened order; a component's vertices are the places from
    /// its head's to `end[head]`.
    pos: Vec<usize>,
    end: Vec<usize>,
    /// The enclosing component of a component.
    parent: Vec<usize>,
    /// The innermost component holding a vertex (for a head, its own).
    inner: Vec<usize>,
}

impl<L: Lattice> Walk<L> {
    fn number(&mut self, order: &[Element], within: usize, at: &mut usize) {
        for element in order {
            match element {
                Element::Vertex(v) => {
                    self.pos[*v] = *at;
                    self.inner[*v] = within;
                    *at += 1;
                }
                Element::Component { head, body } => {
                    let h = *head;
                    self.pos[h] = *at;
                    self.inner[h] = h;
                    self.parent[h] = within;
                    *at += 1;
                    self.number(body, h, at);
                    self.end[h] = *at - 1;
                }
            }
        }
    }

    fn holds(&self, c: usize, u: usize) -> bool {
        self.pos[c] <= self.pos[u] && self.pos[u] <= self.end[c]
    }

    /// Sets cell `v`; on a change, every component that reads `v` from outside it is dirty.
    fn set(&mut self, v: usize, value: L) {
        if value == self.cells[v] {
            return;
        }
        self.cells[v] = value;
        for i in 0..self.succ[v].len() {
            let mut c = self.inner[self.succ[v][i]];
            while c != NONE && !self.holds(c, v) {
                self.dirty[c] = true;
                c = self.parent[c];
            }
        }
    }

    fn stabilize(&mut self, eq: &impl Equations<L>, order: &[Element]) {
        for element in order {
            match element {
                Element::Vertex(v) => {
                    let next = self.cells[*v].join(&eq.eval(*v, &self.cells));
                    self.set(*v, next);
                }
                Element::Component { head, body } => {
                    let h = *head;
                    if !self.dirty[h] {
                        continue;
                    }
                    for i in 0.. {
                        let next = self.cells[h].join(&eq.eval(h, &self.cells));
                        if i > 0 && next == self.cells[h] {
                            break;
                        }
                        if next != self.cells[h] {
                            let value = self.cells[h].widen(&next, &self.marks);
                            self.set(h, value);
                        }
                        self.stabilize(eq, body);
                    }
                    self.dirty[h] = false;
                }
            }
        }
    }
}

/// Phase 2: rounds of narrowing every cell by its meet with its projection from the state
/// at the start of the round, until a round changes nothing. Each cell's values form a chain
/// of narrowings, which is finite, so the rounds end. Returns the number of rounds that
/// changed a cell.
pub fn narrow<L: Lattice>(eq: &impl Equations<L>, cells: &mut Vec<L>) -> u32 {
    let marks = eq.landmarks();
    for round in 0.. {
        let next: Vec<L> = (0..cells.len())
            .map(|v| cells[v].narrow(&cells[v].meet(&eq.eval(v, cells)), &marks))
            .collect();
        if next == *cells {
            return round;
        }
        *cells = next;
    }
    unreachable!("a chain of narrowings is finite")
}
