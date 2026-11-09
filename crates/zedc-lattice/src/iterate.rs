//! The store's iteration strategy (DESIGN.md sec:constraints rule 1, fixed by step M0.5).
//!
//! Phase 1 computes a post-fixpoint by forward projections only: Bourdoncle's recursive
//! strategy over the weak topological order of the dependency graph, joining at every cell
//! and widening at the heads of components. Phase 2 then narrows that post-fixpoint in rounds:
//! in each round every cell is narrowed by its meet with its projection computed from the
//! state at the start of the round, until a round changes nothing. Both phases end because
//! the widening and the narrowing move bounds only to landmarks and to values already present
//! (module `lattice`), so no delay, no bound on a head's changes and no budget of rounds
//! enters. A cell's landmarks are those of its loop ([`Scopes`]), so a head stops only at
//! values written in its loop.
//!
//! The specification of these rules is prelude source, `zed/prelude/iteration.zed`; this
//! module is the Rust-hosted checker's copy.

use super::landmarks::Landmarks;
use super::lattice::Lattice;
use super::wto::{Element, SameKey, Tie, VertexKey, ordered_by};
use zedc_syntax::lex::Span;

/// A system of equations over a lattice: one cell per vertex, `0..n`. The numbering does not
/// enter the result: the order of iteration comes from the cells' keys.
pub trait Equations<L: Lattice> {
    /// The canonical form of a cell's static node, the third part of its key.
    type Form: Ord;
    /// The keypath of a cell's fact address, the fourth and last part of its key.
    type Keypath: Ord;
    /// For each cell, the cells its projection reads.
    fn reads(&self) -> &[Vec<usize>];
    /// What the traversal orders cell `v` by: the name the unit's address hashes for its
    /// binding (a declaration's written name, a local binder's de Bruijn level), the content
    /// address of its static node, that node's canonical form and the keypath of its fact
    /// address (DESIGN.md step M0.5). A cell of a local binding must not be keyed by the
    /// written name: two units with one address would then get two verdicts.
    fn key(&self, v: usize) -> VertexKey<'_, Self::Form, Self::Keypath>;
    /// Where cell `v`'s static node is written, for the refusal of two cells with one key;
    /// the order never reads it.
    fn span(&self, v: usize) -> Span;
    /// The forward projection into cell `v` from the current cells.
    fn eval(&self, v: usize, cells: &[L]) -> L;
    /// The values written in the equation of cell `v`, where a widening or a narrowing may
    /// stop a bound.
    fn landmarks(&self, v: usize) -> Landmarks;
}

/// The dependency graph: an edge from `u` to every cell that reads `u`, the successors in
/// increasing number.
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

/// The weak topological order of the system's dependency graph, the traversal visiting the
/// cells in the order of their keys; refused, with the spans of both, when two cells have one
/// key.
pub fn order<L: Lattice>(eq: &impl Equations<L>) -> Result<Vec<Element>, SameKey> {
    let keys: Vec<_> = (0..eq.reads().len()).map(|v| eq.key(v)).collect();
    ordered_by(&dependency_graph(eq.reads()), &keys).map_err(|Tie(u, w)| SameKey {
        cells: [u, w],
        spans: [eq.span(u), eq.span(w)],
    })
}

/// Phase 1 and then phase 2, from every cell at the bottom, over [`order`].
///
/// The result is a post-fixpoint: each cell holds its projection from the result. For a loop
/// cell whose projection joins its start with its step, the cell is therefore an inductive
/// invariant, holding the start and closed under one step, so it holds at every iteration and
/// not only once the values settle. Phase 1 leaves a head only when joining its projection
/// changes nothing; each narrowing of phase 2 lies between the meet with the projection and
/// the old element, and for monotone projections that keeps a post-fixpoint one. Tests:
/// `m0_05_widening_and_iteration::invariant` (item RANGE-invariant-audit).
pub fn solve<L: Lattice>(eq: &impl Equations<L>) -> Result<Vec<L>, SameKey> {
    let order = order(eq)?;
    let mut cells = phase1(eq, &order);
    narrow(eq, &order, &mut cells);
    Ok(cells)
}

/// The landmarks each cell's widening and narrowing take (COMPLEXITY.md S13). A cell in a
/// loop takes those of every equation of its innermost component, nested components included,
/// since a guard of an inner loop bounds what flows out to the heads around it; a cell in no
/// loop takes those of its own equation. So a head stops only at values written in its loop,
/// not at every literal of the program. Building them takes time and space linear in the sum,
/// over the components, of the landmarks each holds, which is at most the landmarks times the
/// depth of nesting.
///
/// Complexity tradeoff: the standard choice gives every cell all `L` literals of the program
/// as landmarks, so a head may stop at each, `3L + 1` evaluations per head whatever its loop
/// writes. Used: each cell takes the landmarks of its innermost component, nested ones
/// included, so a head's evaluations follow the literals of its loop (5 for a counter beside
/// 1 to 128 other literals). Cost: the sets take memory up to `L` times the nesting depth,
/// since an outer component holds its inner ones' landmarks again. Precision: a head no longer
/// stops at a literal written outside its loop, so its widening may pass a value such a
/// literal would have stopped it at (inferred from the code, not measured). Tests:
/// `m0_05_widening_and_iteration::scaling::a_head_takes_only_the_landmarks_of_its_loop` and
/// `a_head_stops_at_most_once_per_landmark`; COMPLEXITY.md row S13.
pub struct Scopes {
    sets: Vec<Landmarks>,
    /// The set of each cell.
    of: Vec<usize>,
}

impl Scopes {
    /// The sets of the cells, for the order of the system's dependency graph.
    pub fn new<L: Lattice>(eq: &impl Equations<L>, order: &[Element]) -> Self {
        let mut s = Scopes {
            sets: Vec::new(),
            of: vec![0; eq.reads().len()],
        };
        for element in order {
            match element {
                Element::Vertex(v) => {
                    s.of[*v] = s.sets.len();
                    s.sets.push(eq.landmarks(*v));
                }
                Element::Component { head, body } => {
                    s.component(eq, *head, body);
                }
            }
        }
        s
    }

    /// Gives the component headed by `head`, and each one inside it, its set, and returns the
    /// index of its own.
    fn component<L: Lattice>(
        &mut self,
        eq: &impl Equations<L>,
        head: usize,
        body: &[Element],
    ) -> usize {
        let mut marks = eq.landmarks(head);
        let mut direct = vec![head];
        for element in body {
            match element {
                Element::Vertex(v) => {
                    marks.extend(&eq.landmarks(*v));
                    direct.push(*v);
                }
                Element::Component { head, body } => {
                    let inner = self.component(eq, *head, body);
                    marks.extend(&self.sets[inner]);
                }
            }
        }
        let i = self.sets.len();
        for v in direct {
            self.of[v] = i;
        }
        self.sets.push(marks);
        i
    }

    /// The landmarks of cell `v`.
    pub fn of(&self, v: usize) -> &Landmarks {
        &self.sets[self.of[v]]
    }
}

/// Phase 1 over the given order, from every cell at the bottom.
pub fn phase1<L: Lattice>(eq: &impl Equations<L>, order: &[Element]) -> Vec<L> {
    let n = eq.reads().len();
    let mut w = Walk {
        cells: vec![L::bottom(); n],
        marks: Scopes::new(eq, order),
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
///
/// Complexity tradeoff: the standard recursive strategy stabilizes every inner component
/// again at each change of an enclosing head, exponential in the nesting depth `h` (64^h
/// with the old head counters). Used: a component is skipped while no cell it reads from
/// outside has changed, so it is stabilized once per such change, work linear in the
/// number of loops for a nest. Cost of the skip: a `dirty` flag per vertex, and a change of a
/// cell marks the components between each reader and the common enclosing component, `O(d)`
/// per edge for nesting depth `d`. No result changes (a clean component is already a
/// post-fixpoint of its equations; the stack-machine oracle agrees). Tests:
/// `m0_05_widening_and_iteration::scaling::nested_loops_cost_linear_work_in_the_depth` and
/// `the_nest_scales`; COMPLEXITY.md row S3.
struct Walk<L> {
    cells: Vec<L>,
    marks: Scopes,
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
        debug_assert!(self.cells[v].leq(&value), "phase 1 fell at cell {v}");
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
                            let value = self.cells[h].widen(&next, self.marks.of(h));
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
/// changed a cell. `order` is the order of the system's dependency graph, which places the
/// landmarks.
pub fn narrow<L: Lattice>(eq: &impl Equations<L>, order: &[Element], cells: &mut Vec<L>) -> u32 {
    let marks = Scopes::new(eq, order);
    for round in 0.. {
        let next: Vec<L> = (0..cells.len())
            .map(|v| cells[v].narrow(&cells[v].meet(&eq.eval(v, cells)), marks.of(v)))
            .collect();
        debug_assert!(
            next.iter().zip(cells.iter()).all(|(n, c)| n.leq(c)),
            "phase 2 rose"
        );
        if next == *cells {
            return round;
        }
        *cells = next;
    }
    unreachable!("a chain of narrowings is finite")
}
