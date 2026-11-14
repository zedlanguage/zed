//! The order of a build's checks, evaluations and compilations (DESIGN.md sec:checking_in_zed,
//! "Checks and evaluations on one dependency graph"; plan row SCHED-dep-dag).
//!
//! Every fact of a build is a node: a type, a store bound, a derived facet (iterable nodes), a
//! check's verdict, a value `mix` computes, a compiled region (once nodes). An iterable node has
//! a monotone transfer function over a static list of reads; a strongly connected component of
//! iterable nodes is handed whole to its solver once every read from outside it is final. A
//! once node publishes a result that is never revised: it runs step by step ([`Facts::poll`]),
//! asking for one node at a time, and which node it asks for next may depend on the answers it
//! has. A component that holds a once node is refused ([`Refusal`]).
//!
//! The search is Tarjan's (DESIGN.md \[Tarjan72\]): one depth-first search with an explicit
//! stack, each node visited once and each read walked once, the components emitted as they
//! close, every component a node reads closed before it. A once node is polled with each answer
//! as it comes: a read of a final node is answered at once, a read of an unvisited node descends
//! into it, and a read of a node still on the search stack leaves the once node waiting on it,
//! that read being its one edge in the component. So when a component closes, every read leaving
//! it is final, and it is one of three things: a once node that finished, alone; a component of
//! iterable nodes, which [`Facts::solve`] solves; or a component with a waiting once node, which
//! [`Facts::refuse`] gives its values.
//!
//! The result is a function of the program, not of the order of the roots or of the numbering of
//! the nodes (DESIGN.md, "The meaning, independent of order"). Proof, by induction over the order
//! in which components close: a component closes only when every node it reads outside itself is
//! final, so a once node that finished ran on final answers, the same ones the declarative
//! closure gives it, and a component of iterable nodes is a whole strongly connected component
//! of the static graph (its edges are all walked) with final inputs, as the closure solves it; a
//! component with a waiting once node waits on nothing outside itself, so it is a sink component
//! of the wait graph, which the declarative refusal step refuses. That needs `solve` to depend
//! only on the set of its members and their final inputs, `poll` only on the answers it is
//! given, and the cycle a refusal names to be found from the component's own edges (here, a
//! breadth-first search from the once node of least key, each node's edges in their order). The
//! tests check the engine against an independent implementation of the declarative rounds, over
//! renumberings and root orders (`m0_05_widening_and_iteration::schedule`).
//!
//! It ends: a node gets a number once and is never entered again; an iterable node's reads are
//! walked once, its cursor only moving forward; each poll of a once node finishes it, descends
//! into a new node, or leaves it waiting, so it is polled once per answer. What remains is each
//! `solve`, which ends by the widening of the store (sec:constraints), and each evaluation's
//! `poll`, which ends by its budget. The budget keeps the result one: whether `mix` runs an
//! evaluation is decided from that evaluation's own predicted work and per-call limits (rule 6),
//! so a `poll` stays a function of its answers, as the proof above needs; a total budget shared
//! between evaluations would make one evaluation's value depend on which ran first. It is the
//! most precise: a once node runs only on final values, which no later step raises, so no order
//! that runs it earlier, on values that may still rise, gives it more; a component of iterable
//! nodes receives final inputs, and its own solver decides how precise its solution is.
//!
//! Complexity tradeoff: the naive method runs every step again until nothing changes (a round
//! robin over all nodes, Kildall's worklist, DESIGN.md \[Kildall73\], without an order),
//! O(k (n + e)) for k rounds and k up to n, and it re-runs once nodes, which for an evaluation
//! means running user code again.
//! Used: one depth-first search, O(n + e) for n nodes and e reads, plus the solvers' own work,
//! O((n_C + e_C) · h) per component where h bounds how often a cell can rise, plus one
//! breadth-first search inside each refused component. A once node is polled once per answer, so
//! a node that asks k times costs O(k) here when it keeps its own continuation, as the checker's
//! frame machine does; re-running it from its start for each answer, as a restarting build system
//! does, would cost O(k²). Cost: the search keeps four 32-bit words per node besides its value,
//! and its two stacks. Tests:
//! `m0_05_widening_and_iteration::bench::schedule::scaling`; COMPLEXITY.md row S-sched.

/// What a node is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// A fact with a monotone transfer function over the static reads [`Facts::reads`] gives:
    /// a type, a store bound, a derived facet. It may lie on a cycle of such facts.
    Iterable,
    /// A fact published once and never revised: a verdict, an evaluation, a compiled region.
    /// Its reads are the requests its [`Facts::poll`] makes.
    Once,
}

/// One step of a once node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Poll<V> {
    /// The node's value.
    Ready(V),
    /// The node needs the value of this node next.
    Pending(usize),
}

/// A component that holds a once node, refused: the value of each member is needed to compute
/// itself through a verdict or an evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refusal {
    /// The members, in no particular order.
    pub members: Vec<usize>,
    /// The shortest cycle through the once node of least key, starting there: each node reads
    /// the next, and the last reads the first.
    pub cycle: Vec<usize>,
}

/// The nodes of a build, as the scheduler sees them. The scheduler numbers nothing itself:
/// node `v` is `0..count()`, and an evaluation may add nodes as it runs (the types a schema
/// evaluation makes), raising [`Facts::count`].
pub trait Facts {
    /// A node's value.
    type Value;
    /// What orders nodes where an order must not depend on their numbers: the once node a
    /// refusal's cycle starts at. Two nodes must not have one key.
    type Key: Ord;
    /// How many nodes there are now.
    fn count(&self) -> usize;
    /// Whether node `v` is iterable or once; it does not change.
    fn kind(&self, v: usize) -> Kind;
    /// Node `v`'s key: its place in the text, as the definition it is about and the fact.
    fn key(&self, v: usize) -> Self::Key;
    /// The reads of iterable node `v`, in an order that does not depend on the numbering.
    fn reads(&self, v: usize) -> &[usize];
    /// One step of once node `v`: `None` the first time, then the value of the node its last
    /// step asked for. Called once per request, never again after `Ready`.
    fn poll(&mut self, v: usize, answer: Option<&Self::Value>) -> Poll<Self::Value>;
    /// The values of a strongly connected component of iterable nodes, one per member in the
    /// order given, from the final values of the nodes they read outside it. The result must
    /// depend on the set of members only, not on their order.
    fn solve(&mut self, members: &[usize], done: &Values<Self::Value>) -> Vec<Self::Value>;
    /// The values of a refused component's members, one per member in the order given.
    fn refuse(&mut self, refusal: &Refusal) -> Vec<Self::Value>;
}

/// The final values found so far.
pub struct Values<V> {
    of: Vec<Option<V>>,
}

impl<V> Values<V> {
    /// The value of node `v`, once final.
    pub fn get(&self, v: usize) -> Option<&V> {
        self.of.get(v).and_then(Option::as_ref)
    }
}

/// No node: the number of a node not yet visited, a frame that is not waiting on a child, a
/// node outside the component being refused.
const NONE: u32 = u32::MAX;
/// A member of the component being refused that its breadth-first search has not reached.
const UNREACHED: u32 = u32::MAX - 1;

/// One node the search is in, with where it is in its reads.
#[derive(Clone, Copy)]
struct Frame {
    v: u32,
    /// For an iterable node, the next of its reads to walk. For a once node, 0 until it is
    /// polled the first time and 1 after.
    cursor: u32,
    /// The node the search descended into from here and has not yet come back from, or
    /// [`NONE`].
    child: u32,
}

/// The scheduler: the final values and the search's state, kept across demands so a later
/// demand reuses every value an earlier one made final.
pub struct Schedule<V> {
    values: Values<V>,
    /// Each node's number in the order the search reached it, [`NONE`] before.
    index: Vec<u32>,
    /// Tarjan's lowlink: the least number of a node on the stack that this node reaches by
    /// edges walked so far.
    low: Vec<u32>,
    /// For a once node that is waiting, the node it waits on; [`NONE`] otherwise.
    waits: Vec<u32>,
    /// During a refusal, each member's breadth-first parent, [`UNREACHED`] for a member not
    /// reached yet; [`NONE`] for every other node and at every other time.
    mark: Vec<u32>,
    /// Tarjan's stack: the nodes reached whose component has not closed. A node is on it
    /// exactly when it has a number and no value, so no flag is kept.
    stack: Vec<u32>,
    /// The search's own stack, in place of recursion, so a long chain of reads cannot overflow
    /// the thread's stack.
    calls: Vec<Frame>,
    next_index: u32,
}

impl<V> Default for Schedule<V> {
    fn default() -> Self {
        Schedule::new()
    }
}

/// `v` as a node number of the search's arrays.
fn node(v: usize) -> u32 {
    let n = u32::try_from(v).expect("a build has fewer than 2^32 - 2 facts");
    assert!(n < UNREACHED, "a build has fewer than 2^32 - 2 facts");
    n
}

impl<V> Schedule<V> {
    /// A scheduler with no node final.
    pub fn new() -> Self {
        Schedule {
            values: Values { of: Vec::new() },
            index: Vec::new(),
            low: Vec::new(),
            waits: Vec::new(),
            mark: Vec::new(),
            stack: Vec::new(),
            calls: Vec::new(),
            next_index: 0,
        }
    }

    /// The final values.
    pub fn values(&self) -> &Values<V> {
        &self.values
    }

    /// Makes node `root` final, and every node it reads.
    pub fn demand<F: Facts<Value = V>>(&mut self, facts: &mut F, root: usize) {
        self.grow(facts.count());
        assert!(root < self.index.len(), "node {root} does not exist");
        if self.is_final(root) {
            return;
        }
        // Between demands the search's stacks are empty, so a node without a value has no
        // number either.
        self.enter(node(root));
        while let Some(&Frame { v, .. }) = self.calls.last() {
            match facts.kind(v as usize) {
                Kind::Iterable => self.step_iterable(facts),
                Kind::Once => self.step_once(facts),
            }
        }
    }

    /// [`Schedule::demand`] for each root in turn: the build demands every definition in the
    /// order of the text.
    pub fn run<F: Facts<Value = V>>(
        &mut self,
        facts: &mut F,
        roots: impl IntoIterator<Item = usize>,
    ) {
        for r in roots {
            self.demand(facts, r);
        }
    }

    /// Makes room for the nodes an evaluation added.
    fn grow(&mut self, count: usize) {
        if self.index.len() < count {
            node(count - 1);
            self.values.of.resize_with(count, || None);
            self.index.resize(count, NONE);
            self.low.resize(count, NONE);
            self.waits.resize(count, NONE);
            self.mark.resize(count, NONE);
        }
    }

    fn is_final(&self, v: usize) -> bool {
        self.values.of[v].is_some()
    }

    /// A read of node `u`, checked to exist.
    fn read<F: Facts<Value = V>>(&mut self, facts: &F, from: u32, u: usize) -> u32 {
        self.grow(facts.count());
        assert!(
            u < self.index.len(),
            "node {from} reads node {u}, which does not exist"
        );
        node(u)
    }

    fn enter(&mut self, v: u32) {
        let i = self.next_index;
        self.next_index += 1;
        self.index[v as usize] = i;
        self.low[v as usize] = i;
        self.stack.push(v);
        self.calls.push(Frame {
            v,
            cursor: 0,
            child: NONE,
        });
    }

    /// Walks the reads of the iterable node on top of the search, from where it stopped, until
    /// one needs a descent or none is left.
    fn step_iterable<F: Facts<Value = V>>(&mut self, facts: &mut F) {
        let top = self.calls.len() - 1;
        let Frame { v, cursor, child } = self.calls[top];
        let vu = v as usize;
        if child != NONE {
            self.calls[top].child = NONE;
            if !self.is_final(child as usize) {
                // The child's component is still open, so it holds a node on the stack below
                // `v`, or `v` itself: the tree edge of Tarjan's search.
                self.low[vu] = self.low[vu].min(self.low[child as usize]);
            }
        }
        let count = facts.reads(vu).len();
        let mut i = cursor as usize;
        while i < count {
            let r = facts.reads(vu)[i];
            i += 1;
            let u = self.read(facts, v, r);
            let uu = u as usize;
            if self.is_final(uu) {
                continue;
            }
            if self.index[uu] == NONE {
                self.calls[top].cursor = node(i);
                self.calls[top].child = u;
                self.enter(u);
                return;
            }
            // On the stack: the back or cross edge of Tarjan's search.
            self.low[vu] = self.low[vu].min(self.index[uu]);
        }
        self.finish(facts, v, None);
    }

    /// Polls the once node on top of the search with each answer it can have now, until it
    /// finishes, needs a descent, or waits on a node on the stack.
    fn step_once<F: Facts<Value = V>>(&mut self, facts: &mut F) {
        let top = self.calls.len() - 1;
        let Frame { v, cursor, child } = self.calls[top];
        let vu = v as usize;
        let mut step = if child != NONE {
            self.calls[top].child = NONE;
            let c = child as usize;
            match self.values.of[c].as_ref() {
                Some(answer) => facts.poll(vu, Some(answer)),
                None => {
                    self.low[vu] = self.low[vu].min(self.low[c]);
                    self.waits[vu] = child;
                    self.finish(facts, v, None);
                    return;
                }
            }
        } else {
            debug_assert_eq!(
                cursor, 0,
                "a once node on top of the search is new or back from a child"
            );
            self.calls[top].cursor = 1;
            facts.poll(vu, None)
        };
        loop {
            match step {
                Poll::Ready(value) => {
                    self.finish(facts, v, Some(value));
                    return;
                }
                Poll::Pending(r) => {
                    let u = self.read(facts, v, r);
                    let uu = u as usize;
                    if let Some(answer) = self.values.of[uu].as_ref() {
                        step = facts.poll(vu, Some(answer));
                        continue;
                    }
                    if self.index[uu] == NONE {
                        self.calls[top].child = u;
                        self.enter(u);
                        return;
                    }
                    self.low[vu] = self.low[vu].min(self.index[uu]);
                    self.waits[vu] = u;
                    self.finish(facts, v, None);
                    return;
                }
            }
        }
    }

    /// Leaves node `v`; if it is the first node of its component, the component closes and gets
    /// its values. `ready` is the value of a once node that finished.
    fn finish<F: Facts<Value = V>>(&mut self, facts: &mut F, v: u32, ready: Option<V>) {
        self.calls.pop();
        let vu = v as usize;
        if self.low[vu] != self.index[vu] {
            // A once node that finished read only final nodes, so it is the first node of its
            // own component.
            debug_assert!(
                ready.is_none(),
                "a finished once node closes its own component"
            );
            return;
        }
        let at = self
            .stack
            .iter()
            .rposition(|&m| m == v)
            .expect("a node being left is on the stack");
        let members: Vec<usize> = self.stack.drain(at..).map(|m| m as usize).collect();
        let values = match ready {
            Some(value) => {
                debug_assert_eq!(
                    members,
                    [vu],
                    "a finished once node is alone in its component"
                );
                vec![value]
            }
            None if members.iter().all(|&m| facts.kind(m) == Kind::Iterable) => {
                facts.solve(&members, &self.values)
            }
            None => {
                let cycle = self.cycle(facts, &members);
                facts.refuse(&Refusal {
                    members: members.clone(),
                    cycle,
                })
            }
        };
        assert_eq!(
            values.len(),
            members.len(),
            "one value per member of a component"
        );
        for (m, value) in members.into_iter().zip(values) {
            self.values.of[m] = Some(value);
        }
    }

    /// The shortest cycle through the once member of least key of a component being refused,
    /// starting there: a breadth-first search over the component's own edges, each node's edges
    /// in their order, the first edge back to the start ending it. Every member waits only on
    /// members or on final nodes, and the component is strongly connected, so a cycle exists.
    fn cycle<F: Facts<Value = V>>(&mut self, facts: &F, members: &[usize]) -> Vec<usize> {
        let start = members
            .iter()
            .copied()
            .filter(|&m| facts.kind(m) == Kind::Once)
            .min_by(|&a, &b| facts.key(a).cmp(&facts.key(b)))
            .expect("a refused component holds a once node");
        for &m in members {
            self.mark[m] = UNREACHED;
        }
        self.mark[start] = node(start);
        let mut queue: Vec<usize> = Vec::with_capacity(members.len());
        queue.push(start);
        let mut head = 0;
        let mut back = None;
        'search: while head < queue.len() {
            let x = queue[head];
            head += 1;
            let waits = [self.waits[x] as usize];
            let edges: &[usize] = match facts.kind(x) {
                Kind::Iterable => facts.reads(x),
                Kind::Once => &waits,
            };
            for &y in edges {
                if y == start {
                    back = Some(x);
                    break 'search;
                }
                if self.mark[y] == UNREACHED {
                    self.mark[y] = node(x);
                    queue.push(y);
                }
            }
        }
        let mut cycle = Vec::new();
        let mut x = back.expect("a refused component is strongly connected");
        while x != start {
            cycle.push(x);
            x = self.mark[x] as usize;
        }
        cycle.push(start);
        cycle.reverse();
        for &m in members {
            self.mark[m] = NONE;
        }
        cycle
    }
}
