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
//! The search is Tarjan's (DESIGN.md \[Tarjan72\]), the workspace's one copy of it
//! ([`zed_graph::Search`]), run again for each demand on the graph as it has grown: one
//! depth-first search with an explicit stack, each node visited once and each read walked once, the components emitted as they
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
//! does, would cost O(k²). Cost: per node besides its value, one 64-bit word in the search (its
//! number, or that its component is found) and two 32-bit words here (`waits`, `mark`), 16
//! bytes, as the four 32-bit words of this module's own copy of the search took before
//! GRAPH-lazy-tarjan; and the search's two stacks. Tests:
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

/// No node: a once node that is not waiting, a node outside the component being refused.
const NONE: u32 = u32::MAX;
/// A member of the component being refused that its breadth-first search has not reached.
const UNREACHED: u32 = u32::MAX - 1;

/// Where the search is in the reads of a node on its path ([`zed_graph::Walk::At`]).
#[derive(Default)]
struct At {
    /// For an iterable node, the place of the next of its reads to walk.
    read: usize,
    /// For a once node, the node its last step asked for, once it is polled; `None` before.
    asked: Option<u32>,
}

/// The scheduler: the final values and the search's state, kept across demands so a later
/// demand reuses every value an earlier one made final.
pub struct Schedule<V> {
    values: Values<V>,
    /// For a once node that is waiting, the node it waits on; [`NONE`] otherwise.
    waits: Vec<u32>,
    /// During a refusal, each member's breadth-first parent, [`UNREACHED`] for a member not
    /// reached yet; [`NONE`] for every other node and at every other time.
    mark: Vec<u32>,
    /// Tarjan's search, on an explicit stack in place of recursion, so a long chain of reads
    /// cannot overflow the thread's stack. A node is on its stack exactly when it has a number
    /// and no value. It is run again for each demand: a node it found in an earlier one is
    /// final and is passed over.
    search: zed_graph::Search<At>,
}

impl<V> Default for Schedule<V> {
    fn default() -> Self {
        Schedule::new()
    }
}

/// `v` as a node number of the arrays `waits` and `mark`.
fn node(v: usize) -> u32 {
    zed_collections::index::to_u32_below(v, UNREACHED, "facts in a build")
}

impl<V> Schedule<V> {
    /// A scheduler with no node final.
    pub fn new() -> Self {
        Schedule {
            values: Values { of: Vec::new() },
            waits: Vec::new(),
            mark: Vec::new(),
            search: zed_graph::Search::new(),
        }
    }

    /// The final values.
    pub fn values(&self) -> &Values<V> {
        &self.values
    }

    /// Makes node `root` final, and every node it reads.
    // Complexity tradeoff: the search is the workspace's one Tarjan search
    // ([`zed_graph::Search`], GRAPH-lazy-tarjan), run again for each demand on the graph as it
    // has grown, in place of a copy of it here; each run reads only nodes no earlier one
    // reached, so all the demands together cost O(n + e), as the copy did. The naive method, a
    // search from scratch per demand, costs O(n + e) per demand.
    pub fn demand<F: Facts<Value = V>>(&mut self, facts: &mut F, root: usize) {
        let mut walk = Demand {
            facts,
            values: &mut self.values,
            waits: &mut self.waits,
            mark: &mut self.mark,
            ready: None,
        };
        walk.grow();
        assert!(root < walk.values.of.len(), "node {root} does not exist");
        if walk.values.get(root).is_some() {
            return;
        }
        // Between demands the search's stack is empty, so a node without a value has no
        // number either.
        self.search.run(&mut walk, [root]);
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
}

/// One demand's walk over the reads of the nodes, as [`zed_graph::Search`] reads them.
struct Demand<'s, F: Facts> {
    facts: &'s mut F,
    values: &'s mut Values<F::Value>,
    waits: &'s mut Vec<u32>,
    mark: &'s mut Vec<u32>,
    /// The value of the once node that just finished, with the node, until its component,
    /// which is that node alone, gets it.
    ready: Option<(usize, F::Value)>,
}

impl<F: Facts> Demand<'_, F> {
    /// Makes room for the nodes an evaluation added.
    fn grow(&mut self) {
        let count = self.facts.count();
        if self.values.of.len() < count {
            node(count - 1);
            self.values.of.resize_with(count, || None);
            self.waits.resize(count, NONE);
            self.mark.resize(count, NONE);
        }
    }

    /// A read of node `u` by node `from`, checked to exist.
    fn read(&mut self, from: usize, u: usize) -> usize {
        self.grow();
        assert!(
            u < self.values.of.len(),
            "node {from} reads node {u}, which does not exist"
        );
        u
    }

    /// The shortest cycle through the once member of least key of a component being refused,
    /// starting there: a breadth-first search over the component's own edges, each node's edges
    /// in their order, the first edge back to the start ending it. Every member waits only on
    /// members or on final nodes, and the component is strongly connected, so a cycle exists.
    fn cycle(&mut self, members: &[usize]) -> Vec<usize> {
        let facts = &*self.facts;
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

impl<F: Facts> zed_graph::Walk for Demand<'_, F> {
    type At = At;

    /// The next node `v` reads that is not final. An iterable node walks its reads from where
    /// it stopped; a once node is polled with each answer it can have now, until it finishes,
    /// asks for a node that is not final, or waits on one.
    fn next(&mut self, v: usize, at: &mut At) -> Option<usize> {
        if self.facts.kind(v) == Kind::Iterable {
            while let Some(&r) = self.facts.reads(v).get(at.read) {
                at.read += 1;
                let u = self.read(v, r);
                if self.values.get(u).is_none() {
                    return Some(u);
                }
            }
            return None;
        }
        let mut step = match at.asked {
            None => self.facts.poll(v, None),
            Some(u) => match self.values.of[u as usize].as_ref() {
                Some(answer) => self.facts.poll(v, Some(answer)),
                None => {
                    // The node asked for is on the search's stack: `v` waits on it, that read
                    // being its one edge in its component.
                    self.waits[v] = u;
                    return None;
                }
            },
        };
        loop {
            match step {
                Poll::Ready(value) => {
                    self.ready = Some((v, value));
                    return None;
                }
                Poll::Pending(r) => {
                    let u = self.read(v, r);
                    if let Some(answer) = self.values.of[u].as_ref() {
                        step = self.facts.poll(v, Some(answer));
                        continue;
                    }
                    at.asked = Some(node(u));
                    return Some(u);
                }
            }
        }
    }

    /// Gives a component its values: a once node that finished, alone, its value; a component
    /// of iterable nodes what [`Facts::solve`] gives; a component with a waiting once node what
    /// [`Facts::refuse`] gives.
    fn found(&mut self, members: &mut [usize], _from: Option<usize>) {
        let members = &*members;
        let values = match self.ready.take() {
            Some((v, value)) => {
                // A once node that finished read only final nodes, so it is the first node of
                // its own component.
                debug_assert_eq!(
                    members,
                    [v],
                    "a finished once node is alone in its component"
                );
                vec![value]
            }
            None if members
                .iter()
                .all(|&m| self.facts.kind(m) == Kind::Iterable) =>
            {
                self.facts.solve(members, self.values)
            }
            None => {
                let cycle = self.cycle(members);
                self.facts.refuse(&Refusal {
                    members: members.to_vec(),
                    cycle,
                })
            }
        };
        assert_eq!(
            values.len(),
            members.len(),
            "one value per member of a component"
        );
        for (&m, value) in members.iter().zip(values) {
            self.values.of[m] = Some(value);
        }
    }
}
