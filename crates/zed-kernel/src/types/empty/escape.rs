//! The escape solve (round 6): the difference `P \ (N_1 | .. | N_r)` of list types of integers
//! that the prefix-chain sweep ([`super::Searching::find_prefix_chains`]) leaves open, decided
//! by 2-SAT over the places of one length.
//!
//! The class, read from the type alone. `t` has atoms only, one atom name `link` with a payload
//! and no bare atom; the payload is pairs only, a clause of rows (taken rows `P_i`, refused rows
//! `N_k`, at least one of each, the payload exactly their meet less their union). Every row
//! head is a set of integers (finite, or cofinite within the integers; arbitrary-width integer values). From
//! each row tail, the types reached by [`super::list_step`] are *nodes*: a *cons* node
//! `stop? | link(h, next)` with `h` a set of integers and `next` a node other than itself, an
//! *end* node (the bare `stop` atom alone), or the *carrier* `L = stop | link(H, L)`, at most
//! one, with `H` a set of integers. One stop name throughout; no cycle but the carrier's. At
//! most one taken row has a tail other than the carrier. Recognizing the class reads each
//! distinct node once: O(size of the types) set operations.
//!
//! The semantics. A list `x_1 .. x_l` is in a row `(h, s)` when `x_1 ∈ h` and the node reached
//! from `s` after `j - 2` links holds `x_j` in its head for `j = 2 .. l` (at the carrier the
//! head is `H`) and the node reached after `l - 1` links holds the empty list (a stop, the end,
//! or the carrier). The taken rows fix the shortest length `l0` they all hold and a set `p_j`
//! for each place (the meet of their heads). For a refused row `N` that holds the length `l0`,
//! the *cell* at place `j` is `p_j \ head_N(j)`: empty when the place does not separate, all of
//! `p_j` when it kills `N` (no list of `P` of length at least `j` is in `N`), else an *atom*: a
//! list of `P` of length `l0` escapes `N` exactly when some `x_j` is in one of `N`'s atoms.
//!
//! Lemma (truncation). If (E3) the taken rows hold no length above `l0`, or (E1) every `p_j`
//! with `j >= 2` (over the whole positive chain) lies in `H` and (E2) every refused row that
//! holds `l0` and is not killed reaches the carrier within `l0 - 1` links, then `t` has a value
//! exactly when it has one of length `l0`. Proof: lengths below `l0` are not in `P`. Let `w`
//! of length `l > l0` be in `t`. Under E3 there is no such `w`. Else its first `l0` items `w'`
//! are in every taken row (each holds `l0` with the same heads on places `1 .. l0`, the carrier
//! rows any length with heads `H ⊇ p_j`). If `w'` were in a refused row `N`, then `N` holds
//! `l0` and is not killed (a kill at `j <= l0` excludes `w` too), so by E2 `N` is at the carrier
//! from place `l0 + 1` on, whose head `H` holds every later item of `w` (E1), and the carrier
//! holds every length: `w ∈ N`, a contradiction. So `w'` is in `t`.
//!
//! The solve at length `l0`. Each place takes one value, and all literals are positive ("x_j in
//! atom A"), so a list escapes every refused row exactly when a choice of at most one atom per
//! place, each pair of chosen atoms at a place sharing a value, meets every row. When the atoms
//! at each place form a laminar family (any two nested or disjoint) and every row has at most
//! two atoms, this is 2-SAT: a variable `z_A` per distinct atom, `z_A -> z_parent(A)` along the
//! forest, at most one true among the children of each atom and among the forest roots (the
//! ladder encoding, linear), one clause `z_A | z_B` per row. A model makes the true atoms of a
//! place one chain from a forest root; any value of its deepest atom is in each of them. A row
//! with no atom and no kill holds every list of `P` of length `l0`.
//!
//! The answers. `Inhabited` only with a list built from a model and checked by
//! [`super::Searching::check_chain_witness`], which reads none of this module's tables; the
//! hints it gets (for each refused row, an item it should miss) are checked against its own
//! parse and fall back to its full walk when they do not hold. `Empty` only when the truncation
//! lemma holds and (every taken length is missing, or a row has no atom and no kill, or the
//! 2-SAT has no model with every row's atoms all kept). A row with three or more atoms keeps its
//! first two (by place) and then the solve may answer only `Inhabited`. Atoms that are not
//! laminar at some place: `None` (two atoms per row with crossing atoms is NP-hard, by a
//! reduction from 3-colouring). `None` sends the type to the search, as before this module.
//!
//! The cost. Recognizing the class and the positive chain: O(size) set operations. The cells
//! are found from the nodes' side: a node `v` at height `ht(v)` (links to its terminal) is at
//! place `ht(s_N) - ht(v) + 2` of each refused row `N` whose tail `s_N` lies below it (an Euler
//! interval). The cons nodes are read from the highest down, so each row meets its places in
//! increasing order, and a row stops being read once it is killed, once it has three atoms, or
//! once the nodes left are past its length `l0`: each row takes at most four cells. At each
//! node the cells are read from whichever side lists fewer: the rows still read below `v`
//! (skipping pointers and a Fenwick count), or the places that can separate at `v`, from an
//! index of the places by value (a cofinite head `int \ X` separates exactly the places whose
//! `p_j` meets `X`; a finite head the places with a value outside it, read between its
//! values), each place then giving its rows at one height by binary search. The work is
//! O((nodes + rows + cells + W) log) plus the 2-SAT, linear in the cells, where W is the sum
//! over the nodes of the reads that find no cell, at most `min(rows below v, places that can
//! separate at v)` for each `v`. The height-congruence filter below makes W zero on
//! `r6parity`: its equal-parity tail heights reach only places whose positive values avoid the
//! node's hole. The old enumerator read n^2 / 8 empty cells there. This is a sufficient
//! skip test, not a bound on W for every input of this class; irregular root heights can
//! still defeat it. A general O(n log n) bound on nonempty alignment discovery is open.
// Complexity tradeoff: the search (`Searching::solve` with its tuple boxes) decides these types
// by narrowing the tail of every refused row at every depth, `Θ(n^2)` or a refusal at a fork
// (`r5sat1lit`, `r5sat2lit`, `r5satk1n`, `r5slotsout`, `r5remout`, rounds 5 and 6); used: one
// length, the cells read from the nodes' side with each row retired after four cells, 2-SAT.
// Given up: a row with three or more atoms is cut to two, so its `Empty` goes back to the
// search (3-SAT, NP-hard), and non-laminar atoms go back whole (NP-hard as above); the reads
// that find no cell after the congruence filter are not bounded in general. Trigger:
// `find_prefix_chains` returns `None` on a type of this class.

use std::collections::{BTreeSet, HashMap, HashSet};

use super::super::{Lits, Parts, Row, Type};
use super::shared::{ByType, ChainHint, ChainPlan, Digests, TwoSat, list_step};
use crate::value::Value;

/// A set of integers: `vals` when not `cof`, else the integers less `vals`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Ints {
    cof: bool,
    vals: BTreeSet<Value>,
}

impl Ints {
    /// The integer set of `t`, if `t` holds integers and nothing else. Wide integers
    /// (`Value::Big`) are kept as values too: the escape only compares and hashes them (round 10).
    fn of(t: &Type) -> Option<Ints> {
        let p = t.p();
        if !only_ints(&p) {
            return None;
        }
        let mut vals = BTreeSet::new();
        for v in p.ints.values.iter() {
            match v {
                v @ (Value::Int(_) | Value::Big(_)) => {
                    vals.insert(v.clone());
                }
                _ => return None,
            }
        }
        Some(Ints {
            cof: p.ints.cofinite,
            vals,
        })
    }

    fn is_empty(&self) -> bool {
        !self.cof && self.vals.is_empty()
    }

    /// Whether `self ⊆ o`.
    fn subset(&self, o: &Ints) -> bool {
        match (self.cof, o.cof) {
            (false, false) => self.vals.iter().all(|x| o.vals.contains(x)),
            (false, true) => self.vals.iter().all(|x| !o.vals.contains(x)),
            (true, false) => false,
            (true, true) => o.vals.iter().all(|x| self.vals.contains(x)),
        }
    }

    /// Whether `self ∩ o` is empty.
    fn disjoint(&self, o: &Ints) -> bool {
        match (self.cof, o.cof) {
            (false, _) => self.vals.iter().all(|x| o.cof == o.vals.contains(x)),
            (true, false) => o.disjoint(self),
            (true, true) => false,
        }
    }

    fn meet(&self, o: &Ints) -> Ints {
        match (self.cof, o.cof) {
            (false, _) => Ints {
                cof: false,
                vals: self
                    .vals
                    .iter()
                    .filter(|x| o.cof != o.vals.contains(x))
                    .cloned()
                    .collect(),
            },
            (true, false) => o.meet(self),
            (true, true) => Ints {
                cof: true,
                vals: self.vals.union(&o.vals).cloned().collect(),
            },
        }
    }

    /// `self \ o`.
    fn minus(&self, o: &Ints) -> Ints {
        match (self.cof, o.cof) {
            (false, _) => Ints {
                cof: false,
                vals: self
                    .vals
                    .iter()
                    .filter(|x| o.cof == o.vals.contains(x))
                    .cloned()
                    .collect(),
            },
            (true, false) => Ints {
                cof: true,
                vals: self.vals.union(&o.vals).cloned().collect(),
            },
            (true, true) => Ints {
                cof: false,
                vals: o.vals.difference(&self.vals).cloned().collect(),
            },
        }
    }

    /// One value of a set that is not empty: its least value, or the least natural number
    /// not excluded.
    fn pick(&self) -> Value {
        if !self.cof {
            return self.vals.iter().next().expect("not empty").clone();
        }
        (0..)
            .map(Value::Int)
            .find(|x| !self.vals.contains(x))
            .expect("a cofinite set has a natural number")
    }
}

/// Whether `p` holds integers only (or nothing).
fn only_ints(p: &Parts) -> bool {
    p.bools == 0
        && [&p.rats, &p.floats, &p.strings]
            .iter()
            .all(|l: &&Lits| !l.cofinite && l.values.is_empty())
        && !p.structs
        && p.morphisms.is_leaf() == Some(false)
        && p.tuples.is_default()
        && !p.atoms.cofinite
        && p.atoms
            .names
            .values()
            .all(|a| !a.bare && a.payload == Type::empty())
}

/// A node of the class: `next` is `None` at a terminal (the end, or the carrier).
struct Node {
    /// Whether the node holds the empty list.
    stop: bool,
    /// The head; the carrier's for the carrier, empty at the end.
    head: Ints,
    next: Option<usize>,
    carrier: bool,
    /// Links to the terminal.
    ht: usize,
}

/// The nodes reached from row tails, each read once.
struct Nodes {
    nodes: Vec<Node>,
    of: ByType<usize>,
    stop: Option<std::sync::Arc<str>>,
    link: std::sync::Arc<str>,
    carrier: Option<(Type, usize)>,
    alphabet: Option<BTreeSet<Value>>,
    heads: ByType<Option<Ints>>,
}

/// A finite alphabet containing every item of every positive row, if their
/// written chains prove one. The actual parser still checks all terminals,
/// names and cycles. Every node and head Type is visited once.
// Complexity tradeoff: copying n shared width-w head predicates and scanning
// their irrelevant holes at every node costs Theta(n*w). Read the positive
// alphabet once, O(V+E+L log(2+A)) for L listed positive literals and A
// alphabet values, and project each distinct
// integer head onto it. Projection preserves every cell because each positive
// place is a subset of this alphabet. Cofinite positive heads decline this
// optional optimization; they keep the existing parser and finder.
fn finite_positive_alphabet(rows: &[Row]) -> Option<BTreeSet<Value>> {
    let mut pending: Vec<Type> = rows.iter().map(|r| r[1].clone()).collect();
    let mut seen = ByType::with_hasher(Digests::new());
    let mut seen_heads = ByType::with_hasher(Digests::new());
    let mut alphabet = BTreeSet::new();
    let mut add_head = |h: &Type| -> Option<()> {
        if seen_heads.insert(h.clone(), ()).is_some() {
            return Some(());
        }
        let p = h.p();
        if !only_ints(&p) || p.ints.cofinite {
            return None;
        }
        alphabet.extend(p.ints.values.iter().cloned());
        Some(())
    };
    for row in rows {
        add_head(&row[0])?;
    }
    while let Some(t) = pending.pop() {
        if seen.insert(t.clone(), ()).is_some() {
            continue;
        }
        if let Some((_, _, h, next)) = list_step(&t) {
            add_head(&h)?;
            pending.push(next);
        } else {
            // Complexity tradeoff: continuing after k unknown positives could
            // reread a shared width-w diagram k times, O(k*w). Stop this
            // optional prepass at its first mismatch, O(k+w) including roots.
            // The only recognized non-link terminal is one bare stop atom.
            let p = t.p();
            let scalar_empty = p.bools == 0
                && [&p.ints, &p.rats, &p.floats, &p.strings]
                    .iter()
                    .all(|l: &&Lits| !l.cofinite && l.values.is_empty());
            if !scalar_empty
                || !p.tuples.is_default()
                || p.structs
                || p.morphisms.is_leaf() != Some(false)
                || p.atoms.cofinite
                || p.atoms.names.len() != 1
                || !p
                    .atoms
                    .names
                    .values()
                    .next()
                    .is_some_and(|a| a.bare && a.payload == Type::empty())
            {
                return None;
            }
        }
    }
    Some(alphabet)
}

impl Nodes {
    // Complexity tradeoff: convert a shared head once rather than once per
    // chain node. Cache O(distinct projected head data); returning a clone still
    // costs its projected width per node, so this is not a global finder bound.
    fn ints(&mut self, t: &Type) -> Option<Ints> {
        if let Some(v) = self.heads.get(t) {
            return v.clone();
        }
        let value = match &self.alphabet {
            None => Ints::of(t),
            Some(alphabet) => {
                let p = t.p();
                if !only_ints(&p) {
                    return None;
                }
                // Complexity tradeoff: either enumeration computes precisely the
                // same intersection. K*log(2+A) versus A*log(2+K) is minimized
                // by iterating the smaller set: x/log(2+x) is increasing.
                // No verdict, cell, or structural refusal changes at this crossing.
                let vals = if p.ints.values.len() <= alphabet.len() {
                    p.ints
                        .values
                        .iter()
                        .filter(|v| alphabet.contains(*v))
                        .cloned()
                        .collect()
                } else {
                    alphabet
                        .iter()
                        .filter(|v| p.ints.values.contains(*v))
                        .cloned()
                        .collect()
                };
                Some(Ints {
                    cof: p.ints.cofinite,
                    vals,
                })
            }
        };
        self.heads.insert(t.clone(), value.clone());
        value
    }

    /// The node of `x`, reading the nodes after it first; `None` outside the class.
    fn node(&mut self, x: &Type) -> Option<usize> {
        let mut path: Vec<(Type, bool, Ints)> = Vec::new();
        let mut on_path: ByType<()> = ByType::with_hasher(Digests::new());
        let mut cur = x.clone();
        let mut below = loop {
            if let Some(&i) = self.of.get(&cur) {
                break i;
            }
            if on_path.insert(cur.clone(), ()).is_some() {
                return None;
            }
            if let Some((s, l, h, next)) = list_step(&cur) {
                if l != self.link {
                    return None;
                }
                if let Some(s) = &s {
                    match &self.stop {
                        None => self.stop = Some(s.clone()),
                        Some(t) if t == s => {}
                        Some(_) => return None,
                    }
                }
                let head = self.ints(&h)?;
                if next == cur {
                    // The carrier: a self-loop holding the empty list, the only one.
                    if s.is_none() || self.carrier.is_some() {
                        return None;
                    }
                    let i = self.nodes.len();
                    self.nodes.push(Node {
                        stop: true,
                        head,
                        next: None,
                        carrier: true,
                        ht: 0,
                    });
                    self.of.insert(cur.clone(), i);
                    self.carrier = Some((cur, i));
                    break i;
                }
                path.push((cur, s.is_some(), head));
                cur = next;
                continue;
            }
            // The end: the bare stop atom and nothing else.
            let p = cur.p();
            let lits_empty = [&p.ints, &p.rats, &p.floats, &p.strings]
                .iter()
                .all(|l: &&Lits| !l.cofinite && l.values.is_empty());
            if p.bools != 0
                || !lits_empty
                || p.structs
                || p.morphisms.is_leaf() != Some(false)
                || !p.tuples.is_default()
                || p.atoms.cofinite
            {
                return None;
            }
            let mut stop = None;
            for (n, a) in &p.atoms.names {
                match (a.bare, a.payload == Type::empty()) {
                    (true, true) if stop.is_none() => stop = Some(n.clone()),
                    (false, true) => {}
                    _ => return None,
                }
            }
            let stop = stop?;
            match &self.stop {
                None => self.stop = Some(stop),
                Some(t) if *t == stop => {}
                Some(_) => return None,
            }
            let i = self.nodes.len();
            self.nodes.push(Node {
                stop: true,
                head: Ints {
                    cof: false,
                    vals: BTreeSet::new(),
                },
                next: None,
                carrier: false,
                ht: 0,
            });
            self.of.insert(cur, i);
            break i;
        };
        while let Some((ty, stop, head)) = path.pop() {
            let i = self.nodes.len();
            let ht = self.nodes[below].ht + 1;
            self.nodes.push(Node {
                stop,
                head,
                next: Some(below),
                carrier: false,
                ht,
            });
            self.of.insert(ty, i);
            below = i;
        }
        Some(below)
    }

    /// The terminal below `v`.
    fn terminal(&self, v: usize, anc: &Ancestors) -> usize {
        anc.at(v, self.nodes[v].ht, &self.nodes)
    }
}

/// Level-ancestor queries on the forest of nodes (each node's parent is its `next`): an Euler
/// tour, and the nodes of each height sorted by entry time.
struct Ancestors {
    tin: Vec<usize>,
    tout: Vec<usize>,
    by_ht: Vec<Vec<(usize, usize)>>,
}

impl Ancestors {
    fn new(nodes: &[Node]) -> Ancestors {
        let n = nodes.len();
        let mut kids: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (i, v) in nodes.iter().enumerate() {
            if let Some(j) = v.next {
                kids[j].push(i);
            }
        }
        let (mut tin, mut tout) = (vec![0; n], vec![0; n]);
        let mut time = 0;
        for r in (0..n).filter(|&i| nodes[i].next.is_none()) {
            let mut stack = vec![(r, 0usize)];
            tin[r] = time;
            time += 1;
            while let Some(&mut (v, ref mut k)) = stack.last_mut() {
                if *k < kids[v].len() {
                    let c = kids[v][*k];
                    *k += 1;
                    tin[c] = time;
                    time += 1;
                    stack.push((c, 0));
                } else {
                    tout[v] = time - 1;
                    stack.pop();
                }
            }
        }
        let top = nodes.iter().map(|v| v.ht).max().unwrap_or(0);
        let mut by_ht: Vec<Vec<(usize, usize)>> = vec![Vec::new(); top + 1];
        for (i, v) in nodes.iter().enumerate() {
            by_ht[v.ht].push((tin[i], i));
        }
        for l in &mut by_ht {
            l.sort_unstable();
        }
        Ancestors { tin, tout, by_ht }
    }

    /// The node `k` links after `v`, for `k <= ht(v)`.
    fn at(&self, v: usize, k: usize, nodes: &[Node]) -> usize {
        let h = nodes[v].ht - k;
        let l = &self.by_ht[h];
        // The one node of height `h` whose interval holds `v`: the last entered at or before it.
        let i = l.partition_point(|&(t, _)| t <= self.tin[v]) - 1;
        l[i].1
    }
}

/// The places in `[lo, hi]` of a sorted list.
fn count(l: &[usize], lo: usize, hi: usize) -> usize {
    l.partition_point(|&j| j <= hi) - l.partition_point(|&j| j < lo)
}

fn range(l: &[usize], lo: usize, hi: usize) -> &[usize] {
    &l[l.partition_point(|&j| j < lo)..l.partition_point(|&j| j <= hi)]
}

/// One refused row that holds the length `l0`.
struct Root {
    row: Row,
    s: usize,
    kill: Option<usize>,
    atoms: Vec<(usize, Ints)>,
}

/// The decision of the class above, or `None` outside it or when only the search can answer.
pub(super) fn decide(t: &Type) -> Option<ChainPlan> {
    decide_counted(t, &mut (0, 0))
}

pub(super) fn cell_counts(t: &Type) -> (usize, usize) {
    let mut counts = (0, 0);
    let _ = decide_counted(t, &mut counts);
    counts
}

fn decide_counted(t: &Type, counts: &mut (usize, usize)) -> Option<ChainPlan> {
    let p = t.p();
    let lits_empty = [&p.ints, &p.rats, &p.floats, &p.strings]
        .iter()
        .all(|l: &&Lits| !l.cofinite && l.values.is_empty());
    if p.bools != 0
        || !lits_empty
        || p.structs
        || p.morphisms.is_leaf() != Some(false)
        || !p.tuples.is_default()
        || p.atoms.cofinite
    {
        return None;
    }
    let mut link: Option<(std::sync::Arc<str>, Type)> = None;
    for (name, a) in &p.atoms.names {
        match (a.bare, a.payload == Type::empty()) {
            (true, _) => return None,
            (false, true) => {}
            (false, false) => {
                if link.is_some() {
                    return None;
                }
                link = Some((name.clone(), a.payload.clone()));
            }
        }
    }
    let (link, payload) = link?;
    let q = payload.p();
    if q.tuples.rest || q.tuples.lens.len() != 1 || q.structs {
        return None;
    }
    let f = q.tuples.lens.get(&2)?;
    let (taken, refused) = f.forced();
    let atoms = f.distinct_atoms();
    if taken.is_empty() || refused.is_empty() || taken.len() + refused.len() != atoms.len() {
        return None;
    }
    let taken_set: BTreeSet<&Row> = taken.iter().collect();
    if !f.eval(&|a| taken_set.contains(a)) {
        return None;
    }

    // The nodes of every row tail.
    let mut ns = Nodes {
        nodes: Vec::new(),
        of: ByType::with_hasher(Digests::new()),
        stop: None,
        link: link.clone(),
        carrier: None,
        alphabet: finite_positive_alphabet(&taken),
        heads: ByType::with_hasher(Digests::new()),
    };
    let mut pos: Vec<(Ints, usize)> = Vec::with_capacity(taken.len());
    for row in &taken {
        pos.push((ns.ints(&row[0])?, ns.node(&row[1])?));
    }
    let mut neg: Vec<(Ints, usize)> = Vec::with_capacity(refused.len());
    for row in &refused {
        neg.push((ns.ints(&row[0])?, ns.node(&row[1])?));
    }
    let stop = ns.stop.clone()?;
    let nodes = &ns.nodes;
    let anc = Ancestors::new(nodes);
    let h_car: Option<Ints> = ns.carrier.as_ref().map(|&(_, i)| nodes[i].head.clone());

    // The positive chain: the one taken row whose tail is not the carrier, if any.
    let mut chain: Option<usize> = None;
    let mut car_pos = false;
    for &(_, s) in &pos {
        if nodes[s].carrier {
            car_pos = true;
        } else if chain.replace(s).is_some() {
            return None;
        }
    }
    let chain = chain.unwrap_or(pos[0].1);
    let mut p1: Ints = pos[0].0.clone();
    for (h, _) in &pos[1..] {
        p1 = p1.meet(h);
    }
    // `pl[j]` for places `j = 1 .. l0` (index 0 unused).
    let mut pl: Vec<Ints> = vec![p1.clone(), p1];
    let mut cur = chain;
    loop {
        if pl[pl.len() - 1].is_empty() {
            return Some(ChainPlan::Empty);
        }
        if nodes[cur].stop {
            break;
        }
        // Not a stop: a cons node (the carrier and the end hold the empty list).
        let mut h: Ints = nodes[cur].head.clone();
        if car_pos && let Some(c) = &h_car {
            h = h.meet(c);
        }
        pl.push(h);
        cur = nodes[cur].next.expect("a cons node");
    }
    let l0 = pl.len() - 1;
    // E1 and E3, over the rest of the positive chain.
    let longer = nodes[cur].next.is_some() || nodes[cur].carrier;
    let mut e1 = h_car.is_some();
    if let Some(c) = &h_car {
        e1 = pl[2..].iter().all(|x| x.subset(c));
        let mut v = cur;
        while let Some(nx) = nodes[v].next {
            let mut h: Ints = nodes[v].head.clone();
            if car_pos {
                h = h.meet(c);
            }
            if !h.subset(c) {
                e1 = false;
            }
            v = nx;
        }
    }
    // Carrier cells are read as not separating: every `p_j` with `j >= 2` within `H`.
    if let Some(c) = &h_car
        && !pl[2..].iter().all(|x| x.subset(c))
    {
        return None;
    }

    // The refused rows by length: a hint for the checker for each one dropped.
    let mut hints: Vec<(Row, ChainHint)> = Vec::new();
    let mut roots: Vec<Root> = Vec::new();
    for (k, (h0, s)) in neg.into_iter().enumerate() {
        let row = refused[k].clone();
        let hs = nodes[s].ht;
        let steps = l0 - 1;
        let holds = if steps < hs {
            nodes[anc.at(s, steps, nodes)].stop
        } else {
            let term = ns.terminal(s, &anc);
            steps == hs || nodes[term].carrier
        };
        if !holds {
            let hint = if steps < hs {
                ChainHint::Len
            } else {
                ChainHint::Miss(hs + 1)
            };
            hints.push((row, hint));
            continue;
        }
        let mut r = Root {
            row,
            s,
            kill: None,
            atoms: Vec::new(),
        };
        if pl[1].disjoint(&h0) {
            r.kill = Some(1);
        } else if !pl[1].subset(&h0) {
            r.atoms.push((1, pl[1].minus(&h0)));
        }
        roots.push(r);
    }

    // Complexity tradeoff: the naive filter uses all root heights at every node, so
    // one shallow outlier destroys a useful congruence on the entire spine (X38).
    // At height h only roots of height >= h can reach the node. Their suffix gcd
    // gives a necessary residue for every reachable place. On removing a height
    // the nonzero gcd can only grow by an integer factor; there are O(log top)
    // distinct moduli (plus the singleton case). Hash indices of positive places and value
    // incidences for those moduli cost O(P log top) expected time and space, versus
    // O(P log P) time and O(P) space for the old single BTreeSet index. This is a necessary
    // filter, not an Empty proof; the per-value filter below narrows the cells further.
    let mut heights: Vec<usize> = roots
        .iter()
        .filter(|r| r.kill.is_none())
        .map(|r| nodes[r.s].ht)
        .collect();
    heights.sort_unstable();
    heights.dedup();
    let gcd = |mut a: usize, mut b: usize| {
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    };
    let exact_period = l0 + nodes.iter().map(|n| n.ht).max().unwrap_or(0) + 2;
    let mut suffix = vec![0; heights.len()];
    for i in (0..heights.len().saturating_sub(1)).rev() {
        suffix[i] = gcd(suffix[i + 1], heights[i + 1] - heights[i]);
    }
    let mut residues = HashMap::new();
    for &g in &suffix {
        let period = if g == 0 { exact_period } else { g };
        residues.entry(period).or_insert_with(|| {
            let mut finite = HashSet::new();
            let mut cofinite = HashSet::new();
            for (j, x) in pl.iter().enumerate().skip(2) {
                if x.cof {
                    cofinite.insert(j % period);
                } else {
                    for value in &x.vals {
                        finite.insert((j % period, value.clone()));
                    }
                }
            }
            (finite, cofinite)
        });
    }

    // The rows still read. A row leaves once it is killed, once it has three atoms (its first
    // two by place make its clause, the third marks it wide), or once the nodes left are past
    // its length `l0`. The nodes are read from the highest down, so each row meets its places
    // in increasing order and takes at most four cells.
    let nr = roots.len();
    let mut by_tin: Vec<(usize, usize)> = roots
        .iter()
        .enumerate()
        .map(|(i, r)| (anc.tin[r.s], i))
        .collect();
    by_tin.sort_unstable();
    let top = nodes.iter().map(|v| v.ht).max().unwrap_or(0);
    let mut roots_at: Vec<Vec<(usize, usize)>> = vec![Vec::new(); top + 1];
    for &(tn, i) in &by_tin {
        roots_at[nodes[roots[i].s].ht].push((tn, i));
    }
    let mut rows = Rows {
        gone: vec![false; nr],
        g: Live::new(nr),
        h: roots_at.iter().map(|l| Live::new(l.len())).collect(),
        pos_g: vec![0; nr],
        pos_h: vec![0; nr],
        rh: roots.iter().map(|r| nodes[r.s].ht).collect(),
        c: Vec::new(),
        cl: vec![0; nr],
        pos_c: vec![usize::MAX; nr],
    };
    for (k, &(_, i)) in by_tin.iter().enumerate() {
        rows.pos_g[i] = k;
    }
    for l in &roots_at {
        for (k, &(_, i)) in l.iter().enumerate() {
            rows.pos_h[i] = k;
        }
    }
    for (i, r) in roots.iter().enumerate() {
        if r.kill.is_some() {
            rows.retire(i);
        }
    }
    // The places by value: each finite `p_j` under each of its values, and the cofinite ones.
    let mut fin_by_val: HashMap<Value, Vec<usize>> = HashMap::new();
    let (mut fin_places, mut cof_places) = (Vec::new(), Vec::new());
    for (j, x) in pl.iter().enumerate().skip(2) {
        if x.cof {
            cof_places.push(j);
        } else {
            fin_places.push(j);
            for v in &x.vals {
                fin_by_val.entry(v.clone()).or_default().push(j);
            }
        }
    }
    let mut vals: Vec<Value> = fin_by_val.keys().cloned().collect();
    vals.sort_unstable();
    // Complexity tradeoff: the reads above skip a node only by the residue of the root heights
    // modulo their difference gcd, so one root in another residue (`r7congruenceout`) sets that
    // gcd to 1 and every place that can separate is read, `Theta(n^2)` empty reads; and they read
    // places below every root's height (`r7aperiodic`, `n^2 / 18`). Used: (1) the place window
    // starts at the least height of the live rows below the node, not at 2; (2) a modulus `g` from
    // the places themselves: the gcd of the differences between the places (j >= 2) of each value
    // that a cofinite node head excludes. A value `x` excluded at a node of height `h` separates
    // only places `j` congruent to `a_x` (its first place) modulo `g`, so only rows of tail height
    // `h + a_x - 2` modulo `g` (exactly, when `g` is 0) can get a cell from it; a value with no
    // row of that class still read (not retired) below the node is skipped. Counted over the rows
    // unkilled at the start instead, one root of another class retired early kept its class
    // alive and every place of the value was read (`r8heightout`, `n^2 / 6` empty reads). Cost:
    // O(value incidences) gcd steps, the rows indexed by class once (a `Live` per class, a
    // removal per retired row), two binary searches and a Fenwick count per (node, excluded
    // value): O((rows + incidences) log n), linear storage. Sufficient, not complete: a value
    // whose live rows of its class below a node miss its places is still read place by place;
    // no bound on those reads is proved.
    let mut excluded: BTreeSet<Value> = BTreeSet::new();
    for v in nodes.iter().filter(|v| v.next.is_some() && v.head.cof) {
        excluded.extend(
            v.head
                .vals
                .iter()
                .filter(|x| fin_by_val.contains_key(*x))
                .cloned(),
        );
    }
    let mut g = 0usize;
    for x in &excluded {
        let l = &fin_by_val[x];
        for &j in &l[1..] {
            let mut b = j - l[0];
            while b != 0 {
                (g, b) = (b, g % b);
            }
        }
    }
    let class = |height: usize| if g == 0 { height } else { height % g };
    // The rows of each class in Euler order, with those still read (`rows.c`): a class whose rows
    // below a node are all retired gives no cell there (`r8heightout`).
    let mut class_ix: HashMap<usize, usize> = HashMap::new();
    let mut of_class: Vec<Vec<usize>> = Vec::new();
    for &(tn, i) in &by_tin {
        if !rows.gone[i] {
            let next = class_ix.len();
            let c = *class_ix.entry(class(rows.rh[i])).or_insert(next);
            if c == of_class.len() {
                of_class.push(Vec::new());
            }
            rows.pos_c[i] = of_class[c].len();
            rows.cl[i] = c;
            of_class[c].push(tn);
        }
    }
    rows.c = of_class.iter().map(|l| Live::new(l.len())).collect();
    // The class of `height` and the positions of its rows with tails in the Euler interval
    // [a, b], if it has rows.
    let class_span = |height: usize, a: usize, b: usize| {
        class_ix.get(&class(height)).map(|&c| {
            let l = &of_class[c];
            (
                c,
                l.partition_point(|&t| t < a),
                l.partition_point(|&t| t <= b),
            )
        })
    };
    // The greatest tail height of the rows below each node, and the least of the unkilled ones.
    let mut max_below: Vec<Option<usize>> = vec![None; nodes.len()];
    let mut min_below: Vec<Option<usize>> = vec![None; nodes.len()];
    for r in &roots {
        let m = &mut max_below[r.s];
        *m = Some(m.map_or(nodes[r.s].ht, |x: usize| x.max(nodes[r.s].ht)));
        if r.kill.is_none() {
            let m = &mut min_below[r.s];
            *m = Some(m.map_or(nodes[r.s].ht, |x: usize| x.min(nodes[r.s].ht)));
        }
    }
    let mut order: Vec<usize> = (0..nodes.len()).collect();
    order.sort_unstable_by_key(|&i| std::cmp::Reverse(anc.tin[i]));
    for &v in &order {
        if let (Some(m), Some(nx)) = (max_below[v], nodes[v].next) {
            let pm = &mut max_below[nx];
            *pm = Some(pm.map_or(m, |x| x.max(m)));
        }
        if let (Some(m), Some(nx)) = (min_below[v], nodes[v].next) {
            let pm = &mut min_below[nx];
            *pm = Some(pm.map_or(m, |x| x.min(m)));
        }
    }
    let mut cons: Vec<usize> = (0..nodes.len())
        .filter(|&v| nodes[v].next.is_some())
        .collect();
    cons.sort_unstable_by_key(|&v| (std::cmp::Reverse(nodes[v].ht), v));
    let mut past = top + 1;
    for v in cons {
        let h = nodes[v].ht;
        // Rows with tails at height `h + l0 - 1` or more meet `v` past their length.
        while past > h + l0 - 1 {
            past -= 1;
            if past <= top {
                for &(_, i) in &roots_at[past] {
                    rows.retire(i);
                }
            }
        }
        let Some(m) = max_below[v] else { continue };
        let hv: &Ints = &nodes[v].head;
        // A head of all integers holds every `p_j`: no place separates at `v`.
        if hv.cof && hv.vals.is_empty() {
            continue;
        }
        let first = heights.partition_point(|&rh| rh < h);
        if first == heights.len() {
            continue;
        }
        let base_height = heights[first];
        let period = if suffix[first] == 0 {
            exact_period
        } else {
            suffix[first]
        };
        let (finite_residue, cofinite_residue) = &residues[&period];
        let residue = (base_height % period + period + 2 - h % period) % period;
        if hv.cof
            && !cofinite_residue.contains(&residue)
            && hv
                .vals
                .iter()
                .all(|x| !finite_residue.contains(&(residue, x.clone())))
        {
            continue;
        }
        // Places below `lo` meet `v` only from rows lower than every unkilled row below `v`.
        let lo = min_below[v].map_or(2, |mn| (mn + 2 - h).max(2));
        let hi = l0.min(m + 2 - h);
        if hi < lo {
            continue;
        }
        let (a, b) = (anc.tin[v], anc.tout[v]);
        // The excluded values that may give a cell here: places in the window, and a live row of
        // their class below `v`. The others give none.
        let kept: Vec<Value> = if hv.cof {
            hv.vals
                .iter()
                .filter(|x| {
                    fin_by_val.get(x).is_some_and(|l| {
                        count(l, lo, hi) > 0
                            && class_span(h + l[0] - 2, a, b)
                                .is_some_and(|(c, ka, kb)| rows.c[c].count(ka, kb) > 0)
                    })
                })
                .cloned()
                .collect()
        } else {
            Vec::new()
        };
        if hv.cof && kept.is_empty() && count(&cof_places, lo, hi) == 0 {
            continue;
        }
        let (glo, ghi) = (
            by_tin.partition_point(|&(t, _)| t < a),
            by_tin.partition_point(|&(t, _)| t <= b),
        );
        let live = rows.g.count(glo, ghi);
        if live == 0 {
            continue;
        }
        // The cost of listing the places that may separate at `v`: from the values a cofinite
        // head leaves out; for a finite head, from the values outside it, or every place.
        let (est, by_value) = if hv.cof {
            let e = kept
                .iter()
                .map(|x| fin_by_val.get(x).map_or(0, |l| count(l, lo, hi)))
                .sum::<usize>();
            (e + count(&cof_places, lo, hi), true)
        } else {
            let inside = hv
                .vals
                .iter()
                .filter(|x| fin_by_val.contains_key(x))
                .count();
            let outside = hv.vals.len() + vals.len() - inside;
            let all = count(&fin_places, lo, hi);
            (outside.min(all) + count(&cof_places, lo, hi), outside < all)
        };
        if live <= est {
            let mut k = rows.g.find(glo);
            while k < ghi {
                let i = by_tin[k].1;
                if take(&mut roots[i], rows.rh[i] + 2 - h, &pl, hv, counts) {
                    rows.retire(i);
                }
                k = rows.g.find(k + 1);
            }
            continue;
        }
        let mut js: Vec<usize> = Vec::new();
        if hv.cof {
            for x in &kept {
                if let Some(l) = fin_by_val.get(x) {
                    js.extend(range(l, lo, hi));
                }
            }
        } else if by_value {
            // The values of the places outside `hv`, read between `hv`'s values.
            let mut from = 0;
            for x in &hv.vals {
                let e = vals.partition_point(|u| u < x);
                for u in &vals[from..e] {
                    js.extend(range(&fin_by_val[u], lo, hi));
                }
                from = if vals.get(e) == Some(x) { e + 1 } else { e };
            }
            for u in &vals[from..] {
                js.extend(range(&fin_by_val[u], lo, hi));
            }
        } else {
            js.extend(range(&fin_places, lo, hi));
        }
        js.extend(range(&cof_places, lo, hi));
        js.sort_unstable();
        js.dedup();
        for j in js {
            let hh = h + j - 2;
            let at = &roots_at[hh];
            let s1 = at.partition_point(|&(t, _)| t <= b);
            let mut k = rows.h[hh].find(at.partition_point(|&(t, _)| t < a));
            if k >= s1 {
                counts.0 += 1;
                counts.1 += 1;
            }
            while k < s1 {
                let i = at[k].1;
                if take(&mut roots[i], j, &pl, hv, counts) {
                    rows.retire(i);
                }
                k = rows.h[hh].find(k + 1);
            }
        }
    }

    // E2, and the rows left.
    let mut e2 = true;
    let mut live: Vec<Root> = Vec::new();
    for mut r in roots {
        if let Some(j) = r.kill {
            hints.push((r.row, ChainHint::Miss(j - 1)));
            continue;
        }
        let term = ns.terminal(r.s, &anc);
        if !(nodes[r.s].ht < l0 && nodes[term].carrier) {
            e2 = false;
        }
        r.atoms.sort_unstable_by_key(|a| a.0);
        live.push(r);
    }
    let exact = !longer || (e1 && e2);
    if live.iter().any(|r| r.atoms.is_empty()) {
        return exact.then_some(ChainPlan::Empty);
    }
    let wide = live.iter().any(|r| r.atoms.len() > 2);

    // The atoms, one variable each, and their forest at each place.
    let mut ids: HashMap<(usize, Ints), usize> = HashMap::new();
    let mut atom: Vec<(usize, Ints)> = Vec::new();
    let mut clause: Vec<[usize; 2]> = Vec::with_capacity(live.len());
    for r in &live {
        let mut two = [0; 2];
        for (k, (j, a)) in r.atoms.iter().take(2).enumerate() {
            let n = atom.len();
            let id = *ids.entry((*j, a.clone())).or_insert_with(|| {
                atom.push((*j, a.clone()));
                n
            });
            two[k] = id;
        }
        if r.atoms.len() == 1 {
            two[1] = two[0];
        }
        clause.push(two);
    }
    let mut at_place: HashMap<usize, Vec<usize>> = HashMap::new();
    for (i, (j, _)) in atom.iter().enumerate() {
        at_place.entry(*j).or_default().push(i);
    }
    let mut parent: Vec<Option<usize>> = vec![None; atom.len()];
    for list in at_place.values() {
        forest(list, &atom, &mut parent)?;
    }

    let mut sat = TwoSat {
        vars: 0,
        clauses: Vec::new(),
        meets: HashMap::new(),
    };
    let z: Vec<usize> = atom.iter().map(|_| sat.fresh()).collect();
    let mut kids: HashMap<(usize, Option<usize>), Vec<usize>> = HashMap::new();
    for (i, (j, _)) in atom.iter().enumerate() {
        if let Some(pa) = parent[i] {
            sat.clauses.push((z[i] ^ 1, z[pa]));
        }
        kids.entry((*j, parent[i])).or_default().push(i);
    }
    let mut groups: Vec<Vec<usize>> = kids.into_values().collect();
    groups.sort_unstable();
    for g in groups {
        // At most one: the ladder `s_i` = "one of the first i is true".
        let mut prev: Option<usize> = None;
        for &a in &g {
            let s = sat.fresh();
            sat.clauses.push((z[a] ^ 1, s));
            if let Some(ps) = prev {
                sat.clauses.push((ps ^ 1, s));
                sat.clauses.push((ps ^ 1, z[a] ^ 1));
            }
            prev = Some(s);
        }
    }
    for c in &clause {
        sat.clauses.push((z[c[0]], z[c[1]]));
    }
    let Some(model) = sat.solve() else {
        return (exact && !wide).then_some(ChainPlan::Empty);
    };

    // The list: at each place a value of the deepest true atom, else any value of `p_j`.
    let depth = |mut a: usize| {
        let mut d = 0;
        while let Some(pa) = parent[a] {
            d += 1;
            a = pa;
        }
        d
    };
    let mut deepest: HashMap<usize, (usize, usize)> = HashMap::new();
    for (i, (j, _)) in atom.iter().enumerate() {
        if model[z[i] / 2] {
            let d = depth(i);
            let e = deepest.entry(*j).or_insert((d, i));
            if d >= e.0 {
                *e = (d, i);
            }
        }
    }
    let mut heads = Vec::with_capacity(l0);
    for (j, x) in pl.iter().enumerate().skip(1) {
        let v = deepest
            .get(&j)
            .map_or_else(|| x.pick(), |&(_, i)| atom[i].1.pick());
        heads.push(Type::lit(&v)?);
    }
    for (r, c) in live.into_iter().zip(&clause) {
        let a = if model[z[c[0]] / 2] { c[0] } else { c[1] };
        hints.push((r.row, ChainHint::Miss(atom[a].0 - 1)));
    }
    Some(ChainPlan::Inhabited {
        stop,
        link,
        heads,
        hints,
    })
}

/// The parent of each atom of one place in the laminar forest of the atoms `list`, or `None`
/// when two of them cross. Cofinite atoms must be a chain (their excluded sets nested); a
/// finite atom, taken largest first, lies in the deepest atom holding one of its values, which
/// must be the same for all its values.
fn forest(list: &[usize], atom: &[(usize, Ints)], parent: &mut [Option<usize>]) -> Option<()> {
    let mut cof: Vec<usize> = list.iter().copied().filter(|&i| atom[i].1.cof).collect();
    cof.sort_unstable_by_key(|&i| (atom[i].1.vals.len(), i));
    for w in cof.windows(2) {
        if !atom[w[0]].1.vals.is_subset(&atom[w[1]].1.vals) {
            return None;
        }
        parent[w[1]] = Some(w[0]);
    }
    // The first cofinite atom (in the chain) that excludes each value.
    let mut first_out: HashMap<Value, usize> = HashMap::new();
    for (k, &i) in cof.iter().enumerate() {
        for x in &atom[i].1.vals {
            first_out.entry(x.clone()).or_insert(k);
        }
    }
    let deepest_cof = |x: &Value| -> Option<usize> {
        let k = first_out.get(x).copied().unwrap_or(cof.len());
        (k > 0).then(|| cof[k - 1])
    };
    let mut fin: Vec<usize> = list.iter().copied().filter(|&i| !atom[i].1.cof).collect();
    fin.sort_unstable_by_key(|&i| (std::cmp::Reverse(atom[i].1.vals.len()), i));
    let mut owner: HashMap<Value, usize> = HashMap::new();
    for i in fin {
        let mut up: Option<Option<usize>> = None;
        for x in &atom[i].1.vals {
            let o = owner.get(x).copied().or_else(|| deepest_cof(x));
            match up {
                None => up = Some(o),
                Some(u) if u == o => {}
                Some(_) => return None,
            }
        }
        parent[i] = up.flatten();
        for x in &atom[i].1.vals {
            owner.insert(x.clone(), i);
        }
    }
    Some(())
}

/// Reads the cell of row `r` at place `j`, where the row's node has the head `hv`: a kill, an
/// atom, or nothing. Whether the row is done (killed, or three atoms).
fn take(r: &mut Root, j: usize, pl: &[Ints], hv: &Ints, counts: &mut (usize, usize)) -> bool {
    counts.0 += 1;
    if pl[j].subset(hv) {
        counts.1 += 1;
        return false;
    }
    if pl[j].disjoint(hv) {
        r.kill = Some(r.kill.map_or(j, |k| k.min(j)));
        return true;
    }
    r.atoms.push((j, pl[j].minus(hv)));
    r.atoms.len() >= 3
}

/// The positions `0 .. n` still in a list: the next one at or after a position (by pointers
/// that skip the removed ones), and how many lie in a range (a Fenwick tree).
struct Live {
    next: Vec<usize>,
    fen: Vec<isize>,
}

impl Live {
    fn new(n: usize) -> Live {
        let mut fen = vec![1; n + 1];
        fen[0] = 0;
        for i in 1..=n {
            let p = i + i.isolate_lowest_one();
            if p <= n {
                fen[p] += fen[i];
            }
        }
        Live {
            next: (0..=n).collect(),
            fen,
        }
    }

    fn prefix(&self, mut i: usize) -> isize {
        let mut s = 0;
        while i > 0 {
            s += self.fen[i];
            i -= i.isolate_lowest_one();
        }
        s
    }

    /// How many of `lo .. hi` are left.
    fn count(&self, lo: usize, hi: usize) -> usize {
        (self.prefix(hi) - self.prefix(lo)) as usize
    }

    /// The first position left at or after `i` (`n` if none).
    fn find(&mut self, mut i: usize) -> usize {
        let mut r = i;
        while self.next[r] != r {
            r = self.next[r];
        }
        while self.next[i] != r {
            let n = self.next[i];
            self.next[i] = r;
            i = n;
        }
        r
    }

    /// Removes `i`, once.
    fn remove(&mut self, i: usize) {
        self.next[i] = i + 1;
        let mut k = i + 1;
        while k < self.fen.len() {
            self.fen[k] -= 1;
            k += k.isolate_lowest_one();
        }
    }
}

/// The rows still read: in Euler order over all heights (`g`), and at each tail height (`h`).
struct Rows {
    gone: Vec<bool>,
    g: Live,
    h: Vec<Live>,
    pos_g: Vec<usize>,
    pos_h: Vec<usize>,
    /// Each row's tail height.
    rh: Vec<usize>,
    /// The rows unkilled at the start by class of tail height (`c`), each row's class (`cl`), and
    /// its position there (`pos_c`, `usize::MAX` for a row killed at the start).
    c: Vec<Live>,
    cl: Vec<usize>,
    pos_c: Vec<usize>,
}

impl Rows {
    fn retire(&mut self, i: usize) {
        if !self.gone[i] {
            self.gone[i] = true;
            self.g.remove(self.pos_g[i]);
            self.h[self.rh[i]].remove(self.pos_h[i]);
            if self.pos_c[i] != usize::MAX {
                self.c[self.cl[i]].remove(self.pos_c[i]);
            }
        }
    }
}
