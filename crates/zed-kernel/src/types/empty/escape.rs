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
//! once the nodes left are past its length `l0`: each row takes at most four cells there. A
//! row with three atoms is read further only when the unit narrowing leaves it fewer than
//! three (`read_on`), since an atom it has further on can save a list. At each
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

use std::collections::{BTreeSet, HashMap};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use super::super::{Lits, Parts, Row, Type};
use super::shared::{ByType, ChainHint, ChainPlan, Digests, TwoSat, list_step};
use crate::digest::Digest;
use crate::value::Value;

/// A set of integers: `vals` when not `cof`, else the integers less `vals`.
// Complexity tradeoff: `n` rows sharing a width-`w` head `not_a` (`xr_bucket`) previously cloned,
// hashed and compared `BTreeSet<Value>` of size `w` once per row in `Nodes::ints`, `orig_live`,
// `U1` partner bucketing and `ids`, costing `Theta(n * w)`. Wrapping `vals` in `Rc` with a
// precomputed 64-bit `Digest` makes `Clone` and `Hash` `O(1)`, and `PartialEq` `O(1)` whenever
// hashes differ or `Rc::ptr_eq` holds (such as shared `Nodes::heads` and memoized place-1 cells).
#[derive(Clone, Debug)]
struct Ints {
    cof: bool,
    hash: u64,
    vals: Rc<BTreeSet<Value>>,
}

impl PartialEq for Ints {
    #[inline]
    fn eq(&self, o: &Ints) -> bool {
        self.cof == o.cof
            && self.hash == o.hash
            && (Rc::ptr_eq(&self.vals, &o.vals) || *self.vals == *o.vals)
    }
}

impl Eq for Ints {}

impl Hash for Ints {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

impl Ints {
    fn new(cof: bool, vals: BTreeSet<Value>) -> Ints {
        let mut d = Digest::default();
        cof.hash(&mut d);
        vals.hash(&mut d);
        Ints {
            cof,
            hash: d.finish(),
            vals: Rc::new(vals),
        }
    }

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
        Some(Ints::new(p.ints.cofinite, vals))
    }

    fn is_empty(&self) -> bool {
        !self.cof && self.vals.is_empty()
    }

    /// Whether `self ⊆ o`.
    fn subset(&self, o: &Ints) -> bool {
        match (self.cof, o.cof) {
            (false, false) => {
                self.vals.len() <= o.vals.len() && self.vals.iter().all(|x| o.vals.contains(x))
            }
            (false, true) => {
                if self.vals.len() <= o.vals.len() {
                    self.vals.iter().all(|x| !o.vals.contains(x))
                } else {
                    o.vals.iter().all(|x| !self.vals.contains(x))
                }
            }
            (true, false) => false,
            (true, true) => {
                o.vals.len() <= self.vals.len() && o.vals.iter().all(|x| self.vals.contains(x))
            }
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
            (false, _) => Ints::new(
                false,
                self.vals
                    .iter()
                    .filter(|x| o.cof != o.vals.contains(x))
                    .cloned()
                    .collect(),
            ),
            (true, false) => o.meet(self),
            (true, true) => Ints::new(true, self.vals.union(&o.vals).cloned().collect()),
        }
    }

    /// `self \ o`.
    fn minus(&self, o: &Ints) -> Ints {
        match (self.cof, o.cof) {
            (false, _) => Ints::new(
                false,
                self.vals
                    .iter()
                    .filter(|x| o.cof == o.vals.contains(x))
                    .cloned()
                    .collect(),
            ),
            (true, false) => Ints::new(true, self.vals.union(&o.vals).cloned().collect()),
            (true, true) => Ints::new(false, o.vals.difference(&self.vals).cloned().collect()),
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

    fn contains(&self, v: &Value) -> bool {
        self.cof != self.vals.contains(v)
    }

    fn pick_in(&self, dom: &Ints) -> Value {
        if !self.cof {
            return self.vals.iter().next().expect("not empty").clone();
        }
        (0..)
            .map(Value::Int)
            .find(|x| !self.vals.contains(x) && dom.contains(x))
            .expect("an intersection of two cofinite sets has a natural number")
    }

    /// Intersects a non-empty slice of `Ints` in `O(S log S)` time where `S = \sum_r (1 + |s_r.vals|)`.
    // Complexity tradeoff: folding `Ints::meet` left-to-right across `k` cofinite partners in one
    // `U1` bucket (`\bigcap_{q=1}^k (\mathbb{Z} \setminus \{q\})`) clones an excluded set of size
    // `q` at step `q`, costing `Theta(k^2)` (`xr_r2_bench_escape_single_bucket_scales_n_log_n`).
    // Cloning the smallest finite set once (or, when all sets are cofinite, the largest excluded
    // set once) and mutating that single `BTreeSet` in place costs `O(S log S)`.
    fn intersect_many(sets: &[&Ints]) -> Ints {
        debug_assert!(!sets.is_empty());
        if sets.len() == 1 {
            return (*sets[0]).clone();
        }
        if let Some((min_idx, min_fin)) = sets
            .iter()
            .enumerate()
            .filter(|(_, s)| !s.cof)
            .min_by_key(|(_, s)| s.vals.len())
        {
            let mut vals: BTreeSet<Value> = (*min_fin.vals).clone();
            for (idx, s) in sets.iter().enumerate() {
                if idx == min_idx || vals.is_empty() {
                    continue;
                }
                if s.cof {
                    for v in s.vals.iter() {
                        vals.remove(v);
                    }
                } else {
                    vals.retain(|x| s.vals.contains(x));
                }
            }
            Ints::new(false, vals)
        } else {
            let (max_idx, max_cof) = sets
                .iter()
                .enumerate()
                .max_by_key(|(_, s)| s.vals.len())
                .expect("non-empty cofinite slice");
            let mut vals = (*max_cof.vals).clone();
            for (idx, s) in sets.iter().enumerate() {
                if idx != max_idx {
                    for v in s.vals.iter() {
                        vals.insert(v.clone());
                    }
                }
            }
            Ints::new(true, vals)
        }
    }
}

/// Whether `p` holds integers only (or nothing).
fn only_ints(p: &Parts) -> bool {
    p.bools == 0
        && [&p.rats, &p.floats, &p.f32s, &p.strings]
            .iter()
            .all(|l: &&Lits| !l.cofinite && l.values.is_empty())
        && !p.structs
        && p.morphisms.is_leaf() == Some(false)
        && p.tuples.is_default()
        && !p.atoms.cofinite()
        && p.atoms
            .names()
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
    carrier: Option<(Type, usize, Type)>,
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
    let mut seen = ByType::new();
    let mut seen_heads = ByType::new();
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
                && [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
                    .iter()
                    .all(|l: &&Lits| !l.cofinite && l.values.is_empty());
            if !scalar_empty
                || !p.tuples.is_default()
                || p.structs
                || p.morphisms.is_leaf() != Some(false)
                || p.atoms.cofinite()
                || p.atoms.names().len() != 1
                || !p
                    .atoms
                    .names()
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
                Some(Ints::new(p.ints.cofinite, vals))
            }
        };
        self.heads.insert(t.clone(), value.clone());
        value
    }

    /// The node of `x`, reading the nodes after it first; `None` outside the class.
    fn node(&mut self, x: &Type) -> Option<usize> {
        let mut path: Vec<(Type, bool, Ints)> = Vec::new();
        let mut on_path: ByType<()> = ByType::new();
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
                    // The carrier: a self-loop holding the empty list.
                    s.as_ref()?;
                    // Complexity tradeoff: merging self-loop carriers across distinct recursive
                    // groups by comparing unprojected `h.p().ints` in O(|vals|) avoids unfolding
                    // or intersecting DFA states across groups (O(|Q_1| * |Q_2|)), following
                    // Hopcroft & Karp (1971) bisimulation / language equivalence on single-state
                    // Kleene-star list tails `L_H = #nil | #cons(H, L_H)`.
                    if let Some((_, existing_i, ref existing_h)) = self.carrier {
                        if existing_h.p().ints.cmp(&h.p().ints).is_eq() {
                            self.of.insert(cur, existing_i);
                            break existing_i;
                        }
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
                    self.carrier = Some((cur, i, h));
                    break i;
                }
                path.push((cur, s.is_some(), head));
                cur = next;
                continue;
            }
            // The end: the bare stop atom and nothing else.
            let p = cur.p();
            let lits_empty = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
                .iter()
                .all(|l: &&Lits| !l.cofinite && l.values.is_empty());
            if p.bools != 0
                || !lits_empty
                || p.structs
                || p.morphisms.is_leaf() != Some(false)
                || !p.tuples.is_default()
                || p.atoms.cofinite()
            {
                return None;
            }
            let mut stop = None;
            for (n, a) in p.atoms.names() {
                match (a.bare, a.payload == Type::empty()) {
                    (true, true) if stop.is_none() => stop = Some(n.clone()),
                    // A finite map of atoms lists no name whose part is none, the bare atom out
                    // and no payload (`Atoms::set`), and the map is finite here.
                    (false, true) => {
                        unreachable!("a finite map of atoms lists no name of no atom")
                    }
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
                head: Ints::new(false, BTreeSet::new()),
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

/// The cells read and the empty ones among them: each cell the pair listing reads (never an
/// empty one), and each distinct pair of a place class and a node class whose cell method A
/// summarizes at level 0, empty or not.
pub(super) fn cell_counts(t: &Type) -> (usize, usize) {
    let mut counts = (0, 0);
    let _ = decide_counted(t, &mut counts);
    counts
}

fn decide_counted(t: &Type, counts: &mut (usize, usize)) -> Option<ChainPlan> {
    let p = t.p();
    let lits_empty = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
        .iter()
        .all(|l: &&Lits| !l.cofinite && l.values.is_empty());
    if p.bools != 0
        || !lits_empty
        || p.structs
        || p.morphisms.is_leaf() != Some(false)
        || !p.tuples.is_default()
        || p.atoms.cofinite()
    {
        return None;
    }
    let mut link: Option<(std::sync::Arc<str>, Type)> = None;
    for (name, a) in p.atoms.names() {
        match (a.bare, a.payload == Type::empty()) {
            (true, _) => return None,
            // A finite map of atoms lists no name whose part is none, the bare atom out and no
            // payload (`Atoms::set`), and the map is finite here.
            (false, true) => unreachable!("a finite map of atoms lists no name of no atom"),
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
        of: ByType::new(),
        stop: None,
        link: link.clone(),
        carrier: None,
        alphabet: finite_positive_alphabet(&taken),
        heads: ByType::new(),
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
    let h_car: Option<Ints> = ns.carrier.as_ref().map(|&(_, i, _)| nodes[i].head.clone());

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

    // Complexity tradeoff: bounded 2-pass distributive partner merge `(U1)` and unit-clause
    // domain narrowing `(U2)` before laminar 2-SAT (Aspvall, Plass and Tarjan, "A linear-time
    // algorithm for testing the truth of certain quantified boolean formulas", Inform. Process.
    // Lett. 8(3), 1979, pp. 121-123), evaluated at `l0` and at the carrier-truncation lengths
    // `l_next` and `l_trunc`. Place-1 subtractions `pl[1].minus(h0)` are memoized by `h0` (`O(1)`
    // hash and `Rc::ptr_eq` equality), and bucket intersections use `Ints::intersect_many`, giving
    // `O(S log S)` work where `S` is the written size of distinct integer sets plus clauses;
    // naive per-row subtraction and pairwise `meet` folding cost `Theta(n^2)`.
    let solve_at_len = |target_len: usize,
                        mut pl: Vec<Ints>,
                        longer_after: bool,
                        all_held_from_l0: bool,
                        mut zero_out: Option<&mut Vec<usize>>,
                        counts: &mut (usize, usize)|
     -> Option<ChainPlan> {
        let mut hints: Vec<(Row, ChainHint)> = Vec::new();
        let mut roots: Vec<Root> = Vec::new();
        let mut p1_cache: HashMap<Ints, Option<Option<Ints>>, Digests> = HashMap::default();
        for (k, &(ref h0, s)) in neg.iter().enumerate() {
            let row = refused[k].clone();
            let hs = nodes[s].ht;
            let steps = target_len - 1;
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
            let p1_cell = p1_cache.entry(h0.clone()).or_insert_with(|| {
                if pl[1].disjoint(h0) {
                    Some(None)
                } else if !pl[1].subset(h0) {
                    Some(Some(pl[1].minus(h0)))
                } else {
                    None
                }
            });
            match p1_cell {
                Some(None) => r.kill = Some(1),
                Some(Some(diff)) => r.atoms.push((1, diff.clone())),
                None => {}
            }
            roots.push(r);
        }

        cells_windows(nodes, &anc, &pl, &mut roots, target_len, counts);

        // E2, and the rows left.
        let mut e2 = true;
        let mut orig_live: Vec<(Row, Vec<(usize, Ints)>)> = Vec::new();
        let mut clauses_work: Vec<Vec<(usize, Ints)>> = Vec::new();
        // For each clause, where its row's read stopped, when it stopped at the third atom
        // (`take`) with places left: the node of the next place, that place, and the row's
        // last place. Such a row may have more atoms, or a kill, further on, so its clause is
        // stronger than the row written; the unit narrowing (U2) below could shrink it to one
        // atom or none, read as exact: a wrong Empty (sweep_agreement r7, fixed case: a row
        // read to x1, x2, x3 lost its atom at x4). So whenever U2 leaves such a clause fewer
        // than three atoms, `read_on` reads its row further, to three atoms again, its end, or a
        // kill. While places are left a clause holds three atoms, so it is no unit, U1 (which
        // merges clauses of two) passes it by, and a clause of three at the fixed point turns
        // every Empty into a refusal (`strengthened`).
        // Complexity tradeoff: each cell of a row is read at most once, and only for rows the
        // narrowing reaches: `O(cells read)` set operations more, none on the families where no
        // unit narrows a cut row. Naive alternatives: read every cut row to its end, 28.7 times
        // the instructions per 8 times the size on `r6three` and `r6repeat3` (`Θ(n^2)`: n rows
        // of n places); or answer no Empty once a row is cut, which lost the decided cases of
        // `r8_light_edges_and_wide_rows_agree_with_the_witness` and
        // `r9_bmm_encoding_decides_as_the_boolean_product`.
        let mut more: Vec<Option<(usize, usize, usize)>> = Vec::new();
        for mut r in roots {
            if let Some(j) = r.kill {
                hints.push((r.row, ChainHint::Miss(j - 1)));
                continue;
            }
            let term = ns.terminal(r.s, &anc);
            if !(nodes[r.s].ht < target_len && nodes[term].carrier) {
                e2 = false;
            }
            r.atoms.sort_unstable_by_key(|a| a.0);
            // The read covers places 2 ..= min(target_len, ht + 1) (`walk`); place `j` is at
            // the node `j - 2` links after the row's tail.
            let last = target_len.min(nodes[r.s].ht + 1);
            let read = r.atoms.last().map_or(0, |a| a.0);
            more.push(
                (r.atoms.len() >= 3 && read < last)
                    .then(|| (anc.at(r.s, read - 1, nodes), read + 1, last)),
            );
            if r.atoms.is_empty()
                && let Some(z) = zero_out.as_deref_mut()
            {
                z.push(r.s);
            }
            orig_live.push((r.row, r.atoms.clone()));
            clauses_work.push(r.atoms);
        }
        let exact = (!longer_after || (e1 && e2)) && all_held_from_l0;
        if clauses_work.iter().any(Vec::is_empty) {
            return exact.then_some(ChainPlan::Empty);
        }

        // Complexity tradeoff (GROUP-order-cpoly-merge): the distributive partner merge (U1) and
        // unit-clause domain narrowing (U2) run to a fixed point, then the clauses left go to
        // laminar 2-SAT (Aspvall, Plass and Tarjan 1979). U1 is Boolean distributivity,
        // `\bigwedge_q ((j_1, A) \lor (j_2, B_q)) \iff (j_1, A) \lor (j_2, \bigcap_q B_q)`, and U2
        // is unit propagation: a clause of one atom `(j, U)` narrows `pl[j]` to `pl[j] \cap U`.
        // Both rewrite the clauses into an equivalent set, so every clause stays exact (each row is
        // read whole, above): no clause
        // is cut to its first two atoms (round 3 of XR-group-order-5 cut them, which made a unit
        // or an emptied clause prove nothing), and a clause of three or more atoms is narrowed
        // like the others; only the 2-SAT below reads the first two atoms of a clause still wide
        // and then answers no Empty (`wide`). Each pass costs `O(S log S)` (`S` the clauses'
        // atoms plus the written size of their sets; the groups are found by hashing, the
        // intersections by `Ints::intersect_many`), and a pass that changes anything removes at
        // least one clause (a merge replaces two or more by one; a narrowing removes each unit it
        // reads, since `pl[j] \subseteq U` afterward), so there are at most `C + 1` passes for `C`
        // clauses: `O(C S log S)` in the worst case, `O(S log S)` when the cascade is a bounded
        // number of passes deep, as on every family measured (`refusals::bench::xr_r2_bench_*`).
        // Naive: the round 3 patch stopped after two passes, a fixed bound that the
        // no-thresholds rule forbids and that left deeper cascades to the general search; the
        // general method is the product of the excluded chains, `O(2^n)` states.
        let mut strengthened = false;
        loop {
            loop {
                let mut changed = false;
                for side in 0..2 {
                    let mut drop_mask = vec![false; clauses_work.len()];
                    let mut merged_new: Vec<Vec<(usize, Ints)>> = Vec::new();
                    {
                        let mut groups: HashMap<(usize, &Ints, usize), Vec<usize>, Digests> =
                            HashMap::default();
                        for (idx, atoms) in clauses_work.iter().enumerate() {
                            if atoms.len() == 2 {
                                let (fixed, other) = if side == 0 {
                                    (&atoms[0], atoms[1].0)
                                } else {
                                    (&atoms[1], atoms[0].0)
                                };
                                groups
                                    .entry((fixed.0, &fixed.1, other))
                                    .or_default()
                                    .push(idx);
                            }
                        }
                        for ((jf, af, jo), idxs) in groups {
                            if idxs.len() < 2 {
                                continue;
                            }
                            let partner_pos = if side == 0 { 1 } else { 0 };
                            let partners: Vec<&Ints> = idxs
                                .iter()
                                .map(|&idx| &clauses_work[idx][partner_pos].1)
                                .collect();
                            let inter = Ints::intersect_many(&partners);
                            for &idx in &idxs {
                                drop_mask[idx] = true;
                            }
                            let mut new_atoms = vec![(jf, af.clone())];
                            if !inter.is_empty() {
                                new_atoms.push((jo, inter));
                                new_atoms.sort_unstable_by_key(|x| x.0);
                            }
                            merged_new.push(new_atoms);
                        }
                    }
                    if !merged_new.is_empty() {
                        changed = true;
                        let mut next_work = Vec::with_capacity(clauses_work.len());
                        let mut next_more = Vec::with_capacity(clauses_work.len());
                        for (idx, (item, m)) in clauses_work.into_iter().zip(more).enumerate() {
                            if !drop_mask[idx] {
                                next_work.push(item);
                                next_more.push(m);
                            }
                        }
                        // Merged from clauses of two atoms, each read whole.
                        next_more.extend(merged_new.iter().map(|_| None));
                        next_work.extend(merged_new);
                        clauses_work = next_work;
                        more = next_more;
                    }
                }

                let mut narrowed_places: HashMap<usize, Ints> = HashMap::new();
                {
                    let mut unit_by_place: HashMap<usize, Vec<&Ints>> = HashMap::new();
                    for atoms in &clauses_work {
                        if atoms.len() == 1 {
                            let (j, ref u) = atoms[0];
                            unit_by_place
                                .entry(j)
                                .or_insert_with(|| vec![&pl[j]])
                                .push(u);
                        }
                    }
                    for (j, sets) in unit_by_place {
                        narrowed_places.insert(j, Ints::intersect_many(&sets));
                    }
                }
                if narrowed_places.is_empty() {
                    if changed {
                        continue;
                    }
                    break;
                }
                for (&j, new_pl) in &narrowed_places {
                    if new_pl.is_empty() {
                        return (exact && !strengthened).then_some(ChainPlan::Empty);
                    }
                    pl[j] = new_pl.clone();
                }
                let mut next_work = Vec::with_capacity(clauses_work.len());
                let mut next_more = Vec::with_capacity(clauses_work.len());
                for (atoms, mut rest) in clauses_work.into_iter().zip(more) {
                    let mut killed = false;
                    let mut updated: Vec<(usize, Ints)> = Vec::with_capacity(atoms.len());
                    for (j, a) in atoms {
                        if narrowed_places.contains_key(&j) {
                            if pl[j].subset(&a) {
                                killed = true;
                                break;
                            }
                            if pl[j].cof {
                                let vals: BTreeSet<Value> = a
                                    .vals
                                    .iter()
                                    .filter(|x| !pl[j].vals.contains(*x))
                                    .cloned()
                                    .collect();
                                if a.cof || !vals.is_empty() {
                                    updated.push((j, Ints::new(a.cof, vals)));
                                }
                            } else {
                                let m = pl[j].meet(&a);
                                if !m.is_empty() {
                                    updated.push((j, m));
                                }
                            }
                        } else {
                            updated.push((j, a));
                        }
                    }
                    if killed || read_on(&mut updated, &mut rest, nodes, &pl, counts) {
                        continue;
                    }
                    if updated.is_empty() {
                        return (exact && !strengthened).then_some(ChainPlan::Empty);
                    }
                    next_work.push(updated);
                    next_more.push(rest);
                }
                clauses_work = next_work;
                more = next_more;
            }
            if strengthened || !clauses_work.iter().any(|a| a.len() > 2) {
                break;
            }
            // The exact fixed point left a clause of three or more atoms, which 2-SAT cannot
            // read. For the witness only, keep the first two atoms of each such clause: that
            // strengthens the system (each kept clause implies the clause written), so a model
            // of it is a model of the written clauses, checked again against `orig_live`
            // below; but an empty answer of it proves nothing, so `strengthened` turns every
            // Empty below into a refusal. Its fixed point runs once more, at the same cost.
            strengthened = true;
            for atoms in &mut clauses_work {
                atoms.truncate(2);
            }
            // No Empty follows from here on, so no row is read further.
            more.iter_mut().for_each(|m| *m = None);
        }

        let wide = strengthened;

        // The atoms, one variable each, and their forest at each place.
        let mut ids: HashMap<(usize, Ints), usize, Digests> = HashMap::default();
        let mut atom: Vec<(usize, Ints)> = Vec::new();
        let mut clause: Vec<[usize; 2]> = Vec::with_capacity(clauses_work.len());
        for atoms in &clauses_work {
            let mut two = [0; 2];
            for (k, (j, a)) in atoms.iter().take(2).enumerate() {
                let n = atom.len();
                let id = *ids.entry((*j, a.clone())).or_insert_with(|| {
                    atom.push((*j, a.clone()));
                    n
                });
                two[k] = id;
            }
            if atoms.len() == 1 {
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

        // The list: at each place a value of the deepest true atom, else any value of `pl[j]`.
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
        let mut vals_picked = Vec::with_capacity(target_len + 1);
        vals_picked.push(Value::Int(0)); // unused index 0
        let mut heads = Vec::with_capacity(target_len);
        for (j, x) in pl.iter().enumerate().skip(1) {
            let v = deepest
                .get(&j)
                .map_or_else(|| x.pick(), |&(_, i)| atom[i].1.pick_in(x));
            heads.push(Type::lit(&v)?);
            vals_picked.push(v);
        }
        for (row, orig_atoms) in orig_live {
            let mut missed_at = None;
            for (j, a) in orig_atoms {
                if a.contains(&vals_picked[j]) {
                    missed_at = Some(j);
                    break;
                }
            }
            let j = missed_at?;
            hints.push((row, ChainHint::Miss(j - 1)));
        }
        Some(ChainPlan::Inhabited {
            stop: stop.clone(),
            link: link.clone(),
            heads,
            hints,
        })
    };

    let mut zero_rows: Vec<usize> = Vec::new();
    if let Some(plan) = solve_at_len(l0, pl.clone(), longer, true, Some(&mut zero_rows), counts) {
        return Some(plan);
    }

    if longer && e1 {
        let holds_l0 = |s: usize| -> bool {
            let hs = nodes[s].ht;
            let steps = l0 - 1;
            if steps < hs {
                nodes[anc.at(s, steps, nodes)].stop
            } else {
                let term = ns.terminal(s, &anc);
                steps == hs || nodes[term].carrier
            }
        };
        // Complexity tradeoff: deciding every positive length `l0 ..= l_steady` independently
        // costs `O(n^2 log n)` when chains have height `n`. Instead, one `O(nodes)` bottom-up
        // DP on the node forest (`next_no_stop`, and `next_sep` when `cur` is at the carrier
        // so every place `j > l0` has head `H`) finds the exact earliest length `l_first > l0`
        // where `l0`'s active rows change (clearing every zero-atom killer of `l0`, or else the
        // earliest active row that stops holding or gains a separating cell), plus the active-
        // row and steady-state lengths `l_next` and `l_steady`. At most three lengths past `l0`
        // are solved, preserving `O((nodes + rows + cells) log n)` with no thresholds. Order-
        // independent (min/max over sets of rows) and sound: only `l_steady` with `all_held`, or
        // a single zero-atom row covering every length `>= l0`, may return `Empty`.
        let mut next_no_stop = vec![usize::MAX; nodes.len()];
        for v in 0..nodes.len() {
            next_no_stop[v] = match nodes[v].next {
                None if nodes[v].carrier => usize::MAX,
                None => 1,
                Some(nx) => {
                    debug_assert!(nx < v);
                    if !nodes[v].stop {
                        0
                    } else {
                        next_no_stop[nx].saturating_add(1)
                    }
                }
            };
        }
        let next_sep = if nodes[cur].carrier
            && let Some(c) = &h_car
        {
            let mut sep_cache: HashMap<Ints, bool, Digests> = HashMap::default();
            let mut dp = vec![usize::MAX; nodes.len()];
            for v in 0..nodes.len() {
                if let Some(nx) = nodes[v].next {
                    debug_assert!(nx < v);
                    let sep = *sep_cache
                        .entry(nodes[v].head.clone())
                        .or_insert_with(|| !c.subset(&nodes[v].head));
                    dp[v] = if sep {
                        0
                    } else {
                        dp[nx].saturating_add(1)
                    };
                }
            }
            Some(dp)
        } else {
            None
        };
        let first_change = |s: usize| -> usize {
            let hs = nodes[s].ht;
            let steps = l0 - 1;
            let no_stop = if steps < hs {
                let d = next_no_stop[anc.at(s, steps, nodes)];
                if d == usize::MAX {
                    usize::MAX
                } else {
                    l0.saturating_add(d)
                }
            } else if nodes[ns.terminal(s, &anc)].carrier {
                usize::MAX
            } else {
                l0.saturating_add(1)
            };
            let sep = if let Some(ref dp) = next_sep
                && steps < hs
            {
                let d = dp[anc.at(s, steps, nodes)];
                if d == usize::MAX {
                    usize::MAX
                } else {
                    l0.saturating_add(1).saturating_add(d)
                }
            } else {
                usize::MAX
            };
            no_stop.min(sep)
        };
        let row_steady = |s: usize| -> usize {
            let term = ns.terminal(s, &anc);
            nodes[s].ht + if nodes[term].carrier { 1 } else { 2 }
        };
        let l_first = if next_sep.is_some() {
            if !zero_rows.is_empty() {
                let mut clear = l0;
                for &s in &zero_rows {
                    let fc = first_change(s);
                    if fc == usize::MAX {
                        // Proof that the type is empty. The positive values have lengths
                        // `L >= l0` only (`cur` is the first stop), with cells `pl[1 ..= l0]` and,
                        // as `cur` is the carrier (no `next`), cell `H` at every place past `l0`.
                        // Row `s` read at `l0` kept no atom, so each of its cells at places
                        // `1 ..= l0` holds the positive cell there. `fc == MAX` gives, at every
                        // `L > l0`: (a) `next_no_stop` is MAX from the node of place `l0 + 1`, so
                        // every node from there is a stop and the row's terminal is the carrier,
                        // so the row holds at `L` (`holds` in `solve_at_len`); (b) `next_sep` is
                        // MAX from that node, so each of the row's nodes for places
                        // `l0 + 1 ..= ht + 1` has a head containing `H`, and places past `ht + 1`
                        // are carrier cells, read as not separating because every positive cell
                        // from place 2 on lies within `H` (checked above, the `return None`
                        // before `solve_at_len`). Places `1 ..= l0` read the same cells and
                        // nodes as at `l0`. So at every `L >= l0` the row holds with no atom:
                        // it refuses every positive value, and no value is left.
                        return Some(ChainPlan::Empty);
                    }
                    clear = clear.max(fc);
                }
                clear
            } else {
                let m = neg
                    .iter()
                    .filter(|&&(_, s)| holds_l0(s))
                    .map(|&(_, s)| first_change(s))
                    .min()
                    .unwrap_or(usize::MAX);
                if m == usize::MAX { l0 } else { m }
            }
        } else {
            l0.saturating_add(1)
        };
        let l_next = neg
            .iter()
            .filter(|&&(_, s)| holds_l0(s))
            .map(|&(_, s)| row_steady(s))
            .max()
            .unwrap_or(0)
            .max(l0);
        let l_steady = neg
            .iter()
            .map(|&(_, s)| row_steady(s))
            .max()
            .unwrap_or(0)
            .max(l0);
        let mut cands = Vec::with_capacity(3);
        for len in [l_first, l_next, l_steady] {
            if len > l0 {
                cands.push(len);
            }
        }
        cands.sort_unstable();
        cands.dedup();
        let all_rows_held_from_l0 = neg.iter().all(|&(_, s)| {
            let hs = nodes[s].ht;
            let steps = l0 - 1;
            if steps < hs {
                next_no_stop[anc.at(s, steps, nodes)] == usize::MAX
            } else {
                nodes[ns.terminal(s, &anc)].carrier
            }
        });
        let mut pl_ext = pl;
        let mut v = cur;
        let mut ok = true;
        let mut last_tried = l0;
        for cand_len in cands {
            if cand_len <= last_tried {
                continue;
            }
            while pl_ext.len() - 1 < cand_len || !nodes[v].stop {
                if nodes[v].carrier {
                    let c = h_car.as_ref()?;
                    if c.is_empty() {
                        ok = false;
                        break;
                    }
                    pl_ext.push(c.clone());
                } else if let Some(nx) = nodes[v].next {
                    let mut h: Ints = nodes[v].head.clone();
                    if car_pos && let Some(c) = &h_car {
                        h = h.meet(c);
                    }
                    if h.is_empty() {
                        ok = false;
                        break;
                    }
                    pl_ext.push(h);
                    v = nx;
                } else {
                    ok = false;
                    break;
                }
            }
            if !ok {
                break;
            }
            let actual_len = pl_ext.len() - 1;
            last_tried = actual_len;
            let longer_after = nodes[v].next.is_some() || nodes[v].carrier;
            let all_held = actual_len == l_steady && all_rows_held_from_l0;
            if let Some(plan) =
                solve_at_len(actual_len, pl_ext.clone(), longer_after, all_held, None, counts)
            {
                return Some(plan);
            }
        }
    }
    None
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
        for x in atom[i].1.vals.iter() {
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
        for x in atom[i].1.vals.iter() {
            let o = owner.get(x).copied().or_else(|| deepest_cof(x));
            match up {
                None => up = Some(o),
                Some(u) if u == o => {}
                Some(_) => return None,
            }
        }
        parent[i] = up.flatten();
        for x in atom[i].1.vals.iter() {
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

/// Reads a row further from where `rest` says its read stopped (the node of the next place,
/// that place, the row's last place), as `take` reads, until `atoms` holds three again or the
/// row ends; `rest` is then `None` at the end. Whether a kill was met: the row then holds no
/// list of the places' sets and drops out.
fn read_on(
    atoms: &mut Vec<(usize, Ints)>,
    rest: &mut Option<(usize, usize, usize)>,
    nodes: &[Node],
    pl: &[Ints],
    counts: &mut (usize, usize),
) -> bool {
    while atoms.len() < 3 {
        let Some((v, j, last)) = *rest else {
            break;
        };
        *rest = (j < last).then(|| {
            let next = nodes[v]
                .next
                .expect("a cons node below the row's last place");
            (next, j + 1, last)
        });
        counts.0 += 1;
        let hv = &nodes[v].head;
        if pl[j].subset(hv) {
            counts.1 += 1;
        } else if pl[j].disjoint(hv) {
            return true;
        } else {
            atoms.push((j, pl[j].minus(hv)));
        }
    }
    false
}

/// The positions `0 .. n` still in a list: the next one at or after a position, by pointers that
/// skip the removed ones (path compression; each removal is once).
struct Live {
    next: Vec<usize>,
}

impl Live {
    fn new(n: usize) -> Live {
        Live {
            next: (0..=n).collect(),
        }
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
    }
}

const NONE: u32 = u32::MAX;

/// A block's first non-empty cells (at most three, cut after the first kill): offsets from the
/// block's first place, and whether the last one is a kill.
#[derive(Clone, Copy, Default)]
struct Summary {
    len: u8,
    kill: bool,
    off: [u32; 3],
}

/// Ids for equal sets: the id of each item, and one copy of each distinct set.
fn intern<'a>(items: impl Iterator<Item = &'a Ints>) -> (Vec<u32>, Vec<Ints>) {
    let mut id: HashMap<&Ints, u32, Digests> = HashMap::default();
    let mut types: Vec<Ints> = Vec::new();
    let ids = items
        .map(|x| {
            *id.entry(x).or_insert_with(|| {
                types.push(x.clone());
                types.len() as u32 - 1
            })
        })
        .collect();
    (ids, types)
}

/// Method A's tables: the block of level `k` at place `j` and node `v` is the `2^k` cells read
/// from place `j` and node `v` upward. Blocks with equal place classes and equal node classes
/// have equal summaries, memoized by level.
struct Blocks {
    ta: Vec<u32>,
    tb: Vec<u32>,
    ptypes: Vec<Ints>,
    htypes: Vec<Ints>,
    rel: HashMap<(u32, u32), u8, Digests>,
    /// `ca[k][j]`: the class of the level-`k` block of places at `j`, for every level and the
    /// aligned places only. `cb[k][v]` and `up[k][v]`: the class of the level-`k` block of nodes
    /// at `v` and the node `2^k` links above `v`, for the levels built so far; `n_cls[k]`: the
    /// number of node classes of level `k`.
    ca: Vec<Vec<u32>>,
    cb: Vec<Vec<u32>>,
    up: Vec<Vec<u32>>,
    n_cls: Vec<usize>,
    memo: Vec<HashMap<(u32, u32), Summary, Digests>>,
    reads: usize,
    empty: usize,
}

impl Blocks {
    /// `ta` has `l0 + 2` entries (`NONE` at 0 and `l0 + 1`), `tb` one per node. Builds the place
    /// classes of every level and the node classes of level 0.
    fn new(
        ta: Vec<u32>,
        tb: Vec<u32>,
        ptypes: Vec<Ints>,
        htypes: Vec<Ints>,
        nodes: &[Node],
        l0: usize,
    ) -> Blocks {
        debug_assert_eq!(ta.len(), l0 + 2);
        // A walk reads a level-k block only at places `j` with `j - 2` a multiple of `2^k`, and
        // its halves are aligned at level `k - 1`, so only those places get a class: O(l0) for
        // all levels, where every place at every level would cost O(l0 log l0).
        let mut ca = vec![ta.clone()];
        let mut d: HashMap<(u32, u32), u32, Digests> = HashMap::default();
        for k in 1..=level_of(l0) {
            let (h, pa) = (1usize << (k - 1), &ca[k - 1]);
            let mut na = vec![NONE; l0 + 2];
            d.clear();
            for j in (2..=l0 + 1).step_by(2 * h) {
                let r = if j + h <= l0 + 1 { pa[j + h] } else { NONE };
                let n = d.len() as u32;
                na[j] = *d.entry((pa[j], r)).or_insert(n);
            }
            ca.push(na);
        }
        Blocks {
            ca,
            cb: vec![tb.clone()],
            up: vec![
                nodes
                    .iter()
                    .map(|v| v.next.map_or(NONE, |x| x as u32))
                    .collect(),
            ],
            n_cls: vec![htypes.len()],
            memo: vec![HashMap::default()],
            ta,
            tb,
            ptypes,
            htypes,
            rel: HashMap::default(),
            reads: 0,
            empty: 0,
        }
    }

    /// Builds the node levels up to `need_k` not built yet, each in O(n + classes): a level-`k`
    /// class is the pair (class of `v`, class of the node `2^(k-1)` links above) at level `k - 1`.
    /// The nodes are grouped by their own class (counting sort); within a group, a pair is new
    /// when the last own class seen with its upper class differs. Hashing the pairs is also O(n)
    /// per level in expectation, but costs several times more per node, while A's price counts
    /// one unit per node and level built.
    fn grow(&mut self, need_k: usize) {
        for k in self.cb.len()..=need_k {
            let (pb, pu, c) = (&self.cb[k - 1], &self.up[k - 1], self.n_cls[k - 1]);
            let mut at = vec![0usize; c + 1];
            for &b in pb {
                at[b as usize + 1] += 1;
            }
            for x in 1..=c {
                at[x] += at[x - 1];
            }
            let mut ord = vec![0; pb.len()];
            for (v, &b) in pb.iter().enumerate() {
                ord[at[b as usize]] = v;
                at[b as usize] += 1;
            }
            // `last[u]`: the own class last seen with upper class `u` (`c` for no node above),
            // and the number given to that pair.
            let (mut last, mut n) = (vec![(NONE, 0u32); c + 1], 0u32);
            let mut nb = vec![0; pb.len()];
            for &v in &ord {
                let u = if pu[v] == NONE {
                    c
                } else {
                    pb[pu[v] as usize] as usize
                };
                if last[u].0 != pb[v] {
                    last[u] = (pb[v], n);
                    n += 1;
                }
                nb[v] = last[u].1;
            }
            let nu = pu
                .iter()
                .map(|&w| if w == NONE { NONE } else { pu[w as usize] })
                .collect();
            self.n_cls.push(n as usize);
            self.cb.push(nb);
            self.up.push(nu);
            self.memo.push(HashMap::default());
        }
    }

    fn summ(&mut self, k: usize, j: usize, v: usize) -> Summary {
        let key = (self.ca[k][j], self.cb[k][v]);
        if let Some(&s) = self.memo[k].get(&key) {
            return s;
        }
        let r = if k == 0 {
            let (a, b) = (self.ta[j], self.tb[v]);
            let (pt, ht) = (&self.ptypes[a as usize], &self.htypes[b as usize]);
            let c = *self.rel.entry((a, b)).or_insert_with(|| {
                if pt.subset(ht) {
                    0
                } else if pt.disjoint(ht) {
                    2
                } else {
                    1
                }
            });
            self.reads += 1;
            if c == 0 {
                self.empty += 1;
                Summary::default()
            } else {
                Summary {
                    len: 1,
                    kill: c == 2,
                    off: [0; 3],
                }
            }
        } else {
            let h = 1usize << (k - 1);
            let left = self.summ(k - 1, j, v);
            if left.len >= 3 || left.kill {
                left
            } else {
                let right = self.summ(k - 1, j + h, self.up[k - 1][v] as usize);
                let mut out = left;
                for i in 0..right.len as usize {
                    out.off[out.len as usize] = right.off[i] + h as u32;
                    out.len += 1;
                    if right.kill && i + 1 == right.len as usize {
                        out.kill = true;
                    }
                    if out.kill || out.len >= 3 {
                        break;
                    }
                }
                out
            }
        };
        self.memo[k].insert(key, r);
        r
    }

    /// The node `t` links above `v`, on the levels built.
    fn node_at(&self, mut v: usize, mut t: usize) -> usize {
        let mut l = 0;
        while t > 0 {
            if t & 1 == 1 {
                v = self.up[l][v] as usize;
            }
            t >>= 1;
            l += 1;
        }
        v
    }
}

/// The greatest level a walk over places `2 ..= jmax` can ask for.
fn level_of(jmax: usize) -> usize {
    if jmax >= 2 {
        (jmax - 1).ilog2() as usize
    } else {
        0
    }
}

/// The cells of the rows, read window by window over the place offsets `j - 2`: window 0 is
/// offset 0, window `i >= 1` is offsets `[2^(i-1), 2^i)`, one aligned level-`(i-1)` block of
/// [`Blocks`]. Each window reads the rows still open in one of these ways:
/// - A: each row reads the window as one block, by memoized block summaries. Cost: `live
///   (lev + 1)` walk steps, two lookups per memo miss with at most `min(P_k N_k, live 2^(lev-k))`
///   misses at level `k` (`P_k` place classes at the window's aligned places, `N_k` node
///   classes), and one step per node for each node level not built yet.
/// - P(md): list the pairs (place `j`, cons node `v`) whose cell is not empty and give each to
///   the open rows below `v` at height `ht(v) + j - 2`. The pairs come from lists, one per value
///   of a finite place (the cons nodes whose head lacks it) and one of all cons nodes for the
///   cofinite places, each sorted by node height class modulo `md`. A pair reaches a row only
///   if the classes agree, so with `rs` the open rows' classes, place `j` takes from each of its
///   lists only the class `r - (j - 2)`, `r` in `rs`, found by two binary searches. Cost: `1 +
///   2 lgn` per (place, list, class), `lg` per pair taken (two searches among one height's rows),
///   and building and sorting each list not ready. Up to three moduli: `m`, the gcd of the open
///   rows' height differences (the rows are in one class; `top + 1` when they have one height,
///   which compares heights exactly); `lcm(m, g_place)`, with `g_place` the gcd of the
///   differences between the places of each list; and `lcm(m, g_head)`, with `g_head` the gcd of
///   the height differences of the cons nodes with equal heads. The rows may fill several
///   classes modulo the last two, but a list's places (or equal heads) fill one, so a place
///   meets only the nodes whose pairs can reach a row's class. `m` alone keeps one searched
///   class per (place, list) but lets every such pair through (adv/parity3.32768: 82 times
///   slower); the lcm alone can search up to `lcm / m` classes where `m` searches one. A few
///   stray places make `g_place` 1 but leave `g_head` (adv/parity4 to parity6, stray3).
///
/// The window takes the cheapest way. Each price starts as a lower bound (A with the node
/// classes of its highest built level, as classes only split as levels grow; P without its
/// pairs) and the cheapest is made exact (A builds its levels; P builds and sorts its lists and
/// counts its pairs) until the cheapest is exact. A step costs at most its lower bound, which is
/// at most the cheapest exact price, so the window costs O(its cheapest price). Total: the sum
/// over windows of the cheapest price plus O((n + l0 + I) log n + rows log l0). Rows read their
/// windows in order and each window in place order, so each stops at its first kill or third
/// atom, as in the sweep.
fn cells_windows(
    nodes: &[Node],
    anc: &Ancestors,
    pl: &[Ints],
    roots: &mut [Root],
    l0: usize,
    counts: &mut (usize, usize),
) {
    let jmax: Vec<usize> = roots.iter().map(|r| l0.min(nodes[r.s].ht + 1)).collect();
    let open = |r: &Root| r.kill.is_none() && r.atoms.len() < 3;
    let mut live: Vec<usize> = (0..roots.len())
        .filter(|&i| open(&roots[i]) && jmax[i] >= 2)
        .collect();
    let (mut ta, ptypes) = intern(pl[1..].iter());
    ta.insert(0, NONE);
    ta.push(NONE);
    let (tb, htypes) = intern(nodes.iter().map(|v| &v.head));
    // P's lists: list `x < nv` for the value `x` of the finite places (the cofinite heads that
    // exclude it and the finite heads between those that hold it), list `nv` of all cons nodes
    // for the cofinite places. `pv[j]`: the lists of place `j`. The value ids are found once for
    // each place type and each head type: found per place and per node, hashing the values took
    // 40 of the 120 ms of r6parity.65536's setup.
    let cons: Vec<usize> = (0..nodes.len())
        .filter(|&v| nodes[v].next.is_some())
        .collect();
    let fin_heads: Vec<usize> = cons
        .iter()
        .copied()
        .filter(|&v| !nodes[v].head.cof)
        .collect();
    let mut vid: HashMap<&Value, usize, Digests> = HashMap::default();
    let mut pvt: Vec<Option<Vec<usize>>> = vec![None; ptypes.len()];
    for &t in &ta[2..=l0] {
        let t = t as usize;
        if pvt[t].is_none() && !ptypes[t].cof {
            let ids = ptypes[t].vals.iter().map(|x| {
                let n = vid.len();
                *vid.entry(x).or_insert(n)
            });
            pvt[t] = Some(ids.collect());
        }
    }
    let nv = vid.len();
    let all = [nv];
    let pv: Vec<&[usize]> = (0..=l0)
        .map(|j| match j {
            0 | 1 => &[][..],
            _ => pvt[ta[j] as usize].as_deref().unwrap_or(&all),
        })
        .collect();
    let hv: Vec<Vec<usize>> = htypes
        .iter()
        .map(|h| h.vals.iter().filter_map(|x| vid.get(x).copied()).collect())
        .collect();
    let mut excl: Vec<Vec<usize>> = vec![Vec::new(); nv];
    let mut holds: Vec<Vec<usize>> = vec![Vec::new(); nv];
    for &v in cons.iter().filter(|&&v| nodes[v].head.cof) {
        for &x in &hv[tb[v] as usize] {
            excl[x].push(v);
        }
    }
    for (p, &v) in fin_heads.iter().enumerate() {
        for &x in &hv[tb[v] as usize] {
            holds[x].push(p);
        }
    }
    // A builds its node levels only when a window takes it or must price it exactly. Building
    // all levels at once costs O(n log l0) on every input, where lazily the levels cost only
    // what the windows that need them pay (eagerly: 1.15 to 1.28 times slower on s, p, parity).
    let mut bl = Blocks::new(ta, tb, ptypes, htypes, nodes, l0);
    let build = |x: usize| -> Vec<usize> {
        if x == nv {
            return cons.clone();
        }
        let h = &holds[x][..];
        let gaps = std::iter::once(0)
            .chain(h.iter().map(|&p| p + 1))
            .zip(h.iter().copied().chain(std::iter::once(fin_heads.len())));
        excl[x]
            .iter()
            .copied()
            .chain(gaps.flat_map(|(a, b)| fin_heads[a..b].iter().copied()))
            .collect()
    };
    // Each list's building cost and length.
    let size: Vec<(usize, usize)> = (0..nv)
        .map(|x| {
            let e = excl[x].len();
            (e + fin_heads.len(), e + fin_heads.len() - holds[x].len())
        })
        .chain(std::iter::once((cons.len(), cons.len())))
        .collect();
    // The lists built so far, each sorted by height class modulo the `usize` kept with it (any
    // order is sorted modulo 1).
    let mut lists: Vec<Option<(usize, Vec<usize>)>> = vec![None; nv + 1];
    // The open rows by tail height in Euler order, with those still read.
    let top = nodes.iter().map(|v| v.ht).max().unwrap_or(0);
    // A counting sort by Euler index (below n) puts each height's rows in Euler order, ties in
    // row order as `live` has them: O(n + rows), where a comparison sort of each height costs
    // O(rows log rows) (r6parity.65536: 21 of the 120 ms of setup). With the value ids per type,
    // 944M instructions there became 802M, below the sweep's 875M.
    let mut at = vec![0usize; nodes.len() + 1];
    for &i in &live {
        at[anc.tin[roots[i].s] + 1] += 1;
    }
    for t in 1..=nodes.len() {
        at[t] += at[t - 1];
    }
    let mut by_tin = vec![0; live.len()];
    for &i in &live {
        let t = &mut at[anc.tin[roots[i].s]];
        by_tin[*t] = i;
        *t += 1;
    }
    let mut at_ht: Vec<Vec<(usize, usize)>> = vec![Vec::new(); top + 1];
    for &i in &by_tin {
        at_ht[nodes[roots[i].s].ht].push((anc.tin[roots[i].s], i));
    }
    let mut pos = vec![0; roots.len()];
    for l in &at_ht {
        for (k, &(_, i)) in l.iter().enumerate() {
            pos[i] = k;
        }
    }
    let mut left: Vec<Live> = at_ht.iter().map(|l| Live::new(l.len())).collect();
    let log = |n: usize| (n + 2).next_power_of_two().ilog2() as usize;
    let lg = log(at_ht.iter().map(Vec::len).max().unwrap_or(0));
    let lgn = log(nodes.len());
    // Sorting `len` nodes by height class modulo `md` (classes below `min(md, top + 1)`): a
    // counting sort costs `len + min(md, top + 1)`, a comparison sort `len lgn`; the cheaper is
    // taken, so `sort_cost` bounds the work.
    let sort_cost = |len: usize, md: usize| (len + md.min(top + 1)).min(len * lgn);
    let sort_by = |l: &mut Vec<usize>, md: usize| {
        let (key, range) = (|v: usize| nodes[v].ht % md, md.min(top + 1));
        if l.len() + range <= l.len() * lgn {
            let mut at = vec![0usize; range + 1];
            for &v in l.iter() {
                at[key(v) + 1] += 1;
            }
            for c in 1..=range {
                at[c] += at[c - 1];
            }
            let mut o = vec![0; l.len()];
            for &v in l.iter() {
                o[at[key(v)]] = v;
                at[key(v)] += 1;
            }
            *l = o;
        } else {
            l.sort_unstable_by_key(|&v| key(v));
        }
    };
    fn gcd(a: usize, b: usize) -> usize {
        if b == 0 { a } else { gcd(b, a % b) }
    }
    // The places' modulus: list `x` is only at places `j = a_x` modulo `g_place`.
    let (mut g_place, mut first) = (0usize, vec![usize::MAX; nv + 1]);
    for (j, xs) in pv.iter().enumerate().skip(2) {
        for &x in *xs {
            first[x] = first[x].min(j);
            g_place = gcd(g_place, j - first[x]);
        }
    }
    // The heads' modulus: equal heads repeat at one height class modulo `g_head`. Unlike
    // `g_place`, a few stray places leave it, and a stray node with its own head too.
    let (mut g_head, mut first) = (0usize, vec![usize::MAX; bl.htypes.len()]);
    for &v in &cons {
        let a = &mut first[bl.tb[v] as usize];
        if *a == usize::MAX {
            *a = nodes[v].ht;
        }
        g_head = gcd(g_head, nodes[v].ht.abs_diff(*a));
    }
    let mut stamp = vec![usize::MAX; nv + 1];
    let mut seen = vec![usize::MAX; nodes.len()];
    let (mut cand, mut ws) = (Vec::new(), Vec::new());
    let mut mark = vec![usize::MAX; l0 + 2];
    // Each row's node at the first place of the last window A read, and that place's offset:
    // the next A window jumps from there on the levels built, in at most `lev + 1` steps.
    let mut cur: Vec<(usize, usize)> = roots.iter().map(|r| (r.s, 0)).collect();
    let mut i = 0usize;
    while !live.is_empty() {
        let (a, b) = if i == 0 {
            (0, 1)
        } else {
            (1usize << (i - 1), 1usize << i)
        };
        let lev = i.saturating_sub(1);
        let (j0, j1) = (a + 2, (b + 1).min(l0));
        let n_live = live.len();
        // A's place classes per level in the window.
        let p_k: Vec<usize> = (0..=lev)
            .map(|k| {
                let s = i * 64 + k;
                (j0..=j1)
                    .step_by(1 << k)
                    .filter(|&j| std::mem::replace(&mut mark[bl.ca[k][j] as usize], s) != s)
                    .count()
            })
            .collect();
        let cost_a = |bl: &Blocks| {
            let built = bl.cb.len() - 1;
            n_live * (lev + 1)
                + nodes.len() * lev.saturating_sub(built)
                + (0..=lev)
                    .map(|k| 2 * (p_k[k] * bl.n_cls[k.min(built)]).min(n_live << (lev - k)))
                    .sum::<usize>()
        };
        // The moduli with the open rows' classes: `m` with its one class, and `lcm(m, g_place)`
        // and `lcm(m, g_head)` with the classes that occur. A modulus above `top` compares
        // heights exactly (each live row is higher than `j - 2`, so no class wraps), and is
        // kept at `top + 1`.
        let h0 = nodes[roots[live[0]].s].ht;
        let m = live
            .iter()
            .fold(0, |d, &r| gcd(d, nodes[roots[r].s].ht.abs_diff(h0)));
        let md0 = if m == 0 { top + 1 } else { m };
        let mut mods = vec![(md0, vec![h0 % md0])];
        for d in [g_place, g_head] {
            if m == 0 || d == 0 || m % d == 0 {
                continue;
            }
            let md = (m / gcd(m, d))
                .checked_mul(d)
                .map_or(top + 1, |x| x.min(top + 1));
            if mods.iter().all(|q| q.0 != md) {
                let mut rs: Vec<usize> = live.iter().map(|&r| nodes[roots[r].s].ht % md).collect();
                rs.sort_unstable();
                rs.dedup();
                mods.push((md, rs));
            }
        }
        let want = |md: usize, rs: &[usize], j: usize, ws: &mut Vec<usize>| {
            ws.clear();
            ws.extend(rs.iter().map(|&r| (r + md - (j - 2) % md) % md));
        };
        let class = |md: usize, v: usize| nodes[v].ht % md;
        let in_class = |l: &[usize], md: usize, c: usize| {
            l.partition_point(|&v| class(md, v) < c)..l.partition_point(|&v| class(md, v) <= c)
        };
        // P's price with modulus `md`: with `exact` false, a lower bound (the searches, and
        // building and sorting the lists not ready); with `exact` true, the lists are made ready
        // and the pairs counted. `key` marks the lists already priced in this call.
        let mut price_p = |md: usize,
                           rs: &[usize],
                           exact: bool,
                           key: usize,
                           lists: &mut Vec<Option<(usize, Vec<usize>)>>| {
            let mut c = 0;
            for (j, xs) in pv.iter().enumerate().take(j1 + 1).skip(j0) {
                want(md, rs, j, &mut ws);
                for &x in *xs {
                    c += rs.len() * (1 + 2 * lgn);
                    if std::mem::replace(&mut stamp[x], key) != key {
                        let (cost, len) = size[x];
                        let ready = lists[x].as_ref().map(|l| l.0);
                        if ready.is_none() {
                            c += cost;
                        }
                        if ready != Some(md) && md != 1 {
                            c += sort_cost(len, md);
                        }
                        if exact {
                            let l = lists[x].get_or_insert_with(|| (1, build(x)));
                            if l.0 != md && md != 1 {
                                sort_by(&mut l.1, md);
                                l.0 = md;
                            }
                        }
                    }
                    if exact {
                        let l = &lists[x].as_ref().expect("made ready above").1;
                        c += ws.iter().map(|&w| in_class(l, md, w).len()).sum::<usize>() * lg;
                    }
                }
            }
            c
        };
        // The prices, each with whether it is exact: 0 is A, `1 + q` is P with `mods[q]`.
        let mut price = vec![(cost_a(&bl), bl.cb.len() > lev)];
        for (q, (md, rs)) in mods.iter().enumerate() {
            price.push((price_p(*md, rs, false, i * 8 + q, &mut lists), false));
        }
        let way = loop {
            let w = (0..price.len()).min_by_key(|&w| price[w].0).unwrap_or(0);
            if price[w].1 {
                break w;
            }
            price[w] = if w == 0 {
                bl.grow(lev);
                (cost_a(&bl), true)
            } else {
                let (md, rs) = &mods[w - 1];
                (price_p(*md, rs, true, i * 8 + 3 + w, &mut lists), true)
            };
        };
        let mut done: Vec<usize> = Vec::new();
        if way == 0 {
            for &r in &live {
                let start = bl.node_at(cur[r].0, j0 - 2 - cur[r].1);
                cur[r] = (start, j0 - 2);
                let (mut j, mut v, mut k) = (j0, start, lev);
                let mut rem = j1.min(jmax[r]) + 1 - j0;
                'walk: while rem > 0 {
                    while (1usize << k) > rem {
                        k -= 1;
                    }
                    let ev = bl.summ(k, j, v);
                    for e in 0..ev.len as usize {
                        let (jj, kill) =
                            (j + ev.off[e] as usize, ev.kill && e + 1 == ev.len as usize);
                        let rr = &mut roots[r];
                        if kill {
                            rr.kill = Some(jj);
                        } else {
                            let w = bl.node_at(start, jj - j0);
                            rr.atoms.push((jj, pl[jj].minus(&nodes[w].head)));
                        }
                        if !open(rr) {
                            done.push(r);
                            break 'walk;
                        }
                    }
                    j += 1 << k;
                    v = bl.up[k][v] as usize;
                    rem -= 1 << k;
                }
            }
        } else {
            let (md, rs) = &mods[way - 1];
            for j in j0..=j1 {
                want(*md, rs, j, &mut ws);
                cand.clear();
                for &x in pv[j] {
                    // Made ready when priced; sorted again if another modulus was priced since,
                    // at most the sort its price counted.
                    let l = lists[x].as_mut().expect("made ready when priced");
                    if l.0 != *md && *md != 1 {
                        sort_by(&mut l.1, *md);
                        l.0 = *md;
                    }
                    for &w in &ws {
                        cand.extend(l.1[in_class(&l.1, *md, w)].iter().copied().filter(|&v| {
                            std::mem::replace(&mut seen[v], j) != j
                                && !(pl[j].cof && pl[j].subset(&nodes[v].head))
                        }));
                    }
                }
                for &v in &cand {
                    let h = nodes[v].ht + j - 2;
                    if h > top || at_ht[h].is_empty() {
                        continue;
                    }
                    let l = &at_ht[h];
                    let (ta, tb) = (anc.tin[v], anc.tout[v]);
                    let end = l.partition_point(|&(t, _)| t <= tb);
                    let mut k = left[h].find(l.partition_point(|&(t, _)| t < ta));
                    while k < end {
                        let r = l[k].1;
                        if take(&mut roots[r], j, pl, &nodes[v].head, counts) {
                            left[h].remove(k);
                            done.push(r);
                        }
                        k = left[h].find(k + 1);
                    }
                }
            }
        }
        for &r in &done {
            let h = nodes[roots[r].s].ht;
            if left[h].find(pos[r]) == pos[r] {
                left[h].remove(pos[r]);
            }
        }
        live.retain(|&r| open(&roots[r]) && jmax[r] >= b + 2);
        i += 1;
    }
    counts.0 += bl.reads;
    counts.1 += bl.empty;
}

#[cfg(test)]
mod bench;

/// Plan row PERF-value-key-sites-bench: the maps of [`forest`] keyed by `Value`, `first_out` and
/// `owner`, at small sizes; `bench.rs` runs them at n and 8n.
#[cfg(test)]
mod forest_tests {
    use num_bigint::BigInt;

    use super::*;
    use crate::num::Rat;

    pub(super) fn finite(vals: impl IntoIterator<Item = Value>) -> Ints {
        Ints::new(false, vals.into_iter().collect())
    }

    pub(super) fn cofinite(vals: impl IntoIterator<Item = Value>) -> Ints {
        Ints::new(true, vals.into_iter().collect())
    }

    /// 10^19, past 64 bits, from its digits and from a decimal exponent, and 10^19 + 1.
    fn wide() -> (Value, Value, Value) {
        let digits = Value::int_text(&format!("1{}", "0".repeat(19)), 10)
            .expect("memory")
            .expect("digits");
        let r = Rat::decimal("1e19").expect("memory").expect("a decimal");
        let next = Value::int(BigInt::from(10_u64.pow(19)) + 1);
        (digits, Value::integer(r), next)
    }

    /// Equal integers built two ways are one key of `owner` and of `first_out`, and an integer
    /// one apart is another: the finite atom `{10^19}` (as a decimal) lies in `{10^19, 1}` (from
    /// digits), `{10^19 + 1}` in no finite atom; under the cofinite chain, all integers, then all
    /// but `10^19`, each finite atom's parent is the deepest cofinite atom that holds its values.
    #[test]
    fn equal_wide_integers_are_one_key_of_the_forest() {
        let (digits, decimal, next) = wide();
        let atom = vec![
            (0, finite([digits.clone(), Value::Int(1)])),
            (0, finite([decimal.clone()])),
            (0, finite([next.clone()])),
        ];
        let mut parent = vec![None; atom.len()];
        assert_eq!(forest(&[0, 1, 2], &atom, &mut parent), Some(()));
        assert_eq!(parent, vec![None, Some(0), None]);

        let atom = vec![
            (0, cofinite([])),
            (0, cofinite([digits])),
            (0, finite([decimal])),
            (0, finite([Value::Int(2)])),
            (0, finite([next])),
        ];
        let mut parent = vec![None; atom.len()];
        assert_eq!(forest(&[0, 1, 2, 3, 4], &atom, &mut parent), Some(()));
        assert_eq!(parent, vec![None, Some(0), Some(0), Some(1), Some(1)]);
    }

    /// Two finite atoms that share one value and not the other cross, and the forest says so.
    #[test]
    fn crossing_atoms_of_wide_integers_are_found() {
        let (digits, decimal, next) = wide();
        let atom = vec![
            (0, finite([digits, Value::Int(1)])),
            (0, finite([decimal, next])),
        ];
        let mut parent = vec![None; atom.len()];
        assert_eq!(forest(&[0, 1], &atom, &mut parent), None);
    }
}

#[cfg(test)]
mod windows_tests {
    use super::*;

    /// A row's kill and atoms.
    type Cells = (Option<usize>, Vec<(usize, Ints)>);

    /// The cells of one row by the definition: walk up from the row's node, one place at a time.
    fn walk(r: &mut Root, nodes: &[Node], pl: &[Ints], l0: usize) {
        if r.kill.is_some() || r.atoms.len() >= 3 {
            return;
        }
        let mut v = r.s;
        for (j, p) in pl
            .iter()
            .enumerate()
            .take(l0.min(nodes[r.s].ht + 1) + 1)
            .skip(2)
        {
            let hv = &nodes[v].head;
            if !p.subset(hv) {
                if p.disjoint(hv) {
                    r.kill = Some(j);
                    return;
                }
                r.atoms.push((j, p.minus(hv)));
                if r.atoms.len() >= 3 {
                    return;
                }
            }
            v = nodes[v]
                .next
                .expect("a cons node below the row's last place");
        }
    }

    /// Random forests, long chains among them, with few values (so method A's summaries repeat)
    /// and more values (so the pair listing wins), finite and cofinite heads and places, and rows
    /// with an atom or a kill at place 1: `cells_windows` gives each row the walk's cells.
    #[test]
    fn windows_agree_with_the_walk() {
        let mut seed = crate::seed::seed("windows_agree_with_the_walk") | 1;
        let mut rnd = |n: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % n.max(1)
        };
        for case in 0..600u64 {
            let sigma = 1 + rnd(if case % 2 == 0 { 3 } else { 12 }) as i64;
            let set = |rnd: &mut dyn FnMut(u64) -> u64| {
                Ints::new(
                    rnd(5) < 2,
                    (0..rnd(4))
                        .map(|_| Value::Int(rnd(sigma as u64) as i64))
                        .collect(),
                )
            };
            let n = 2 + rnd(if case % 3 == 0 { 400 } else { 60 }) as usize;
            let chain = case % 4 == 0;
            let mut nodes = vec![Node {
                stop: false,
                head: Ints::new(false, BTreeSet::new()),
                next: None,
                carrier: false,
                ht: 0,
            }];
            for i in 1..n {
                let p = if chain { i - 1 } else { rnd(i as u64) as usize };
                let head = set(&mut rnd);
                let ht = nodes[p].ht + 1;
                nodes.push(Node {
                    stop: false,
                    head,
                    next: Some(p),
                    carrier: false,
                    ht,
                });
            }
            let l0 = nodes.iter().map(|v| v.ht).max().unwrap() + rnd(4) as usize;
            let mut pl = vec![Ints::new(false, BTreeSet::new())];
            for _ in 1..=l0 {
                pl.push(set(&mut rnd));
            }
            let mut roots: Vec<Root> = Vec::new();
            for s in 0..n {
                if rnd(5) < 3 {
                    let mut r = Root {
                        row: Row::new(Vec::new()),
                        s,
                        kill: None,
                        atoms: Vec::new(),
                    };
                    match rnd(10) {
                        0 => r.kill = Some(1),
                        1..=3 => r.atoms.push((1, set(&mut rnd))),
                        _ => {}
                    }
                    roots.push(r);
                }
            }
            let mut want: Vec<Cells> = Vec::new();
            for r in &roots {
                let mut w = Root {
                    row: Row::new(Vec::new()),
                    s: r.s,
                    kill: r.kill,
                    atoms: r.atoms.clone(),
                };
                walk(&mut w, &nodes, &pl, l0);
                want.push((w.kill, w.atoms));
            }
            let anc = Ancestors::new(&nodes);
            cells_windows(&nodes, &anc, &pl, &mut roots, l0, &mut (0, 0));
            for (k, r) in roots.iter_mut().enumerate() {
                // `decide_counted` sorts the atoms by place; the reads may find them in any order.
                r.atoms.sort_unstable_by_key(|a| a.0);
                assert_eq!(
                    (r.kill, &r.atoms),
                    (want[k].0, &want[k].1),
                    "case {case}, row {k}"
                );
            }
        }
    }
}
