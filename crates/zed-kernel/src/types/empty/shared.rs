//! The items that [`super`] and its children `escape` and `sweep` all read: the type-keyed maps,
//! the chain plan the escape count returns, the 2-CNF it fills, and the list step. They live in a
//! file below all three so that no import cycle runs between the files (ZED_PORT_GAPS gap 10,
//! test S.1f); the procedures over them stay where they were.

use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap};
use std::hash::BuildHasherDefault;

use super::super::{Lits, Parts, Row, Type};
use crate::digest::Digest;

/// The hasher of the maps and sets keyed by types: a type hashes as its digest, made once when it
/// is built, so a lookup reads one node of the type, where a search of a `BTreeMap` compared the
/// key with some `log n` others, each comparison reading another node (EMPTY-morphism-next).
/// Equal digests are told apart by `Eq`, which compares contents.
pub(super) type Digests = BuildHasherDefault<Digest>;

/// A map keyed by retained types, bucketed by their cached presentation hash.
// Complexity tradeoff: a primary fingerprint is shared by renamed copies of one form;
// using it for table identity gave b-way collisions and repeated structural comparisons.
// The presentation hash separates those copies in expected O(1); genuine hash collisions
// retain one inline key or a BTreeMap, O(log b) comparisons, each checking real contents.
pub(super) struct ByType<V>(HashMap<u64, Tied<V>, Digests>);

/// The keys of one digest in a [`ByType`], with their values.
enum Tied<V> {
    One(Type, V),
    Many(BTreeMap<Type, V>),
}

impl<V> Default for ByType<V> {
    fn default() -> Self {
        ByType::new()
    }
}

impl<V> ByType<V> {
    pub(super) const fn new() -> Self {
        ByType(HashMap::with_hasher(Digests::new()))
    }

    pub(super) fn get(&self, t: &Type) -> Option<&V> {
        match self.0.get(&t.name_digest())? {
            Tied::One(k, v) => (k == t).then_some(v),
            Tied::Many(m) => m.get(t),
        }
    }

    pub(super) fn get_mut(&mut self, t: &Type) -> Option<&mut V> {
        match self.0.get_mut(&t.name_digest())? {
            Tied::One(k, v) => (*k == *t).then_some(v),
            Tied::Many(m) => m.get_mut(t),
        }
    }

    pub(super) fn contains_key(&self, t: &Type) -> bool {
        self.get(t).is_some()
    }

    pub(super) fn insert(&mut self, t: Type, v: V) -> Option<V> {
        let mut v = Some(v);
        let slot = self
            .entry(t)
            .or_insert_with(|| v.take().expect("one value"));
        v.map(|v| std::mem::replace(slot, v))
    }

    pub(super) fn remove(&mut self, t: &Type) -> Option<V> {
        let d = t.name_digest();
        let tied = self.0.get_mut(&d)?;
        let (got, empty) = match tied {
            Tied::One(k, _) if *k != *t => return None,
            Tied::One(..) => (None, true),
            Tied::Many(m) => {
                let v = m.remove(t);
                (v, m.is_empty())
            }
        };
        if !empty {
            return got;
        }
        match self.0.remove(&d) {
            Some(Tied::One(_, v)) => Some(v),
            _ => got,
        }
    }

    pub(super) fn clear(&mut self) {
        self.0.clear();
    }

    pub(super) fn retain(&mut self, mut keep: impl FnMut(&Type, &mut V) -> bool) {
        self.0.retain(|_, tied| match tied {
            Tied::One(k, v) => keep(k, v),
            Tied::Many(m) => {
                m.retain(|k, v| keep(k, v));
                !m.is_empty()
            }
        });
    }

    pub(super) fn entry(&mut self, t: Type) -> TypeEntry<'_, V> {
        TypeEntry { map: self, key: t }
    }
}

impl<V> std::ops::Index<&Type> for ByType<V> {
    type Output = V;
    fn index(&self, t: &Type) -> &V {
        self.get(t).expect("a key of the map")
    }
}

impl<V> Extend<(Type, V)> for ByType<V> {
    fn extend<I: IntoIterator<Item = (Type, V)>>(&mut self, items: I) {
        for (t, v) in items {
            self.insert(t, v);
        }
    }
}

/// The place of a key in a [`ByType`], filled or not.
pub(super) struct TypeEntry<'a, V> {
    map: &'a mut ByType<V>,
    key: Type,
}

impl<'a, V> TypeEntry<'a, V> {
    pub(super) fn or_insert_with(self, f: impl FnOnce() -> V) -> &'a mut V {
        let tied = match self.map.0.entry(self.key.name_digest()) {
            Entry::Vacant(e) => {
                let Tied::One(_, v) = e.insert(Tied::One(self.key, f())) else {
                    unreachable!("just put in")
                };
                return v;
            }
            Entry::Occupied(e) => e.into_mut(),
        };
        if let Tied::One(k, _) = tied
            && *k != self.key
        {
            let Tied::One(k, v) = std::mem::replace(tied, Tied::Many(BTreeMap::new())) else {
                unreachable!("matched above")
            };
            let Tied::Many(m) = tied else {
                unreachable!("just put in")
            };
            m.insert(k, v);
        }
        match tied {
            Tied::One(_, v) => v,
            Tied::Many(m) => m.entry(self.key).or_insert_with(f),
        }
    }

    pub(super) fn or_insert(self, v: V) -> &'a mut V {
        self.or_insert_with(|| v)
    }

    pub(super) fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }
}

/// What [`super::Searching::prefix_chains`] finds for a list type whose link payload is a period-1
/// carrier cycle less prefix chains: either no list remains, or a witness list with item types
/// `heads` (from front to back) ending in `stop` remains.
#[derive(Clone)]
pub(super) enum ChainPlan {
    Empty,
    Inhabited {
        stop: std::sync::Arc<str>,
        link: std::sync::Arc<str>,
        heads: Vec<Type>,
        /// For refused rows of the link payload, an item of the witness each should miss
        /// ([`ChainHint`]); [`super::Searching::check_chain_witness`] checks each one itself.
        hints: Vec<(Row, ChainHint)>,
    },
}

/// Where a witness list should leave one refused row, for [`super::Searching::check_chain_witness`]:
/// `Miss(i)`, its item `i` (from 0) is not in the row's head at that place; `Len`, the row's
/// tail holds no list of the witness's length. A hint that does not hold costs only the
/// row's full walk.
#[derive(Clone, Copy, Debug)]
pub(super) enum ChainHint {
    Miss(usize),
    Len,
}

/// A literal of a 2-CNF: variable `v` true is `2 * v`, false is `2 * v + 1`, so `l ^ 1` is the
/// complement of `l`.
pub(super) type Literal2 = usize;

/// A 2-CNF read from a tuple part (step T6-2sat): its variables, and its clauses, each one or
/// two literals (a clause of one literal holds it twice).
pub(super) struct TwoSat {
    pub(super) vars: usize,
    pub(super) clauses: Vec<(Literal2, Literal2)>,
    /// The variable of each meet under an `or`, by the key of its node ([`super::At::key`]).
    pub(super) meets: HashMap<(u64, bool, u8), Literal2>,
}

impl TwoSat {
    /// A variable of its own, as its literal `true`.
    pub(super) fn fresh(&mut self) -> Literal2 {
        self.vars += 1;
        2 * (self.vars - 1)
    }

    /// A value of each variable that holds every clause, or `None` when there is none: a
    /// variable and its complement in one strongly connected component of the implication
    /// graph (`!a -> b` and `!b -> a` for each clause `a | b`). The components are found by
    /// Tarjan's algorithm on an explicit stack, each completed after every component it
    /// reaches, so a literal is set true when its component is completed before its
    /// complement's: then nothing true implies anything false. Time linear in the variables
    /// and clauses.
    pub(super) fn solve(&self) -> Option<Vec<bool>> {
        let n = 2 * self.vars;
        // The edges out of each literal, as one list cut at `start`.
        let mut start = vec![0usize; n + 1];
        for &(a, b) in &self.clauses {
            start[(a ^ 1) + 1] += 1;
            start[(b ^ 1) + 1] += 1;
        }
        for i in 0..n {
            start[i + 1] += start[i];
        }
        let mut next = start.clone();
        let mut to = vec![0usize; start[n]];
        for &(a, b) in &self.clauses {
            for (from, x) in [(a ^ 1, b), (b ^ 1, a)] {
                to[next[from]] = x;
                next[from] += 1;
            }
        }
        const NONE: usize = usize::MAX;
        let (mut index, mut low, mut comp) = (vec![NONE; n], vec![0; n], vec![NONE; n]);
        let (mut found, mut comps) = (0, 0);
        let mut on: Vec<usize> = Vec::new();
        // The walk: each literal entered and the position of its next edge.
        let mut walk: Vec<(usize, usize)> = Vec::new();
        for root in 0..n {
            if index[root] != NONE {
                continue;
            }
            index[root] = found;
            low[root] = found;
            found += 1;
            on.push(root);
            walk.push((root, start[root]));
            while let Some(&(v, e)) = walk.last() {
                if e < start[v + 1] {
                    let w = to[e];
                    let top = walk.len() - 1;
                    walk[top].1 += 1;
                    if index[w] == NONE {
                        index[w] = found;
                        low[w] = found;
                        found += 1;
                        on.push(w);
                        walk.push((w, start[w]));
                    } else if comp[w] == NONE {
                        low[v] = low[v].min(index[w]);
                    }
                    continue;
                }
                walk.pop();
                if let Some(&(u, _)) = walk.last() {
                    low[u] = low[u].min(low[v]);
                }
                if low[v] == index[v] {
                    while let Some(w) = on.pop() {
                        comp[w] = comps;
                        if w == v {
                            break;
                        }
                    }
                    comps += 1;
                }
            }
        }
        (0..self.vars)
            .map(|v| (comp[2 * v] != comp[2 * v + 1]).then(|| comp[2 * v] < comp[2 * v + 1]))
            .collect()
    }
}

/// Whether `p` has no value but atoms.
pub(super) fn only_atoms(p: &Parts) -> bool {
    let lits = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings];
    p.bools == 0
        && lits
            .iter()
            .all(|l: &&Lits| !l.cofinite && l.values.is_empty())
        && p.morphisms.is_leaf() == Some(false)
}

/// The parts of one step of a list, as [`list_step`] gives them.
pub(super) type Step = (Option<std::sync::Arc<str>>, std::sync::Arc<str>, Type, Type);

/// One step of a list: the stop atom of `t` if it has one, the link atom, its item, and the
/// rest; none when `t` is not of that shape.
pub(super) fn list_step(t: &Type) -> Option<Step> {
    let p = t.p();
    if p.structs
        || p.tuples.rest
        || !p.tuples.lens.is_empty()
        || !only_atoms(&p)
        || p.atoms.cofinite
    {
        return None;
    }
    let (mut stop, mut link) = (None, None);
    for (name, a) in &p.atoms.names {
        match (a.bare, a.payload == Type::empty()) {
            (true, true) if stop.is_none() => stop = Some(name.clone()),
            (false, true) => {}
            (false, false) if link.is_none() => link = Some((name.clone(), a.payload.clone())),
            _ => return None,
        }
    }
    let (name, payload) = link?;
    let q = payload.p();
    // Complexity tradeoff: the general payload search can require an exponential subset
    // construction over recursive alternatives. A functional list step is read in
    // O(atom names + pair BDD nodes), but only with at most one stop, one link and positional pairs
    // alone. Mixed named/positional payloads or multiple names stay on the general path.
    // Check the constant-time shape flags before walking the pair BDD (R7-C2/C3).
    if q.structs || q.tuples.rest || q.tuples.lens.len() != 1 {
        return None;
    }
    let f = q.tuples.lens.get(&2)?;
    let atoms = f.distinct_atoms();
    if atoms.len() != 1 || !f.eval(&|_| true) {
        return None;
    }
    if f.eval(&|_| false) {
        return None;
    }
    Some((stop, name, atoms[0][0].clone(), atoms[0][1].clone()))
}
