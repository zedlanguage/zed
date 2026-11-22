//! The items that [`super`] and its children `escape` and `sweep` all read: the type-keyed maps,
//! the chain plan the escape count returns, the 2-CNF it fills, and the list step. They live in a
//! file below all three so that no import cycle runs between the files (ZED_PORT_GAPS gap 10,
//! test S.1f); the procedures over them stay where they were.

use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap};
use std::hash::BuildHasherDefault;

use super::super::{Lits, Parts, Row, Type};
use crate::digest::{Digest, text_hash};

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
pub(super) struct ByType<V> {
    map: HashMap<u64, Tied<V>, Digests>,
    /// Test hook: the bits of each digest the map keys by. A unit test sets it to 0, so that
    /// every key shares one digest and the arms for a digest of two keys or more
    /// (`Tied::Many`) run in the normal build, where two types of one digest are not found.
    #[cfg(test)]
    mask: u64,
}

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
        ByType {
            map: HashMap::with_hasher(Digests::new()),
            #[cfg(test)]
            mask: !0,
        }
    }

    /// A map that keys by the bits `mask` of each digest (test hook, see `mask`).
    #[cfg(test)]
    const fn with_mask(mask: u64) -> Self {
        ByType {
            map: HashMap::with_hasher(Digests::new()),
            mask,
        }
    }

    /// The digest `t` is keyed by: its presentation digest hashed by the process's seeded text
    /// hash ([`text_hash`]), not the digest itself (row KERNEL-bytype-flooding).
    ///
    /// Why the seed. A type can hold the program's literal values, and its digest is built by
    /// unseeded [`crate::digest::step`]s, each of which can be inverted in its argument (the
    /// module comment of `types::bdd::set` says so), so a program could choose literals whose
    /// types take digests that the map's own hash ([`Digests`], also unseeded) sends to one
    /// probe sequence of the table: each lookup would then walk all of them, `O(n)` and
    /// `O(n^2)` over a run (hash flooding; the rule at [`crate::digest::DigestMap`]: keys of a
    /// `Digest` map are never chosen by the program). With the seed the program does not know,
    /// distinct digests spread as foldhash spreads its keys. Digests a program makes equal
    /// still meet in one entry, where [`Tied::Many`] tells them apart by an ordered map,
    /// `O(log b)` comparisons for `b` keys of one digest, so equal digests cost a log factor,
    /// not a walk. A name digest is folded from the parts of the type alone (`types.rs`,
    /// `name_digest`), so equal types have equal digests and still meet in one entry. The order
    /// of the table now follows the run's seed; no caller reads it: the map is only looked up,
    /// and `retain`, its one walk, keeps or drops each entry by its own key and value alone.
    /// Test: `the_key_is_the_seeded_hash_of_the_digest` checks the key; no test builds a
    /// program whose digests collide, which needs inverting the digest steps.
    fn digest(&self, t: &Type) -> u64 {
        let d = text_hash(&t.name_digest());
        #[cfg(test)]
        let d = d & self.mask;
        d
    }

    pub(super) fn get(&self, t: &Type) -> Option<&V> {
        match self.map.get(&self.digest(t))? {
            Tied::One(k, v) => (k == t).then_some(v),
            Tied::Many(m) => m.get(t),
        }
    }

    pub(super) fn get_mut(&mut self, t: &Type) -> Option<&mut V> {
        let d = self.digest(t);
        match self.map.get_mut(&d)? {
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
        let d = self.digest(t);
        let tied = self.map.get_mut(&d)?;
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
        match self.map.remove(&d) {
            Some(Tied::One(_, v)) => Some(v),
            _ => got,
        }
    }

    pub(super) fn clear(&mut self) {
        self.map.clear();
    }

    pub(super) fn retain(&mut self, mut keep: impl FnMut(&Type, &mut V) -> bool) {
        self.map.retain(|_, tied| match tied {
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
        let d = self.map.digest(&self.key);
        let tied = match self.map.map.entry(d) {
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

/// Where a witness list should leave one refused row, for
/// [`super::Searching::check_chain_witness`]: `Miss(i)`, its item `i` (from 0) is not in the row's
/// head at that place; `Len`, the row's tail holds no list of the witness's length. A hint that
/// does not hold costs only the row's full walk.
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
    pub(super) meets: HashMap<(u64, bool), Literal2>,
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
    ///
    /// Source: B. Aspvall, M. F. Plass and R. E. Tarjan, "A linear-time algorithm for testing
    /// the truth of certain quantified boolean formulas", Inform. Process. Lett. 8(3):121-123,
    /// 1979, doi:10.1016/0020-0190(79)90002-4 (Crossref and the text checked 2026-11-20). It
    /// takes the strong components "in reverse topological order" from Tarjan's algorithm, and
    /// for each: "If S is marked, do nothing. Otherwise if S = S̄ then stop: C is
    /// unsatisfiable. Otherwise mark S true and S̄ false." The components come from R. Tarjan,
    /// "Depth-first search and linear graph algorithms", SIAM J. Comput. 1(2):146-160, 1972,
    /// doi:10.1137/0201010 (Crossref checked 2026-11-20). Departure: the recursion is on an
    /// explicit stack. Test: `two_sat_solve_agrees_with_enumeration_and_its_solutions_hold`
    /// compares with enumeration on random sets of up to 12 variables and checks each solution.
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
        let (mut comp, mut comps) = (vec![usize::MAX; n], 0);
        zed_graph::tarjan(
            n,
            0..n,
            |v| &to[start[v]..start[v + 1]],
            |&w| Some(w),
            |members| {
                for &w in members.iter() {
                    comp[w] = comps;
                }
                comps += 1;
            },
        );
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

/// Whether `p` has no value but atoms of finitely many names: no scalar, record, tuple or
/// function, and not every atom name.
pub(super) fn finite_atoms_only(p: &Parts) -> bool {
    !p.structs && p.tuples.is_default() && only_atoms(p) && !p.atoms.cofinite()
}

/// The parts of one step of a list, as [`list_step`] gives them.
pub(super) type Step = (Option<std::sync::Arc<str>>, std::sync::Arc<str>, Type, Type);

/// One step of a list: the stop atom of `t` if it has one, the link atom, its item, and the
/// rest; none when `t` is not of that shape.
pub(super) fn list_step(t: &Type) -> Option<Step> {
    let p = t.p();
    if !finite_atoms_only(&p) {
        return None;
    }
    let (mut stop, mut link) = (None, None);
    for (name, a) in p.atoms.names() {
        match (a.bare, a.payload == Type::empty()) {
            (true, true) if stop.is_none() => stop = Some(name.clone()),
            // A finite map of atoms lists no name whose part is none, the bare atom out and no
            // payload (`Atoms::set`), and the map is finite here.
            (false, true) => unreachable!("a finite map of atoms lists no name of no atom"),
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
    // A part over one atom is that atom, its complement or a leaf: `Part::zip_at_once` gives `a`
    // for `a | a` and `a & a`, and `Connect::zipped` a leaf for `a | !a` and `a & !a`. One true
    // where its atom holds is the atom, false where it fails; the check stays for release builds.
    // Tests: no test reaches this arm (crate COMPLETENESS.md, row TEST-types-unreached-paths-3),
    // so the `debug_assert!` checks the claim only on the parts the suite builds; it cannot
    // catch a part built without `zip_at_once` or `zipped`.
    if f.eval(&|_| false) {
        debug_assert!(false, "a part over one atom true at both of its values");
        return None;
    }
    Some((stop, name, atoms[0][0].clone(), atoms[0][1].clone()))
}

/// One step of a list type of the link atom `link` and the stop atom `stop`, as the two chain
/// readers read it: `find_prefix_chains` (its `step_of`) and `check_chain_witness` (its
/// `verify_step`), which before TEST-kernel-unreached-paths-12 each held a copy of this reading.
pub(super) enum StepShape {
    /// The type is one step of a list ([`list_step`]) of these atoms: whether it holds `stop`,
    /// the item and the rest.
    List(bool, Type, Type),
    /// The type is `stop` and nothing else.
    Stop,
    /// The type holds `stop` when `has_stop`, and `link` of each pair in the union of `rows`, one
    /// row or more, and of no other pair.
    Rows { has_stop: bool, rows: Vec<Row> },
}

/// The step of `x` ([`StepShape`]), and whether the payload of `link` in `x` also holds records
/// (`structs` of its parts). No record is a pair, so the step decides every list of `x` either
/// way; it is `x` itself only without records. None when `x` holds a value other than `stop`
/// and `link` atoms, another atom, a bare `link`, `stop` with a payload, a payload of `link` with
/// a tuple of a length other than two, or pairs that are not a union of rows
/// ([`Part::union_rows`](super::super::bdd::Part::union_rows)). Cost: that of [`list_step`], and
/// one pass over the atom names of `x` and the pair part of its payload.
pub(super) fn step_shape(x: &Type, link: &str, stop: &str) -> Option<(StepShape, bool)> {
    if let Some((s, l, h, next)) = list_step(x) {
        if *l != *link || s.as_deref().is_some_and(|st| st != stop) {
            return None;
        }
        // `list_step` takes no payload with records.
        return Some((StepShape::List(s.is_some(), h, next), false));
    }
    let xp = x.p();
    if !finite_atoms_only(&xp) {
        return None;
    }
    let mut has_stop = false;
    let mut l_payload: Option<Type> = None;
    for (n, a) in xp.atoms.names() {
        match (a.bare, a.payload == Type::empty()) {
            (true, true) if **n == *stop => has_stop = true,
            // Never met: the atoms are finite (tested above), and `Atoms::set`, the one writer of
            // `names` (module `types::atoms`), keeps no name whose part is `AtomPart::none()`
            // there.
            (false, true) => unreachable!("a finite atoms map lists a name with no part"),
            (false, false) if **n == *link && l_payload.is_none() => {
                l_payload = Some(a.payload.clone());
            }
            _ => return None,
        }
    }
    // No `link`: `x`'s lists are `stop` or none, as with no rows below.
    let Some(l_payload) = l_payload else {
        return has_stop.then_some((StepShape::Stop, false));
    };
    let xq = l_payload.p();
    if xq.tuples.rest || xq.tuples.lens.len() != 1 || !xq.tuples.lens.contains_key(&2) {
        return None;
    }
    // Typed, so that the import graph (zed-tools `imports`, test group s_01f) reads
    // `rows.is_empty()` as a call on a `Vec` and not as `Type::is_empty`, written in `empty.rs`,
    // which would close a cycle `empty.rs` -> `shared.rs` -> `empty.rs`.
    let rows: Vec<Row> = xq.tuples.lens[&2].union_rows()?;
    // No rows: `x` has no `link` of a pair (the union of no rows holds no pair), so its lists are
    // `stop` or none; the empty type is no step.
    if rows.is_empty() {
        return has_stop.then_some((StepShape::Stop, xq.structs));
    }
    Some((StepShape::Rows { has_stop, rows }, xq.structs))
}

/// How [`follow`] ended.
pub(super) enum PathEnd<K> {
    /// At a type `known` gave this for.
    Known(K),
    /// At a type met before on the path, at this index of it: the path from there is a cycle.
    Cycle(usize),
    /// At this type, which `step` gave no step for.
    Stuck(Type),
}

/// Follows the steps of a functional graph on types from `start`: at each type, first `known`
/// (a type already read), then whether the type is on the path already (a cycle), then `step`,
/// which gives what the caller keeps of the type and the next type. Gives the path, each type
/// stepped with what `step` gave, in order, and how it ended. The walks of the two chain readers
/// (`find_prefix_chains` and `check_chain_witness`) share it; before TEST-kernel-unreached-paths-12
/// each held a copy. Cost: per type on the path, one call of `known`, one of `step`, and one
/// lookup and one insert in a map keyed by type (expected O(1), [`ByType`]); each type is
/// stepped at most once, since a second visit ends the walk as a cycle.
pub(super) fn follow<K, S>(
    start: &Type,
    mut known: impl FnMut(&Type) -> Option<K>,
    mut step: impl FnMut(&Type) -> Option<(S, Type)>,
) -> (Vec<(Type, S)>, PathEnd<K>) {
    let mut path: Vec<(Type, S)> = Vec::new();
    let mut at: ByType<usize> = ByType::new();
    let mut cur = start.clone();
    loop {
        if let Some(k) = known(&cur) {
            return (path, PathEnd::Known(k));
        }
        if let Some(&i) = at.get(&cur) {
            return (path, PathEnd::Cycle(i));
        }
        let Some((s, next)) = step(&cur) else {
            return (path, PathEnd::Stuck(cur));
        };
        at.insert(cur.clone(), path.len());
        path.push((cur, s));
        cur = next;
    }
}

#[cfg(test)]
mod tests {
    use super::{ByType, PathEnd, StepShape, Tied, follow, step_shape};
    use crate::types::{Type, Universe};
    use crate::value::Value;
    use std::collections::BTreeMap;

    /// [`follow`] on the functional graph `k0 → k1 → … → k5 → k2` of atom types: from `k0` it
    /// ends in the cycle at index 2 with the path `k0 … k5`; with `k4` known it ends there with the
    /// path `k0 … k3`; and with `k3` given no step it is stuck at `k3` with the path `k0 … k2`.
    /// Each type is stepped at most once.
    #[test]
    fn follow_ends_at_a_known_type_a_cycle_or_a_type_with_no_step() {
        let k = |i: usize| Type::atom(&format!("k{i}"));
        let next: BTreeMap<Type, Type> = (0..6)
            .map(|i| (k(i), k(if i == 5 { 2 } else { i + 1 })))
            .collect();
        let names = |path: &[(Type, usize)]| path.iter().map(|(_, s)| *s).collect::<Vec<_>>();
        let mut steps = 0;
        let (path, end) = follow(
            &k(0),
            |_| None::<()>,
            |t| {
                steps += 1;
                let i = (0..6).position(|i| k(i) == *t).expect("a key");
                Some((i, next[t].clone()))
            },
        );
        assert_eq!(names(&path), [0, 1, 2, 3, 4, 5]);
        assert!(matches!(end, PathEnd::Cycle(2)));
        assert_eq!(steps, 6, "each type stepped once");
        let step = |t: &Type| {
            let i = (0..6).position(|i| k(i) == *t).expect("a key");
            (i != 3).then(|| (i, next[t].clone()))
        };
        let (path, end) = follow(&k(0), |t| (*t == k(4)).then_some(40), step);
        assert_eq!(names(&path), [0, 1, 2]);
        assert!(matches!(end, PathEnd::Stuck(ref t) if *t == k(3)));
        let (path, end) = follow(&k(0), |t| (*t == k(2)).then_some(20), step);
        assert_eq!(names(&path), [0, 1]);
        assert!(matches!(end, PathEnd::Known(20)));
        let (path, end) = follow(&k(2), |t| (*t == k(2)).then_some(20), step);
        assert!(path.is_empty());
        assert!(matches!(end, PathEnd::Known(20)));
    }

    /// [`step_shape`] with the link `cons` and the stop `nil`: a list step, the stop alone,
    /// two rows with and without records beside them, one row beside records (which
    /// `list_step` refuses), and the shapes it refuses: records with no pair beside the stop,
    /// another link or stop name, a second bare atom, an integer beside the atoms, and a payload
    /// of another length beside the pairs.
    #[test]
    fn step_shape_reads_the_steps_of_a_list() {
        let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer");
        let (nil, end) = (Type::atom("nil"), Type::atom("end"));
        let pair =
            |h: i64, tail: &Type| Type::atom_with("cons", &Type::tuple(vec![lit(h), tail.clone()]));
        let records = Type::atom_with("cons", &Type::universe(Universe::Struct));
        let shape = |x: &Type| step_shape(x, "cons", "nil");
        let one = &nil | &pair(1, &end);
        assert!(
            matches!(shape(&one), Some((StepShape::List(true, h, t), false)) if h == lit(1) && t == end)
        );
        assert!(matches!(shape(&nil), Some((StepShape::Stop, false))));
        // A payload with no pair has no part of length two, and is refused.
        assert!(shape(&(&nil | &records)).is_none());
        let two = &pair(1, &end) | &pair(2, &nil);
        let rows_of = |x: &Type| match shape(x) {
            Some((StepShape::Rows { has_stop, rows }, structs)) => {
                Some((has_stop, rows.len(), structs))
            }
            _ => None,
        };
        assert_eq!(rows_of(&two), Some((false, 2, false)));
        assert_eq!(rows_of(&(&(&two | &nil) | &records)), Some((true, 2, true)));
        assert_eq!(
            rows_of(&(&pair(1, &end) | &records)),
            Some((false, 1, true))
        );
        // Refused: another link, another stop, an integer, a payload of three items.
        assert!(step_shape(&one, "node", "nil").is_none());
        assert!(step_shape(&one, "cons", "end").is_none());
        assert!(shape(&(&two | &end)).is_none(), "a second bare atom");
        assert!(shape(&(&two | &lit(5))).is_none());
        let three = Type::atom_with("cons", &Type::tuple(vec![lit(1), lit(2), lit(3)]));
        assert!(shape(&(&two | &three)).is_none());
    }

    /// A [`ByType`] keys a type by the seeded hash of its digest, not by the digest a program
    /// can steer (row KERNEL-bytype-flooding): the key of each of 600 atoms is
    /// `text_hash(name_digest)`. On main before that row the key was the digest itself, and
    /// this test failed there. It cannot show that a program fails to flood the table, only
    /// that the key is out of the program's reach.
    #[test]
    fn the_key_is_the_seeded_hash_of_the_digest() {
        let m: ByType<()> = ByType::new();
        for i in 0..600 {
            let t = Type::atom(&format!("k{i}"));
            assert_eq!(
                m.digest(&t),
                crate::digest::text_hash(&t.name_digest()),
                "{t}"
            );
        }
    }

    /// Every operation of [`ByType`] agrees with a `BTreeMap` on 600 atoms. In the
    /// short-addresses build, whose digests keep 8 bits, many of the atoms share a digest, so
    /// the arms for a digest of two keys or more (`Tied::Many`) run; in the normal build the
    /// keys of one digest are one.
    #[test]
    fn a_map_by_type_agrees_with_an_ordered_map_also_where_digests_tie() {
        same_as_an_ordered_map(ByType::new());
    }

    /// As above, with the map keyed by no bit of the digest (every key ties with every other,
    /// so one `Tied::Many` holds them all) and by 4 bits (16 digests, each tied by about 37
    /// keys): the arms for tied keys run in the normal build too, among them a removal that
    /// leaves other keys of the digest and one that empties it.
    #[test]
    fn a_map_by_type_whose_digests_are_forced_to_tie_agrees_with_an_ordered_map() {
        assert_eq!(same_as_an_ordered_map(ByType::with_mask(0)), 1);
        assert_eq!(same_as_an_ordered_map(ByType::with_mask(0xF)), 16);
    }

    /// Runs the operations on `m` and a `BTreeMap` side by side, and gives the number of
    /// digests whose keys tie (`Tied::Many`) once all 600 keys are in.
    fn same_as_an_ordered_map(mut m: ByType<u32>) -> usize {
        let keys: Vec<Type> = (0..600).map(|i| Type::atom(&format!("k{i}"))).collect();
        let mut model: BTreeMap<Type, u32> = BTreeMap::new();
        let agree = |m: &ByType<u32>, model: &BTreeMap<Type, u32>| {
            for k in &keys {
                assert_eq!(m.get(k), model.get(k), "{k}");
                assert_eq!(m.contains_key(k), model.contains_key(k), "{k}");
            }
        };
        for (i, k) in keys.iter().enumerate() {
            let v = u32::try_from(i).expect("600 keys");
            assert_eq!(*m.entry(k.clone()).or_insert_with(|| v), v);
            model.insert(k.clone(), v);
        }
        let tied = m
            .map
            .values()
            .filter(|t| matches!(t, Tied::Many(_)))
            .count();
        // An entry of a key present keeps its value.
        for k in keys.iter().step_by(7) {
            assert_eq!(*m.entry(k.clone()).or_insert_with(|| 9999), model[k]);
        }
        agree(&m, &model);
        // A second `insert` of a key replaces its value and returns the old one.
        for k in keys.iter().step_by(3) {
            assert_eq!(m.insert(k.clone(), 7), model.insert(k.clone(), 7));
        }
        for k in keys.iter().step_by(5) {
            *m.get_mut(k).expect("a key") += 1;
            *model.get_mut(k).expect("a key") += 1;
            assert_eq!(m[k], model[k]);
        }
        agree(&m, &model);
        for k in keys.iter().step_by(2) {
            assert_eq!(m.remove(k), model.remove(k), "{k}");
            assert_eq!(m.remove(k), None, "{k} removed twice");
            assert_eq!(m.get_mut(k), None, "{k}");
        }
        agree(&m, &model);
        m.retain(|_, v| *v % 3 != 0);
        model.retain(|_, v| *v % 3 != 0);
        agree(&m, &model);
        // Removing every key left empties each digest's keys, the last removal of each digest
        // dropping its entry.
        for k in keys.iter().skip(1).step_by(2) {
            assert_eq!(m.remove(k), model.remove(k), "{k}");
        }
        agree(&m, &model);
        assert!(m.map.is_empty(), "a digest left with no key");
        for (i, k) in keys.iter().enumerate().take(40) {
            m.insert(k.clone(), u32::try_from(i).expect("40 keys"));
        }
        // A `retain` that keeps no key of a digest drops the digest.
        m.retain(|_, _| false);
        assert!(m.map.is_empty(), "a digest left with no key");
        for (i, k) in keys.iter().enumerate().take(40) {
            m.insert(k.clone(), u32::try_from(i).expect("40 keys"));
        }
        m.clear();
        assert!(keys.iter().all(|k| m.get(k).is_none()));
        tied
    }
}
