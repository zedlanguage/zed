//! Provenance (step L1.20, DESIGN.md sec:keypaths): the fact address of every value a run
//! computes, and the facts each one read.
//!
//! A fact is one node instance: a node of the term together with the instances of the
//! regions around it (sec:kernel, the objects of the dependency theorem). Its address is the pair
//! of a static [`NodeAddress`], code identity, and a dynamic keypath, data identity, and no two
//! facts of a run share one. A run records its facts when
//! [`Evaluator::with_provenance`](crate::Evaluator::with_provenance) asks for them; the
//! record is the run graph, each fact naming the facts it read.

use crate::btree::DiffItem as Change;
use crate::idset::{IdMap, IdSet};
/// The persistent vector of a fact address's node and keypath.
pub use imbl::Vector;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::term::{FixKind, Shared, Term};
use crate::value::{Family, Id};
use crate::value::{Items, Value};

/// The position of a node in a term: the child index taken at each node on the way down from
/// the root, in the order of [`child`]; the root's position is empty. A position is read from
/// the term's structure alone: a subterm that two places of a term share, as a term built by
/// cloning does, has a position at each, and no position depends on where the term sits in
/// memory or on the order a run reaches its nodes. Positions are ordered as the nodes are in
/// the term's preorder. A position shares the path above it with its parent's.
#[derive(Clone, Default)]
pub struct Position(Option<Arc<Link>>);

/// The last step of a position below the root.
struct Link {
    up: Position,
    child: u32,
    depth: u32,
    hash: u64,
}

impl Position {
    /// The root's position.
    pub fn root() -> Self {
        Position(None)
    }

    /// The position of child `i` of the node at `self`.
    pub fn child(&self, i: u32) -> Self {
        let hash = (self.hash_value().rotate_left(26) ^ (u64::from(i) + 1))
            .wrapping_mul(0x9E37_79B9_7F4A_7C15);
        let hash = crate::address::short64(hash);
        Position(Some(Arc::new(Link {
            up: self.clone(),
            child: i,
            depth: self.depth() + 1,
            hash,
        })))
    }

    /// The number of steps from the root.
    pub fn depth(&self) -> u32 {
        self.0.as_ref().map_or(0, |l| l.depth)
    }

    /// The child indices from the root down.
    pub fn path(&self) -> Vec<u32> {
        let mut out = Vec::with_capacity(self.depth() as usize);
        let mut at = self;
        while let Some(l) = &at.0 {
            out.push(l.child);
            at = &l.up;
        }
        out.reverse();
        out
    }

    fn hash_value(&self) -> u64 {
        self.0.as_ref().map_or(0, |l| l.hash)
    }

    fn up(&self) -> &Position {
        self.0.as_ref().map_or(self, |l| &l.up)
    }
}

impl Drop for Position {
    /// Frees a long path one link at a time, not by recursion.
    fn drop(&mut self) {
        let mut next = self.0.take();
        while let Some(link) = next {
            next = Arc::into_inner(link).and_then(|mut l| l.up.0.take());
        }
    }
}

impl PartialEq for Position {
    /// Compares index by index from the bottom; a link both positions share ends the walk.
    ///
    /// Why it is equality of the paths. A link's `depth` and `hash` are functions of the path
    /// alone ([`Position::child`] computes them from the parent's and the index only, never
    /// from an address), so equal paths have equal depths and hashes, and the first test
    /// rejects only unequal paths. A link is never changed after it is made, so two positions
    /// that reach one link (`Arc::ptr_eq`) have the same path from there up, and the walk may
    /// stop there; below it every index was compared. With equal depths both reach the root
    /// together. Test: `two_positions_built_apart_are_equal_when_their_paths_are` in
    /// tests/steps/l01_20_provenance/completeness.rs.
    fn eq(&self, other: &Self) -> bool {
        if self.depth() != other.depth() || self.hash_value() != other.hash_value() {
            return false;
        }
        let (mut a, mut b) = (self, other);
        while let (Some(x), Some(y)) = (&a.0, &b.0) {
            if Arc::ptr_eq(x, y) {
                return true;
            }
            if x.child != y.child {
                return false;
            }
            (a, b) = (&x.up, &y.up);
        }
        true
    }
}

impl Eq for Position {}

impl Ord for Position {
    /// The order of the paths, index by index from the root, a path before the paths below it.
    /// It walks up to the common ancestor, so it costs the distance to it: `O(depth)` for two
    /// positions far apart in a deep term. Many positions are kept by hash, not by this order.
    ///
    /// Why it is the term's preorder and agrees with `==`. Both are first cut to the smaller
    /// depth. If the cut paths differ, the first index where they differ from the root decides,
    /// which is the preorder of two nodes neither above the other; the walk sees the differences
    /// from the bottom up and keeps the last, so it keeps that one, and a shared link (one path
    /// above it, as in `eq`) has none above it. If the cut paths are equal, one position is the
    /// other or above it, and the depth puts the one above first, as preorder does. So `Equal`
    /// comes exactly when the cut paths and the depths are equal, that is when the paths are,
    /// which is `eq`; and the order is the lexicographic order of the paths, so it is total.
    /// Test: `positions_are_ordered_as_the_term_preorder` in
    /// tests/steps/l01_20_provenance/completeness.rs.
    fn cmp(&self, other: &Self) -> Ordering {
        let (mut a, mut b) = (self, other);
        while a.depth() > b.depth() {
            a = a.up();
        }
        while b.depth() > a.depth() {
            b = b.up();
        }
        // The walk goes up, so the last difference it meets is the one nearest the root.
        let mut first = Ordering::Equal;
        while let (Some(x), Some(y)) = (&a.0, &b.0) {
            if Arc::ptr_eq(x, y) {
                break;
            }
            if x.child != y.child {
                first = x.child.cmp(&y.child);
            }
            (a, b) = (&x.up, &y.up);
        }
        first.then(self.depth().cmp(&other.depth()))
    }
}

impl PartialOrd for Position {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for Position {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash_value());
    }
}

impl fmt::Display for Position {
    /// Each child index after a dot: `.` is the root, `.1.0` the first child of its second.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let path = self.path();
        if path.is_empty() {
            return f.write_str(".");
        }
        path.iter().try_for_each(|i| write!(f, ".{i}"))
    }
}

impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// The static half of a fact address: the position of each call site through which the run
/// entered the function holding the node, and then the node's own position. Only equality and
/// order mean anything; the positions change with the build (sec:keypaths, the opaque token).
// Complexity tradeoff (COMPLEXITY.md K9): the naive address copies the call stack and the
// keypath into each fact, O(depth) per fact, O(S·depth) for `S` facts. Used: persistent vectors
// (`imbl::Vector`) the run pushes and pops in amortized O(1) and every fact's address shares,
// O(1) more per fact. Tradeoff: a constant factor in time and memory per push over a plain
// vector, and comparing two addresses still reads them, O(depth).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct NodeAddress(pub Vector<Position>);

impl NodeAddress {
    /// The node's own position, the last.
    pub fn position(&self) -> &Position {
        self.0.last().expect("a node address names a node")
    }
}

/// A fact address: (static node address, dynamic keypath). The keypath holds the wave stamp,
/// then each enclosing region's coordinate: a family key, a generation number, an iterate
/// of a lattice `fix`, the key of a definedness `fix` entry, the step of a `fold`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct FactAddress {
    /// The code identity.
    pub node: NodeAddress,
    /// The data identity.
    pub keypath: Vector<Value>,
}

impl fmt::Display for FactAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let node: Vec<String> = self.node.0.iter().map(Position::to_string).collect();
        let keys: Vec<String> = self.keypath.iter().map(Value::to_string).collect();
        write!(f, "{}@({})", node.join("/"), keys.join(", "))
    }
}

/// One node instance of a run.
#[derive(Clone, Debug)]
pub struct Fact {
    /// Where it is.
    pub address: FactAddress,
    /// Its value; `None` for a function.
    pub value: Option<Value>,
    /// The facts it read, by index into [`Provenance::facts`], in the order it read them.
    pub inputs: Vec<usize>,
    /// Whether its value is a failure or holds one in a tuple, a keypath or a family's value,
    /// false for a function. [`Provenance::origins`] reads only the facts for which it is true.
    pub holds_failure: bool,
}

/// The run graph of one evaluation: its facts, each after the facts it read.
#[derive(Clone, Debug)]
pub struct Provenance {
    pub(crate) term: Term,
    pub(crate) facts: Vec<Fact>,
}

impl Provenance {
    /// Every fact, in the order the run completed them.
    pub fn facts(&self) -> &[Fact] {
        &self.facts
    }

    /// The fact the run's result came from, the last one completed.
    pub fn result(&self) -> usize {
        self.facts.len() - 1
    }

    /// The term at `node`'s position, found by walking down to it: `O(depth)`. The terms of
    /// many facts are read from [`Provenance::fact_terms`].
    pub fn term(&self, node: &NodeAddress) -> &Term {
        let at = node.position();
        at.path().into_iter().fold(&self.term, |t, i| {
            child(t, i).unwrap_or_else(|| panic!("no node at position {at}"))
        })
    }

    /// The term of each fact, by the fact's index: each position is found from its parent's
    /// once, so the work is the number of distinct positions, not the sum of their depths.
    pub fn fact_terms(&self) -> Vec<&Term> {
        let mut known = HashMap::new();
        self.facts
            .iter()
            .map(|f| self.resolve(f.address.node.position(), &mut known))
            .collect()
    }

    fn resolve<'a>(
        &'a self,
        p: &'a Position,
        known: &mut HashMap<&'a Position, &'a Term>,
    ) -> &'a Term {
        // The positions from `p` up to the first one known, nearest first.
        let mut todo = Vec::new();
        let mut at = p;
        let mut t = loop {
            if let Some(t) = known.get(at) {
                break *t;
            }
            match &at.0 {
                Some(l) => {
                    todo.push((at, l.child));
                    at = &l.up;
                }
                None => break &self.term,
            }
        };
        while let Some((q, i)) = todo.pop() {
            t = child(t, i).unwrap_or_else(|| panic!("no node at position {q}"));
            known.insert(q, t);
        }
        t
    }

    /// The addresses held by more than one fact, in fact order; a correct run has none
    /// (sec:keypaths, one writer per fact address). Node addresses are found by their cached
    /// hashes, not by [`Position`]'s order, whose comparison walks up to the common ancestor;
    /// the keypaths of one node are ordered, since a [`Value`] has no hash. The map finds the
    /// same repeats as the ordered set did: `Hash for Position` writes `hash_value` alone, and
    /// `Position::eq` is false where the `hash_value`s differ, so equal addresses hash alike
    /// (the `Hash` and `Eq` contract; `NodeAddress` derives both from its positions). Test:
    /// `the_check_for_repeated_addresses_on_a_chain_of_products_scales` (bench of step
    /// m0_09), which checks the time, not which addresses are found.
    pub fn repeated(&self) -> Vec<&FactAddress> {
        let mut seen: HashMap<&NodeAddress, BTreeSet<&Vector<Value>>> = HashMap::new();
        let mut out = Vec::new();
        for f in &self.facts {
            let a = &f.address;
            if !seen.entry(&a.node).or_default().insert(&a.keypath) {
                out.push(&f.address);
            }
        }
        out
    }

    /// The origins of the failure that fact `i` holds: for each distinct failure, the facts
    /// where it first appeared, so a merged `#errs` keeps the origins of all its operands
    /// rather than a winner (sec:failure). A failure first appears at a fact none of whose
    /// inputs holds it. Empty when the fact holds no failure.
    pub fn origins(&self, i: usize) -> BTreeSet<usize> {
        let Some(v @ Value::Atom(_)) = &self.facts[i].value else {
            return BTreeSet::new();
        };
        // The members, numbered from 0 for the sets of [`IdSet`]. Each is a failure atom: the
        // keys of an `#errs` set are the keys of atoms, which are atoms ([`Value::key`]).
        let members: Vec<&Value> = match v.errs() {
            Some(set) => set.keys().collect(),
            None => vec![v],
        };
        let mut held = Held {
            ids: members.iter().copied().zip(0..).collect(),
            names: members
                .iter()
                .filter_map(|m| match m {
                    Value::Atom(a) => Some(&*a.name),
                    _ => None,
                })
                .collect(),
            own: vec![None; members.len()],
            sets: HashMap::new(),
            tallies: HashMap::new(),
            seen: HashSet::new(),
            done: HashMap::new(),
            made: HashMap::new(),
            nodes: HashMap::new(),
            last: 0,
        };
        // The sets are found oldest fact first, over the facts `i` reaches by inputs whose
        // values hold a failure ([`Fact::holds_failure`]), each taken once: a family's set is
        // then found after that of the family it was made from, and from it, by what was added
        // ([`Held::base`]), so the two share their nodes and a set costs what its family's
        // tally changed. Newest first, a set found before the set it was made from is read
        // entry by entry and shares no nodes with it. A fact whose value holds no failure holds
        // no member, so the search of the pass below never goes through it, and it and the
        // facts it alone reaches are left out: a failure read next to a large value holding
        // none costs nothing for that value.
        // Complexity tradeoff: this reads the values of every fact `i` reaches through values
        // holding failures, where the pass below reads only the inputs of facts that hold a
        // member, so a failure read next to a large value holding other failures costs that
        // value's distinct parts, `O(m log m)` for `m` parts, at most the work of the run that
        // made them. In exchange, a chain of sets each one failure larger than the last costs
        // `O(1)` set work per reading for up to 4096 members, one more trie level for each
        // further factor of 64, where ordered maps of the members cost `O(log n)` per step
        // and copied nodes of up to 64 entries (COMPLEXITY.md K25). The ordering of `reached`
        // and of `traced` below, and the family diffs of [`Held::base`], keep an `O(log n)`
        // factor per fact. Reading only the facts that hold a member would need the members
        // each value holds before the values are read.
        let mut reached = vec![i];
        let mut taken = HashSet::from([i]);
        let mut next = 0;
        while let Some(&j) = reached.get(next) {
            next += 1;
            reached.extend(
                self.facts[j]
                    .inputs
                    .iter()
                    .filter(|k| self.facts[**k].holds_failure && taken.insert(**k)),
            );
        }
        reached.sort_unstable();
        for k in reached {
            if let Some(v) = &self.facts[k].value {
                held.of(v);
            }
        }
        // One backward pass over the facts, newest first: a fact's inputs completed before it,
        // so every fact that reaches `j` is taken before `j`. Why `k < j` for an input `k` of
        // `j`: the one writer of `Fact::inputs` (`eval.rs`, `fact`) takes the reads `t.reads`
        // of the subterms, each the index of a fact pushed before (a fact's own index, pushed
        // to `t.reads` just after the fact, or a variable's, `lookup_fact`, which passes on
        // such an index), and gives the new fact the index `len - 1` after its push, above all
        // of them. The `debug_assert!` below checks it in every debug test run.
        //
        // `traced[j]` holds the members whose search reaches fact `j`; the search of member `m`
        // goes on to each input that holds `m`, and `j` is an origin of `m` when no input holds
        // it. The sets are persistent ([`IdSet`]), and a set found from another shares its
        // nodes, so the common members of two sets are read from the leaves they hold in
        // different copies: along a chain of products, each holding one member more than the
        // last, a step costs `O(1)` for up to 4096 members.
        let mut traced: BTreeMap<usize, Found> = BTreeMap::from([(i, held.of(v).found)]);
        let mut out = BTreeSet::new();
        while let Some((j, at_j)) = traced.pop_last() {
            let mut found = Found::new();
            for &k in &self.facts[j].inputs {
                debug_assert!(k < j, "a fact reads only facts completed before it");
                // An input holding no failure holds no member: its set is empty.
                let input = &self.facts[k];
                let Some(v) = input.value.as_ref().filter(|_| input.holds_failure) else {
                    continue;
                };
                let common = Found::intersection(&at_j, &held.of(v).found);
                if !common.is_empty() {
                    // An input that holds every member of `j` leaves none to `j`. Exact: `common`
                    // is part of `at_j`, so `found` always is, and a part of the same size as
                    // `at_j` is `at_j`; when either is, the union is `at_j`.
                    found = match found.len() == at_j.len() || common.len() == at_j.len() {
                        true => at_j.clone(),
                        false => Found::union(&found, &common),
                    };
                    let t = traced.entry(k).or_default();
                    *t = Found::union(t, &common);
                }
            }
            if found.len() < at_j.len() {
                out.insert(j);
            }
        }
        out
    }
}

/// A set of failures, by their numbers in [`Held::ids`].
type Found = IdSet;

/// A set of failures with an id: two sets with one id hold the same failures, so the entries of
/// a family that hold one set are counted as one set, however many they are. The empty set's
/// id is 0. An id is drawn from [`Held::last`] in the order the walk finds sets, and is only
/// tested for equality: nothing in the result depends on its value.
#[derive(Clone, Default)]
struct Set {
    id: u64,
    found: Found,
}

/// How the set with some id is counted: as the failures of the set `base` (0 for none) and those
/// of `delta`, which holds none of the base's. A set made from another by adding failures is
/// counted from it, and a set from which another is made by removing failures is counted from
/// that one, so that a chain of sets each one failure larger than the last costs one failure
/// per set, whichever end of the chain is found first. Each base is smaller than the set on it,
/// so following bases ends.
#[derive(Clone)]
struct Node {
    base: u64,
    delta: Found,
}

/// A set counted in a [`Tally`]: its base and delta when it was counted, and the number of
/// counted sets whose base it is.
#[derive(Clone)]
struct Counted {
    base: u64,
    delta: Found,
    above: u32,
}

/// The failures a family's entries hold, counted so that the family's set can be found from
/// another family's by the difference of the two: entries added, removed or changed. A set an
/// entry holds is counted with its base, and the base's base, down to a set already counted,
/// and each counted set counts only its delta. So an entry that holds a set some other entry
/// holds costs `O(1)` (its maps are [`IdMap`]s keyed by the numbers of sets and failures),
/// and an entry whose set is made from a counted one costs the failures it adds. The first
/// set counted in an empty tally is counted whole, without its bases and without a count for
/// each failure: it holds each of its failures once, read from its own set. So a family of
/// one entry costs `O(1)` however large the entry's set, and only a later set none of whose
/// bases is counted costs its size.
///
/// Why `found` is the union of the sets the entries hold. Write `S(c)` for the failures of
/// the set `c`. Each operation keeps these, all true of the empty tally:
/// (a) every counted `c` has a base 0 or counted, and `S(c)` is `S(base)` and `delta`,
/// disjoint; the whole set has base 0 and delta `S(whole)`;
/// (b) `above` of `c` is the number of counted sets whose base is `c`;
/// (c) every key of `entries` is counted, and a counted set with `above` 0 is a key of
/// `entries`, so the counted sets are the entries' sets and their bases, no more;
/// (d) `sets[x]` is the number of counted sets but `whole` whose delta holds `x`;
/// (e) `found` is `delta(whole)` and the keys of `sets`.
/// By (a) the union of the counted deltas is the union of their `S(c)`, and by (c) and
/// `S(base) ⊆ S(c)` that is the union of the entries' sets, so (d) and (e) give the claim.
/// `enter` counts `s` whole only when nothing is counted (then by (c) no entry is either),
/// and otherwise counts it and its bases down to a counted one ([`Tally::count`]), taking
/// `(base, delta)` from [`Held::nodes`], which hold (a) for every set made (the makers, all
/// through `Held::fresh` but one: `made_by_difference`, `union`, `family` and a member's own
/// set in `read`; the one, `made_by_difference`'s removing branch, rewrites `was`'s node to
/// the new set and the failures removed, which is `S(was)` again). `count` ends: every base
/// there is a set strictly smaller than the one on it (`union`, `read` and the adding branch
/// put a smaller set under a larger, and the removing branch puts the new, smaller set under
/// `was`), so no chain of bases repeats. A tally keeps its own copy of each counted
/// `(base, delta)`, so a node rewritten later does not reach a set counted already; both
/// copies give the same `S`. `leave` and `uncount` drop a set once no entry holds it and
/// nothing is counted on it, then its base in the same state, keeping (b) and (c); `less` and
/// `drop_if_uncounted` keep (d) and (e), and dropping the whole set takes out of `found` each
/// of its failures no count in `sets` holds. `swap` by difference moves `old`'s place to
/// `new` only when `old` has `above` equal to 0 and one entry, `new` is not counted, and every
/// failure the difference removes is in `old`'s delta: so `S(base)` is untouched, an added
/// failure is outside `S(old)` and so outside `S(base)`, and (a) holds for `new` on `old`'s
/// base, with (b) and (c) as before; the whole set is replaced by `new` counted whole.
/// Otherwise `swap` is `enter` then `leave`. Tests:
/// `a_tally_keeps_the_failures_of_its_entries_when_the_set_counted_whole_changes` and
/// `holds_agrees_with_a_tree_read_over_values_and_families_made_from_others` (this file);
/// neither checks (a) to (e) directly, only `found` at the end.
#[derive(Clone, Default)]
struct Tally {
    /// The id of each distinct non-empty set the entries hold, with the number of entries that
    /// hold it.
    entries: IdMap<u32>,
    /// The sets counted: those the entries hold and their bases.
    counted: IdMap<Counted>,
    /// The id of the set counted whole, 0 for none. Its delta is all of its failures, and
    /// they are not in `sets`.
    whole: u64,
    /// Each failure, with the number of counted sets other than `whole` whose delta holds it.
    sets: IdMap<u32>,
    /// The failures: those of `whole` and the keys of `sets`.
    found: Found,
}

impl Tally {
    /// One more entry holds `s`.
    fn enter(&mut self, s: &Set, nodes: &HashMap<u64, Node>) {
        if s.found.is_empty() {
            return;
        }
        let n = self.entries.get(s.id).copied().unwrap_or(0);
        self.entries.insert(s.id, n + 1);
        if n > 0 || self.counted.contains_key(s.id) {
            return;
        }
        if self.counted.is_empty() {
            self.whole = s.id;
            self.found = s.found.clone();
            self.counted.insert(
                s.id,
                Counted {
                    base: 0,
                    delta: s.found.clone(),
                    above: 0,
                },
            );
            return;
        }
        // `found` takes the nodes it shares with `s`, so that later sets made from either are
        // compared by their difference.
        //
        // Complexity tradeoff (SCALE-near-prov-members): the union allocates a new node on each
        // level of every path where the two differ, a leaf of 64 words (512 bytes) and inner
        // nodes of 64 children, and reads all 64 slots of each, though `s` is most often one
        // failure (`Held::of` gives each member its own unit set). A tally made for a family
        // that adds `m` entries to its base's then allocated `m` leaves, 512 bytes each, where
        // the failures fill one leaf for each 4,096 (measured 25 KB a member at 4,096 members).
        // Used: a set `s` of at most 64 members (`WIDTH`) is inserted member by member, in
        // place where `found`'s nodes are its own (`Arc::make_mut`), O(h + 1) node steps
        // each for a trie of height `h`, so `64 (h + 1)` at most, which a union's read of 64
        // slots on each of the `h + 1` levels of one path matches; a shared path is copied
        // once and then changed in place. A larger `s` keeps the union, O(64 (h + 1)) per path
        // where they differ, and shares `s`'s nodes. Tradeoff: `found` no longer shares a small
        // `s`'s leaf, so a later difference against a set made from `s` reads that leaf, at
        // most 64 words, the read the union would have made here. Tests:
        // `a_tally_keeps_the_failures_of_its_entries_when_the_set_counted_whole_changes` and
        // `holds_agrees_with_a_tree_read_over_values_and_families_made_from_others` (this file)
        // check `found` on both paths; the cost is bench
        // `l01_20_provenance::bench::the_origins_of_a_failure_with_many_members_scale`.
        if s.found.len() <= crate::idset::WIDTH {
            for x in s.found.iter() {
                self.found.insert(x);
            }
        } else {
            self.found = Found::union(&self.found, &s.found);
        }
        self.count(s.id, nodes);
    }

    /// Counts the set `id`, not counted, and its bases down to one that is.
    fn count(&mut self, mut id: u64, nodes: &HashMap<u64, Node>) {
        let mut above = 0;
        loop {
            let node = &nodes[&id];
            for x in node.delta.iter() {
                let k = self.sets.get(u64::from(x)).copied().unwrap_or(0);
                self.sets.insert(u64::from(x), k + 1);
            }
            self.counted.insert(
                id,
                Counted {
                    base: node.base,
                    delta: node.delta.clone(),
                    above,
                },
            );
            if node.base == 0 {
                return;
            }
            if let Some(b) = self.counted.get_mut(node.base) {
                b.above += 1;
                return;
            }
            (id, above) = (node.base, 1);
        }
    }

    /// One entry fewer holds `s`.
    fn leave(&mut self, s: &Set) {
        if s.found.is_empty() {
            return;
        }
        let n = self.entries.get(s.id).copied().expect("an entry holds s");
        if n > 1 {
            self.entries.insert(s.id, n - 1);
            return;
        }
        self.entries.remove(s.id);
        if self.counted.get(s.id).expect("counted").above == 0 {
            self.uncount(s.id);
        }
    }

    /// Removes the set `id`, which no entry holds and no counted set has as its base, and each
    /// base left in the same state.
    fn uncount(&mut self, mut id: u64) {
        loop {
            let c = self.counted.remove(id).expect("a counted set");
            if id == self.whole {
                self.whole = 0;
                match self.counted.is_empty() {
                    true => self.found = Found::new(),
                    false => c.delta.iter().for_each(|x| self.drop_if_uncounted(x)),
                }
            } else {
                c.delta.iter().for_each(|x| self.less(x));
            }
            if c.base == 0 {
                return;
            }
            let b = self.counted.get_mut(c.base).expect("a counted base");
            b.above -= 1;
            if b.above > 0 || self.entries.contains_key(c.base) {
                return;
            }
            id = c.base;
        }
    }

    /// An entry that held `old` holds `new`. When `old` leaves the family and `new` enters
    /// it, `new` can be counted on `old`'s base with `old`'s delta changed by the difference
    /// of the two sets, when every failure it removes is in that delta: the counts change only
    /// at the failures the difference lists. That is done when the difference is shorter than
    /// the delta counting `new` from its own base would add, so a step costs the lesser.
    fn swap(&mut self, old: &Set, new: &Set, nodes: &HashMap<u64, Node>) {
        if old.id == new.id {
            return;
        }
        let leaves = !old.found.is_empty()
            && self.entries.get(old.id) == Some(&1)
            && self.counted.get(old.id).expect("counted").above == 0;
        let enters = !new.found.is_empty() && !self.counted.contains_key(new.id);
        if leaves && enters && self.swap_by_difference(old, new, nodes) {
            return;
        }
        // `new` first: a set made from `old` is then counted on it.
        self.enter(new, nodes);
        self.leave(old);
    }

    /// [`Tally::swap`] by the difference of `old` and `new`; false, with nothing changed, when
    /// it is not shorter than counting `new` or removes a failure of `old`'s base.
    fn swap_by_difference(&mut self, old: &Set, new: &Set, nodes: &HashMap<u64, Node>) -> bool {
        let node = &nodes[&new.id];
        let limit = match self.counted.contains_key(node.base) {
            true => node.delta.len(),
            false => new.found.len(),
        };
        let Some(diff) = Found::diff(&old.found, &new.found, limit) else {
            return false;
        };
        let was = self.counted.get(old.id).expect("counted");
        if diff
            .iter()
            .any(|&(x, added)| !added && !was.delta.contains(x))
        {
            return false;
        }
        let Counted {
            base, mut delta, ..
        } = self.counted.remove(old.id).expect("counted");
        self.entries.remove(old.id);
        self.entries.insert(new.id, 1);
        if old.id == self.whole {
            // The set counted whole becomes `new`, read from its own set, before the failures
            // `old` held and `new` does not are tested against it.
            self.whole = new.id;
            self.counted.insert(
                new.id,
                Counted {
                    base: 0,
                    delta: new.found.clone(),
                    above: 0,
                },
            );
            for (x, added) in diff {
                match added {
                    true => {
                        self.found.insert(x);
                    }
                    false => self.drop_if_uncounted(x),
                }
            }
            return true;
        }
        for (x, added) in diff {
            match added {
                true => {
                    delta.insert(x);
                    self.more(x);
                }
                false => {
                    delta.remove(x);
                    self.less(x);
                }
            }
        }
        self.counted.insert(
            new.id,
            Counted {
                base,
                delta,
                above: 0,
            },
        );
        true
    }

    /// Whether the set counted whole holds `x`.
    fn whole_holds(&self, x: u32) -> bool {
        self.whole != 0
            && self
                .counted
                .get(self.whole)
                .expect("counted")
                .delta
                .contains(x)
    }

    /// `x` leaves `found` unless a counted set's delta holds it.
    fn drop_if_uncounted(&mut self, x: u32) {
        if !self.sets.contains_key(u64::from(x)) && !self.whole_holds(x) {
            self.found.remove(x);
        }
    }

    /// One more counted set holds `x` in its delta.
    fn more(&mut self, x: u32) {
        let n = self.sets.get(u64::from(x)).copied().unwrap_or(0);
        self.sets.insert(u64::from(x), n + 1);
        if n == 0 {
            self.found.insert(x);
        }
    }

    /// One counted set fewer holds `x` in its delta.
    fn less(&mut self, x: u32) {
        match self.sets.get(u64::from(x)).copied().expect("a count") {
            1 => {
                self.sets.remove(u64::from(x));
                self.drop_if_uncounted(x);
            }
            n => {
                self.sets.insert(u64::from(x), n - 1);
            }
        }
    }
}

/// Whether values hold a failure, as [`Fact::holds_failure`] records it when a run makes a
/// fact: that a value is a failure, or holds one in a tuple, a keypath or a family's value, the
/// places [`Provenance::origins`] reads. Each non-empty sequence and family is read once, by its
/// id. A family made from another ([`Family::union`], `Family::extend`) holds each entry of the
/// other, or one holding all of its leaves, so it holds a failure when the other does, unread;
/// made from one holding none, it is read by the difference of the two, when that lists fewer
/// items than the family has entries. The value of a union the run evaluates is not read at all:
/// it holds a failure exactly when one of its operands does ([`Holds::set`]). A run with
/// provenance so reads each distinct part of its values once, `O(log n)` for each item of a
/// difference or entry: the parts it made, at the cost of making them, and the literals and port
/// data it read. An id names one content for good, since [`fresh_id`](crate::value::fresh_id)
/// never draws one twice.
#[derive(Default, Debug)]
pub(crate) struct Holds {
    /// Whether each non-empty sequence read holds a failure, by its id.
    items: HashMap<Id, bool, ById>,
    /// Each non-empty family read, by its id: `None` if it holds a failure, else the family,
    /// against which one made from it is compared.
    families: HashMap<Id, Option<Family>, ById>,
}

/// The hasher of the maps of [`Holds`]: `digest::Digest`, a few multiplications per id in
/// place of the default hasher's SipHash (Aumasson and Bernstein 2012,
/// doi:10.1007/978-3-642-34931-7_28; the full comment is in `digest.rs`, type `FixedState`).
type ById = std::hash::BuildHasherDefault<crate::digest::Digest>;

/// What [`Holds::of`] does next.
enum Visit<'v> {
    /// Reads a value, unless it was read since it was planned.
    Enter(&'v Value),
    /// Records a sequence or a family, the values it planned read.
    Record(Record<'v>),
}

/// A sequence or a family whose values not read before are planned above it. It holds a
/// failure if `found`, or if one of those values does: a sequence's among its items, a
/// family's on the stack of values to read from `from` on.
enum Record<'v> {
    Items {
        items: &'v Items,
        found: bool,
        unread: bool,
    },
    Family {
        family: &'v Family,
        found: bool,
        from: usize,
    },
}

impl Holds {
    /// Whether `v` holds a failure; the parts of `v` not read before are read now. A value whose
    /// parts were all read before needs no stack: a fact made of parts other facts hold.
    pub(crate) fn of(&mut self, v: &Value) -> bool {
        if let Some(holds) = self.read(v) {
            return holds;
        }
        let mut todo = Vec::new();
        // The values each family planned in `todo` has yet to read, a family's after those of
        // the families that hold it.
        let mut pending = Vec::new();
        let top = self.plan(v, &mut todo, &mut pending);
        while let Some(visit) = todo.pop() {
            match visit {
                Visit::Enter(x) if self.read(x).is_none() => {
                    let below = todo.len();
                    let record = self.plan(x, &mut todo, &mut pending);
                    todo.insert(below, Visit::Record(record));
                }
                Visit::Enter(_) => {}
                Visit::Record(record) => {
                    self.record(record, &mut pending);
                }
            }
        }
        self.record(top, &mut pending)
    }

    /// Records that `v`, a family, holds a failure exactly when `holds`, known without reading
    /// it.
    pub(crate) fn set(&mut self, v: &Value, holds: bool) {
        if let Value::Family(f) = v
            && !f.is_empty()
        {
            self.families.insert(f.id(), (!holds).then(|| f.clone()));
        }
    }

    /// Whether `v`, whose parts are all read, holds a failure.
    fn known(&self, v: &Value) -> bool {
        self.read(v).expect("its parts are read")
    }

    /// Whether `v` holds a failure, when that needs no part of it read: `None` for a non-empty
    /// sequence or family not read before.
    fn read(&self, v: &Value) -> Option<bool> {
        match v {
            Value::Atom(_) => Some(true),
            Value::Tuple(xs) | Value::Path(xs) if !xs.is_empty() => {
                self.items.get(&xs.id()).copied()
            }
            Value::Family(f) if !f.is_empty() => self.families.get(&f.id()).map(Option::is_none),
            _ => Some(false),
        }
    }

    /// Reads what of `v`, a sequence or family not read before, its parts read before decide,
    /// and plans the reading of the others on `todo`, a family's also on `pending`.
    fn plan<'v>(
        &self,
        v: &'v Value,
        todo: &mut Vec<Visit<'v>>,
        pending: &mut Vec<&'v Value>,
    ) -> Record<'v> {
        match v {
            Value::Tuple(xs) | Value::Path(xs) => {
                let (mut found, mut unread) = (false, false);
                for x in xs.iter() {
                    match self.read(x) {
                        Some(holds) => found |= holds,
                        None => {
                            unread = true;
                            todo.push(Visit::Enter(x));
                        }
                    }
                }
                Record::Items {
                    items: xs,
                    found,
                    unread,
                }
            }
            Value::Family(f) => {
                let from = pending.len();
                let mut found = false;
                // Reads the values until one holds a failure.
                let mut read = |xs: &mut dyn Iterator<Item = &'v Value>| {
                    for x in xs {
                        match self.read(x) {
                            Some(true) => {
                                found = true;
                                break;
                            }
                            Some(false) => {}
                            None => {
                                pending.push(x);
                                todo.push(Visit::Enter(x));
                            }
                        }
                    }
                };
                // Made from a family holding a failure, it holds that failure. Made from one
                // holding none, it holds one if a value of the difference does: a removed or
                // replaced value held none.
                // Id 0: made from no family.
                let base = (f.from() != 0)
                    .then(|| self.families.get(&f.from()))
                    .flatten();
                match base {
                    Some(None) => found = true,
                    Some(Some(base)) => match base.shallow_diff(f, f.len()) {
                        Some(diff) => read(&mut diff.into_iter().filter_map(|d| match d {
                            Change::Add(_, new) | Change::Update { new: (_, new), .. } => Some(new),
                            Change::Remove(..) => None,
                        })),
                        None => read(&mut f.0.built_map().values()),
                    },
                    None => read(&mut f.0.built_map().values()),
                }
                Record::Family {
                    family: f,
                    found,
                    from,
                }
            }
            _ => unreachable!("only a sequence or a family not read before is planned"),
        }
    }

    /// Records a sequence or a family whose values planned are all read; whether it holds a
    /// failure.
    fn record(&mut self, record: Record<'_>, pending: &mut Vec<&Value>) -> bool {
        match record {
            Record::Items {
                items,
                found,
                unread,
            } => {
                let holds = found || (unread && items.iter().any(|x| self.known(x)));
                self.items.insert(items.id(), holds);
                holds
            }
            Record::Family {
                family,
                found,
                from,
            } => {
                let mut rest = pending.drain(from..);
                let holds = found || rest.any(|x| self.known(x));
                drop(rest);
                let kept = (!holds).then(|| family.clone());
                self.families.insert(family.id(), kept);
                holds
            }
        }
    }
}

/// A non-empty sequence or a family, each named by its id ([`Items::id`], [`Family::id`]). An
/// id is only tested for equality, as a key of `sets` and `seen`, which are never iterated: no
/// order and nothing in the result depends on its value, and the origins come out in fact
/// order. The empty sequence is never entered or looked up.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Part {
    Items(Id),
    Family(Id),
}

/// A family whose set is found from the set of `base` and the difference of the two maps.
type FromBase<'a> = (&'a Family, Vec<Change<'a, 'a, Value, Value>>);

/// What [`Held::of`] does next.
enum Task<'a> {
    Enter(&'a Value),
    /// The set of the sequence, its values' sets found.
    Items(&'a Items),
    /// The set of the family, the sets it needs found.
    Family(&'a Family, Option<FromBase<'a>>),
}

/// The failures of the result that values hold: that a value is, has as a member of an
/// `#errs`, or holds in a tuple, a family or a payload. A value shares its tuples and families
/// with other values, so the set of each is found once, keyed by its id, and a walk
/// over a value is `O(distinct parts)`, not `O(paths)`.
struct Held<'a> {
    /// The number of each failure of the result, from 0 in their order.
    ids: HashMap<&'a Value, u32>,
    /// The names of the failures: an atom of another name is none of them, found without
    /// reading the rest of it.
    names: HashSet<&'a str>,
    /// The set a value equal to each failure holds, once found, by its number.
    own: Vec<Option<Set>>,
    sets: HashMap<Part, Set>,
    /// The tally of each family whose set is found, by the family's id.
    tallies: HashMap<Id, Tally>,
    /// The parts entered: a part is entered once, and its set is found before any part that
    /// holds it, since a value holds no part that holds it.
    ///
    /// Why each set is found before it is read ([`Held::read`] indexes `sets`). [`Held::of`]
    /// pops a task from a stack; entering a part pushes its own task and then the parts it
    /// needs above it, so those run first. A part whose task is still on the stack is one on
    /// the path from the root to the part being entered: everything above its task came from
    /// what it needs. So a part met again in `seen` is either done, with its set in `sets`, or
    /// on that path, and then the part being entered holds it and is held by it, a cycle.
    /// Values have none: every value is built from values made before it and never changed
    /// after it is shared (a family changed by [`Family::extend`] takes a new id, so the old id
    /// keeps naming the old map). A family read from a base reads only the entries the
    /// difference lists, which it needs, and the base's tally and set, found already
    /// (`done` and `made` hold only families whose task has run). Test:
    /// `holds_agrees_with_a_tree_read_over_values_and_families_made_from_others` (this file),
    /// which would panic at a missing set.
    seen: HashSet<Part>,
    /// The families whose sets are found, by id.
    done: HashMap<Id, &'a Family>,
    /// The families whose sets are found, by the id of the family each was made from.
    made: HashMap<Id, &'a Family>,
    /// How each set with a non-zero id is counted.
    nodes: HashMap<u64, Node>,
    /// The last id given to a set.
    last: u64,
}

impl<'a> Held<'a> {
    fn of(&mut self, v: &'a Value) -> Set {
        let mut todo = vec![Task::Enter(v)];
        while let Some(task) = todo.pop() {
            match task {
                Task::Enter(v) => self.enter(v, &mut todo),
                Task::Items(xs) => {
                    let mut s = Set::default();
                    for x in xs.iter() {
                        let r = self.read(x);
                        s = self.union(s, r);
                    }
                    self.sets.insert(Part::Items(xs.id()), s);
                }
                Task::Family(f, base) => {
                    let (tally, s) = self.family(f, base);
                    self.sets.insert(Part::Family(f.id()), s);
                    self.tallies.insert(f.id(), tally);
                    self.done.insert(f.id(), f);
                    if f.from() != 0 {
                        self.made.entry(f.from()).or_insert(f);
                    }
                }
            }
        }
        self.read(v)
    }

    /// A new set of the failures `found`, counted as those of the set `base` and `delta`.
    fn fresh(&mut self, base: u64, delta: Found, found: Found) -> Set {
        self.last += 1;
        self.nodes.insert(self.last, Node { base, delta });
        Set {
            id: self.last,
            found,
        }
    }
    /// Plans the sets of the parts of `v` not yet entered.
    fn enter(&mut self, v: &'a Value, todo: &mut Vec<Task<'a>>) {
        match v {
            Value::Atom(a) => self.enter_items(a.args(), todo),
            Value::Tuple(xs) | Value::Path(xs) => self.enter_items(xs, todo),
            Value::Family(f) if !f.is_empty() && self.seen.insert(Part::Family(f.id())) => {
                let base = self.base(f);
                let needs: Vec<&'a Value> = match &base {
                    None => f.0.built_map().values().collect(),
                    Some((_, diff)) => diff
                        .iter()
                        .flat_map(|d| match d {
                            Change::Add(_, e) | Change::Remove(_, e) => [Some(*e), None],
                            Change::Update { old, new } => [Some(old.1), Some(new.1)],
                        })
                        .flatten()
                        .collect(),
                };
                todo.push(Task::Family(f, base));
                todo.extend(needs.into_iter().map(Task::Enter));
            }
            _ => {}
        }
    }

    fn enter_items(&mut self, xs: &'a Items, todo: &mut Vec<Task<'a>>) {
        if !xs.is_empty() && self.seen.insert(Part::Items(xs.id())) {
            todo.push(Task::Items(xs));
            todo.extend(xs.iter().map(Task::Enter));
        }
    }

    /// The family `f`'s set is found from the set of the family it was made from, or of one
    /// made from it, when that set is found and their difference lists fewer items than `f` has
    /// entries; otherwise from each entry. The two share all but the nodes the change copied,
    /// which the difference skips, and it is abandoned as soon as it is as long as `f`, so
    /// either way the work is `O(|f|)` items. Only such a pair is compared: the difference of
    /// two families that share no nodes compares the values at each common key. Those values
    /// are compared shallowly ([`Family::shallow_diff`]): a family made from another by a
    /// change `d` levels down differs from it at each of those levels, and reading the two down
    /// to their difference at each level cost `O(d²)` per change.
    fn base(&self, f: &'a Family) -> Option<FromBase<'a>> {
        let base = match self.done.get(&f.from()) {
            Some(base) if f.from() != 0 => *base,
            _ => *self.made.get(&f.id())?,
        };
        Some((base, base.shallow_diff(f, f.len())?))
    }

    /// The tally and the set of `f`. Entries that hold one set are counted once, and a set
    /// made from a counted one costs what it adds, so the work is the number of entries read,
    /// `O(1)` each in the tally, and the deltas of the sets that enter or leave the tally.
    fn family(&mut self, f: &'a Family, base: Option<FromBase<'a>>) -> (Tally, Set) {
        let (tally, was) = match base {
            None => {
                let mut t = Tally::default();
                for e in f.0.built_map().values() {
                    let s = self.read(e);
                    t.enter(&s, &self.nodes);
                }
                (t, None)
            }
            Some((base, diff)) => {
                let mut t = self.tallies[&base.id()].clone();
                for d in diff {
                    match d {
                        Change::Add(_, e) => {
                            let s = self.read(e);
                            t.enter(&s, &self.nodes);
                        }
                        Change::Remove(_, e) => t.leave(&self.read(e)),
                        Change::Update { old, new } => {
                            let (old, new) = (self.read(old.1), self.read(new.1));
                            t.swap(&old, &new, &self.nodes);
                        }
                    }
                }
                (t, Some(self.sets[&Part::Family(base.id())].clone()))
            }
        };
        // The set keeps an id it equals: that of the one distinct set the entries hold, or the
        // base's when the failures are the base's map itself.
        let found = tally.found.clone();
        let set = match (tally.entries.len(), was) {
            _ if found.is_empty() => Set::default(),
            (1, _) => Set {
                id: tally.entries.first_key().expect("one set"),
                found,
            },
            (_, Some(was)) if was.found.ptr_eq(&found) => was,
            (_, Some(was)) => self.made_by_difference(was, found),
            (_, None) => self.fresh(0, found.clone(), found),
        };
        (tally, set)
    }

    /// A new set of the failures `found`, which a family's tally found from the set `was` of the
    /// family it was made from, or of one made from it. When `found` only adds failures to
    /// `was`, it is counted on `was`; when it only removes some, `was` is counted on it from
    /// then on, if that makes `was`'s delta smaller. The differences cost what the tally
    /// changed, since the two sets share the rest.
    fn made_by_difference(&mut self, was: Set, found: Found) -> Set {
        let adds = Found::difference(&found, &was.found);
        let removes = Found::difference(&was.found, &found);
        match (adds.is_empty(), removes.is_empty()) {
            (false, true) => self.fresh(was.id, adds, found),
            (true, false) => {
                let set = self.fresh(0, found.clone(), found);
                let node = self.nodes.get_mut(&was.id).expect("a node for each set");
                if removes.len() < node.delta.len() {
                    *node = Node {
                        base: set.id,
                        delta: removes,
                    };
                }
                set
            }
            (true, true) => was,
            (false, false) => self.fresh(0, found.clone(), found),
        }
    }

    /// The set of `a` and `b` together, with the id of the larger when the smaller adds
    /// nothing to it, and otherwise counted on the larger.
    fn union(&mut self, a: Set, b: Set) -> Set {
        let (large, small) = match a.found.len() >= b.found.len() {
            true => (a, b),
            false => (b, a),
        };
        if small.found.is_empty() || small.id == large.id {
            return large;
        }
        let added = Found::difference(&small.found, &large.found);
        if added.is_empty() {
            return large;
        }
        let found = Found::union(&large.found, &added);
        self.fresh(large.id, added, found)
    }

    /// The number of `v` when it is a failure of the result. Those are atoms; one of another
    /// name is found to be none of them by its name alone.
    fn member(&self, v: &Value) -> Option<u32> {
        match v {
            Value::Atom(a) if self.names.contains(&*a.name) => self.ids.get(v).copied(),
            _ => None,
        }
    }

    /// The set of `v`, the sets of its parts found. A value equal to a member holds that
    /// member too; its set is found once and kept, so that each read of it has one id.
    fn read(&mut self, v: &'a Value) -> Set {
        let items = |xs: &Items| match xs.is_empty() {
            true => Set::default(),
            false => self.sets[&Part::Items(xs.id())].clone(),
        };
        let s = match v {
            Value::Atom(a) => items(a.args()),
            Value::Tuple(xs) | Value::Path(xs) => items(xs),
            Value::Family(f) if !f.is_empty() => self.sets[&Part::Family(f.id())].clone(),
            _ => Set::default(),
        };
        let Some(m) = self.member(v) else {
            return s;
        };
        if let Some(own) = &self.own[m as usize] {
            return own.clone();
        }
        let own = match s.found.contains(m) {
            true => s,
            false => {
                let Set { id, mut found } = s;
                found.insert(m);
                self.fresh(id, Found::unit(m), found)
            }
        };
        self.own[m as usize] = Some(own.clone());
        own
    }
}

/// Child `i` of `t`, in the order that numbers the positions.
pub fn child<'a>(t: &'a Term, i: u32) -> Option<&'a Term> {
    let i = i as usize;
    fn pick<'a>(ts: &[&'a Shared], i: usize) -> Option<&'a Term> {
        ts.get(i).map(|&t| &**t)
    }
    let nth = |ts: &[&'a Shared]| pick(ts, i);
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => None,
        Term::Lam(_, body) => nth(&[body]),
        Term::App(f, args) => match i {
            0 => Some(&**f),
            _ => args.get(i - 1),
        },
        Term::Prim(_, args) => args.get(i),
        Term::Let(_, e, body) => nth(&[e, body]),
        Term::If(c, a, b) => nth(&[c, a, b]),
        Term::Match(s, arms) => match i {
            0 => Some(&**s),
            _ => arms.get(i - 1).map(|(_, b)| b),
        },
        Term::Fam { domain, body, .. } => nth(&[domain, body]),
        Term::Reindex { family, kf, vf, .. } => nth(&[family, kf, vf]),
        Term::Discard { family, sel } => nth(&[family, sel]),
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => match identity {
            Some(id) => nth(&[family, op, id]),
            None => nth(&[family, op]),
        },
        Term::Fix {
            init, step, kind, ..
        } => match kind {
            FixKind::Lattice { join } => nth(&[init, step, join]),
            FixKind::Definedness => nth(&[init, step]),
        },
        Term::Gen {
            init, step, guard, ..
        } => nth(&[init, step, guard]),
        Term::Push(_, v) => nth(&[v]),
    }
}

/// Child `i` of `t`, in the order of [`child`], to change in place. A child behind an `Arc`
/// that other terms share is first copied (`Shared::make_mut`, which gives it a new id): that one
/// node, with the children it holds inline; its `Arc` children stay shared. `None` when `t` has no
/// child `i`.
pub fn child_mut(t: &mut Term, i: u32) -> Option<&mut Term> {
    let i = i as usize;
    fn pick<const N: usize>(ts: [&mut Shared; N], i: usize) -> Option<&mut Term> {
        ts.into_iter().nth(i).map(Shared::make_mut)
    }
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => None,
        Term::Lam(_, body) => pick([body], i),
        Term::App(f, args) => match i {
            0 => Some(Shared::make_mut(f)),
            _ => args.get_mut(i - 1),
        },
        Term::Prim(_, args) => args.get_mut(i),
        Term::Let(_, e, body) => pick([e, body], i),
        Term::If(c, a, b) => pick([c, a, b], i),
        Term::Match(s, arms) => match i {
            0 => Some(Shared::make_mut(s)),
            _ => arms.get_mut(i - 1).map(|(_, b)| b),
        },
        Term::Fam { domain, body, .. } => pick([domain, body], i),
        Term::Reindex { family, kf, vf, .. } => pick([family, kf, vf], i),
        Term::Discard { family, sel } => pick([family, sel], i),
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => match identity {
            Some(id) => pick([family, op, id], i),
            None => pick([family, op], i),
        },
        Term::Fix {
            init, step, kind, ..
        } => match kind {
            FixKind::Lattice { join } => pick([init, step, join], i),
            FixKind::Definedness => pick([init, step], i),
        },
        Term::Gen {
            init, step, guard, ..
        } => pick([init, step, guard], i),
        Term::Push(_, v) => pick([v], i),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The sets of `ids`, each with its base and the failures it adds, in an order that puts
    /// each base first; and the failures of each.
    struct Sets {
        nodes: HashMap<u64, Node>,
        sets: HashMap<u64, Set>,
    }

    impl Sets {
        fn new(ids: &[(u64, u64, &[u32])]) -> Self {
            let mut out = Sets {
                nodes: HashMap::new(),
                sets: HashMap::new(),
            };
            for &(id, base, adds) in ids {
                let delta: Found = adds.iter().copied().collect();
                let mut found = match base {
                    0 => Found::new(),
                    b => out.sets[&b].found.clone(),
                };
                delta.iter().for_each(|x| {
                    found.insert(x);
                });
                out.nodes.insert(id, Node { base, delta });
                out.sets.insert(id, Set { id, found });
            }
            out
        }
    }

    /// The failures of the sets the entries hold.
    fn expected(held: &[&Set]) -> Vec<u32> {
        let all: BTreeSet<u32> = held.iter().flat_map(|s| s.found.iter()).collect();
        all.into_iter().collect()
    }

    fn found(t: &Tally) -> Vec<u32> {
        t.found.iter().collect()
    }

    #[test]
    fn a_tally_keeps_the_failures_of_its_entries_when_the_set_counted_whole_changes() {
        // 1 = {0, 1, 2, 3}; 2 = {0, 1, 2, 4}, a set close to 1; 3 = {3, 5}; 4 = {6, 7}, far
        // from 1; 5 = 3 and {6}.
        let s = Sets::new(&[
            (1, 0, &[0, 1, 2, 3]),
            (2, 0, &[0, 1, 2, 4]),
            (3, 0, &[3, 5]),
            (4, 0, &[6, 7]),
            (5, 3, &[6]),
        ]);
        let set = |id: u64| &s.sets[&id];
        let check = |t: &Tally, held: &[&Set], step: &str| {
            assert_eq!(found(t), expected(held), "{step}");
        };

        // The set counted whole leaves: the tally is empty, then another set is counted.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        check(&t, &[set(1)], "enter 1");
        t.leave(set(1));
        check(&t, &[], "leave 1");
        t.enter(set(3), &s.nodes);
        check(&t, &[set(3)], "enter 3 after");

        // The set counted whole leaves while another holds one of its failures.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        t.enter(set(3), &s.nodes);
        t.leave(set(1));
        check(&t, &[set(3)], "leave 1 under 3");

        // The set counted whole is replaced by one close to it, by their difference, while
        // another set holds the failure the difference removes.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        t.enter(set(3), &s.nodes);
        t.swap(set(1), set(2), &s.nodes);
        check(&t, &[set(2), set(3)], "swap 1 for 2 under 3");
        t.leave(set(3));
        check(&t, &[set(2)], "leave 3");

        // The same, with no other set.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        t.swap(set(1), set(2), &s.nodes);
        check(&t, &[set(2)], "swap 1 for 2");
        t.swap(set(2), set(4), &s.nodes);
        check(&t, &[set(4)], "swap 2 for 4");

        // The set counted whole is replaced by one far from it, and the sets counted on a base
        // come and go around it.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        t.enter(set(5), &s.nodes);
        check(&t, &[set(1), set(5)], "enter 1 and 5");
        t.swap(set(1), set(4), &s.nodes);
        check(&t, &[set(4), set(5)], "swap 1 for 4 under 5");
        t.swap(set(5), set(3), &s.nodes);
        check(&t, &[set(4), set(3)], "swap 5 for 3");
        t.leave(set(4));
        check(&t, &[set(3)], "leave 4");
        t.leave(set(3));
        check(&t, &[], "leave 3 last");
    }

    /// `Tally::enter` inserts a set of at most `WIDTH` failures member by member and takes the
    /// union of a larger one (SCALE-near-prov-members): both give the failures of the sets
    /// entered, across leaves and as the trie grows a level (past 4,096 and 262,144), and
    /// after the tally is cloned (a tally made from a base's), with the clone's set unchanged.
    #[test]
    fn a_tally_enters_small_sets_in_place_and_large_ones_by_union() {
        let wide: Vec<u32> = (0..65).collect();
        let edge: Vec<u32> = (0..64).map(|i| 4_000 + 3 * i).collect();
        let spread: Vec<u32> = (0..500).map(|i| 37 * i).collect();
        let s = Sets::new(&[
            (1, 0, wide.as_slice()),
            (2, 0, edge.as_slice()),
            (3, 0, &[4_095, 4_096]),
            (4, 0, spread.as_slice()),
            (5, 0, &[262_144]),
            (6, 0, &[7]),
        ]);
        let set = |id: u64| &s.sets[&id];
        let mut t = Tally::default();
        let mut held = vec![];
        for id in [6, 1, 2, 3, 4, 5] {
            t.enter(set(id), &s.nodes);
            held.push(set(id));
            assert_eq!(found(&t), expected(&held), "enter {id}");
        }
        // A clone entering more leaves the tally it was cloned from as it was.
        let before = found(&t);
        let mut u = t.clone();
        let middle: Vec<u32> = (100..300).collect();
        let more = Sets::new(&[(7, 0, &[1, 5_000, 300_000]), (8, 0, middle.as_slice())]);
        u.enter(&more.sets[&7], &more.nodes);
        u.enter(&more.sets[&8], &more.nodes);
        assert_eq!(found(&t), before, "the clone's sets");
        held.push(&more.sets[&7]);
        held.push(&more.sets[&8]);
        assert_eq!(
            found(&u),
            expected(&held),
            "the clone after entering 7 and 8"
        );
        for id in [1, 4, 6] {
            t.leave(set(id));
        }
        assert_eq!(
            found(&t),
            expected(&[set(2), set(3), set(5)]),
            "after leaving 1, 4 and 6"
        );
    }

    /// The bytes `Tally::enter` allocates for a one-member set, the case `Held::of` makes for
    /// each member (SCALE-near-prov-members): a tally of `m` failures is cloned, as a family's
    /// tally is made from its base's, and `m` sets of one new failure each are entered, at
    /// `m` = 512, 4,096 (a leaf of the trie full) and 32,768 (8 times as many). Each insert
    /// copies a path the clone shares once and then changes it in place, and the maps of the
    /// entries and the counted sets grow by doubling, so the bytes a member stay flat: 270, 254
    /// and 252 (Colab hm5, 2026-11-25). With the union put back for these sets (`if false` for
    /// the test of `WIDTH`) they were 709, 1,230 and 1,228, a new leaf of 512 bytes or more on
    /// each union. The bound, 512 bytes a member, lies between the two. The ratio bench
    /// `l01_20_provenance::bench::the_origins_of_a_failure_with_many_members_scale` cannot see
    /// that variant: its cost has the same order, and it measured 12.14 times the work there
    /// under the proved bound of 20 (PROV-negative-control-weak).
    #[test]
    fn a_tally_enters_one_member_sets_in_place_at_flat_bytes_a_member() {
        for m in [512u32, 4096, 32_768] {
            let base: Vec<u32> = (0..m).collect();
            let s = Sets::new(&[(1, 0, base.as_slice())]);
            let mut t = Tally::default();
            t.enter(&s.sets[&1], &s.nodes);
            let mut u = t.clone();
            let ones: Vec<(u64, Sets)> = (0..m)
                .map(|i| {
                    let id = 2 + u64::from(i);
                    (id, Sets::new(&[(id, 0, &[2 * m + i][..])]))
                })
                .collect();
            let before = zed_alloc_count::allocated();
            for (id, one) in &ones {
                u.enter(&one.sets[id], &one.nodes);
            }
            let bytes = zed_alloc_count::allocated() - before;
            assert!(
                bytes < 512 * u64::from(m),
                "{m} one-member sets entered: {bytes} bytes, {} a member, not under 512",
                bytes / u64::from(m)
            );
            assert_eq!(found(&t), base, "the tally cloned from, {m}");
            let mut all = base.clone();
            all.extend(2 * m..3 * m);
            assert_eq!(found(&u), all, "the clone after {m} entries");
        }
    }

    /// Whether `v` is a failure or holds one where [`Holds`] reads, read as a tree.
    fn holds_by_tree(v: &Value) -> bool {
        match v {
            Value::Atom(_) => true,
            Value::Tuple(xs) | Value::Path(xs) => xs.iter().any(holds_by_tree),
            Value::Family(f) => f.iter().any(|(_, x)| holds_by_tree(x)),
            _ => false,
        }
    }

    #[test]
    fn holds_agrees_with_a_tree_read_over_values_and_families_made_from_others() {
        let late = || Value::atom("late");
        let tuple = Value::tuple;
        let fam = |es: Vec<(i64, Value)>| Family::of(es);
        // A family of 64 entries holding one failure, one holding none, and families made from
        // each by adding entries.
        let base = fam((0..64)
            .map(|k| (k, if k == 5 { late() } else { Value::Int(k) }))
            .collect());
        let clean = fam((0..64).map(|k| (k, Value::Int(k))).collect());
        let from = |f: &Family, entries: Vec<(i64, Value)>| {
            let mut f = f.clone();
            f.extend(entries.into_iter().map(|(k, x)| (Value::Int(k), x)));
            Value::Family(f)
        };
        let made = |entries| from(&base, entries);
        let made_clean = |entries| from(&clean, entries);
        let nested = fam(vec![(0, Value::Family(base.clone()))]);
        let clean_nested = fam(vec![(0, Value::Family(clean.clone()))]);
        let values = vec![
            Value::Int(3),
            late(),
            Value::atom_with("missing", vec![Value::Int(1)]),
            tuple(vec![]),
            tuple(vec![Value::Int(1), Value::Int(2)]),
            tuple(vec![Value::Int(1), tuple(vec![late()])]),
            Value::path(vec![Value::Int(0), late()]),
            Value::Family(fam(vec![])),
            Value::Family(fam(vec![(0, Value::Int(1))])),
            // A failure only in a key is not read.
            Value::Family(Family::set([late()])),
            Value::Family(base.clone()),
            Value::Family(clean.clone()),
            // Made from a family holding a failure, unread; made from one holding none, read by
            // the entries added: none holding a failure, one deep in a tuple, one family.
            made(vec![(64, Value::Int(64))]),
            made_clean(vec![(64, Value::Int(64)), (65, Value::Int(65))]),
            made_clean(vec![(64, Value::Int(64)), (65, tuple(vec![late()]))]),
            made_clean(vec![(70, Value::Family(base.clone()))]),
            // A family made from no other, and families made from it and from one holding no
            // failure by a union: beside an entry, and merging a failure into a family entry.
            Value::Family(nested.clone()),
            Value::Family(
                Family::union(&nested, &fam(vec![(1, Value::Int(0))])).expect("disjoint"),
            ),
            Value::Family(clean_nested.clone()),
            Value::Family(Family::union(&clean_nested, &fam(vec![(1, late())])).expect("disjoint")),
            Value::Family(
                Family::union(
                    &clean_nested,
                    &fam(vec![(0, Value::Family(fam(vec![(100, late())])))]),
                )
                .expect("disjoint"),
            ),
            // Made from a family holding none by adding more entries than it has.
            made_clean((64..256).map(|k| (k, Value::Int(k))).collect()),
            // The same tuple twice in one value is read once.
            {
                let t = tuple(vec![late()]);
                tuple(vec![t.clone(), t])
            },
        ];
        let mut holds = Holds::default();
        for v in &values {
            assert_eq!(holds.of(v), holds_by_tree(v), "{v}");
            // A value read again is known without reading it.
            assert_eq!(holds.of(v), holds_by_tree(v), "{v} again");
        }
    }
}
