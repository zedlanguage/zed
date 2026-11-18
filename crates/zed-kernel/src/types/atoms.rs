//! The atoms part of a type, [`Atoms`], in a module of its own so that its fields are private
//! to it: only [`Atoms::set`] writes the map of names, and only this module's constructors set
//! `cofinite`. So the invariant `set` keeps, that a map lists no name whose part is the default
//! of its kind (`AtomPart::none()` when finite, `AtomPart::all()` when cofinite), holds of every
//! `Atoms` the compiler accepts. The emptiness check's atom walks rely on it (`empty.rs`, the
//! `(false, true)` arms of `cycle_meet`, `find_prefix_chains`, `check_chain_witness` and
//! `list_rows`).

use super::*;

/// Per atom name, its part; a name not listed has every payload when `cofinite`, else none.
/// The map is persistent, and `sum` is the wrapping sum of its entries' hashes. `payloads` is
/// the set of listed names whose payload lists something, kept by [`Atoms::set`] in O(log n),
/// so that a sweep finds the one payload name, or that there is none, without reading the
/// others: the sweeps ask it of every type they are given, and reading every name there made a
/// chain of `n` failure atoms cost `n^2 log n`. `bare_names` counts the listed names that hold
/// their bare atom, kept by [`Atoms::set`] in O(1), so that whether a type holds a bare atom is
/// read without reading the names.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(super) struct Atoms {
    name_sum: u64,
    cofinite: bool,
    names: OrdMap<Arc<str>, AtomPart>,
    sum: u64,
    payloads: OrdSet<Arc<str>>,
    bare_names: usize,
}

impl Atoms {
    /// Every atom: cofinite, no name listed.
    pub(super) fn all() -> Atoms {
        Atoms {
            cofinite: true,
            ..Atoms::default()
        }
    }

    /// The listed names and their parts. No part listed is the default of the map's kind.
    pub(super) fn names(&self) -> &OrdMap<Arc<str>, AtomPart> {
        &self.names
    }

    /// Whether a name not listed has every payload (else none).
    pub(super) fn cofinite(&self) -> bool {
        self.cofinite
    }

    /// The wrapping sum of the entries' hashes.
    pub(super) fn sum(&self) -> u64 {
        self.sum
    }

    /// [`Atoms::sum`] by reference, for the debug writer, which queues references.
    pub(super) fn sum_ref(&self) -> &u64 {
        &self.sum
    }

    /// The wrapping sum of the entries' hashes by name digests.
    pub(super) fn name_sum(&self) -> u64 {
        self.name_sum
    }

    /// The listed names whose payload lists something.
    pub(super) fn payloads(&self) -> &OrdSet<Arc<str>> {
        &self.payloads
    }

    /// How many listed names hold their bare atom.
    pub(super) fn bare_names(&self) -> usize {
        self.bare_names
    }

    /// The map of names, taken out to be freed in a loop when the node holding it is dropped
    /// (`Drop for Node`). The empty map left behind lists no part, so it keeps the invariant;
    /// the sums are left stale, which nothing reads of a node being dropped.
    pub(super) fn take_names(&mut self) -> OrdMap<Arc<str>, AtomPart> {
        std::mem::take(&mut self.names)
    }

    /// Whether it is the part of no atom, `Atoms::default()`, read with nothing built.
    pub(super) fn is_default(&self) -> bool {
        !self.cofinite && self.names.is_empty() && self.sum == 0
    }

    pub(super) fn get(&self, name: &str) -> AtomPart {
        match self.names.get(name) {
            Some(p) => p.clone(),
            None if self.cofinite => AtomPart::all(),
            None => AtomPart::none(),
        }
    }

    fn entries(name: &str, p: &AtomPart) -> (u64, u64) {
        let head = mix(bytes(name.as_bytes()), u64::from(p.bare));
        (
            mix(head, p.payload.digest()),
            mix(head, p.payload.name_digest()),
        )
    }

    /// Gives `name` the part `p`, unlisting it when `p` is what an unlisted name has.
    pub(super) fn set(&mut self, name: &Arc<str>, p: AtomPart) {
        if let Some(old) = self.names.remove(name) {
            let (primary, named) = Atoms::entries(name, &old);
            self.sum = self.sum.wrapping_sub(primary);
            self.name_sum = self.name_sum.wrapping_sub(named);
            self.payloads.remove(name);
            self.bare_names -= usize::from(old.bare);
        }
        let default = if self.cofinite {
            AtomPart::all()
        } else {
            AtomPart::none()
        };
        if p != default {
            let (primary, named) = Atoms::entries(name, &p);
            self.sum = self.sum.wrapping_add(primary);
            self.name_sum = self.name_sum.wrapping_add(named);
            if !p.payload.lists_nothing() {
                self.payloads.insert(name.clone());
            }
            self.bare_names += usize::from(p.bare);
            self.names.insert(name.clone(), p);
        }
    }

    /// The parts combined by `op`. A name the smaller map does not list has every payload or
    /// none, and a part combined with all or none is itself, all or none: so the result is the
    /// larger map, or nothing, changed at the smaller map's names. When it is the larger map,
    /// only the names where the two differ change, since a part combined with itself is itself;
    /// those are found by walking the smaller map, `O(s log l)` steps for its `s` names and the
    /// larger's `l`, or by a diff of the two maps, which skips the nodes they share, so that
    /// two sets grown from one another, as a chain of merged failures grows the set of its
    /// members beside its loose atoms (ERRS-precise), differ in `O(d log l)` for their `d`
    /// differing names. The two walks advance in turn and the first to finish is used:
    // Complexity tradeoff: twice the cheaper walk, so `O(min(s, d + log l) log l)`, against
    // `O(s log l)` alone, which is quadratic for a chain of `n` such unions.
    pub(super) fn zip(&self, other: &Atoms, op: Op) -> Atoms {
        let cofinite = match op {
            Op::Or => self.cofinite || other.cofinite,
            Op::And => self.cofinite && other.cofinite,
        };
        let (large, small) = if self.names.len() >= other.names.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut out = match (op, small.cofinite) {
            (Op::Or, false) | (Op::And, true) => large.clone(),
            _ => {
                let mut out = Atoms {
                    cofinite,
                    ..Atoms::default()
                };
                for (n, p) in &small.names {
                    out.set(n, large.get(n).zip(p, op));
                }
                return out;
            }
        };
        // `cofinite` is `large.cofinite` here (`Or` with `small` finite, `And` with it
        // cofinite), so the clone's names stay valid for it.
        out.cofinite = cofinite;
        let mut walk = small.names.iter();
        let mut diff = large.names.diff(&small.names);
        let mut differ = Vec::new();
        loop {
            if walk.next().is_none() {
                for (n, p) in &small.names {
                    out.set(n, large.get(n).zip(p, op));
                }
                return out;
            }
            match diff.next() {
                None => break,
                Some(DiffItem::Add(n, p) | DiffItem::Update { new: (n, p), .. }) => {
                    differ.push((n, p));
                }
                Some(DiffItem::Remove(..)) => {}
            }
        }
        for (n, p) in differ {
            out.set(n, large.get(n).zip(p, op));
        }
        out
    }

    /// Joins `other` into `self` in place, both listing every name they hold (neither
    /// cofinite): `O(s log l)` for `other`'s `s` names and the result's `l`. A node `self`
    /// shares with another map is copied the first time it changes, and then changed in place.
    pub(super) fn join(&mut self, other: &Atoms) {
        debug_assert!(!self.cofinite && !other.cofinite);
        for (n, p) in &other.names {
            let joined = self.get(n).zip(p, Op::Or);
            self.set(n, joined);
        }
    }

    pub(super) fn not(&self) -> Atoms {
        let mut out = Atoms {
            cofinite: !self.cofinite,
            ..Atoms::default()
        };
        for (n, p) in &self.names {
            out.set(n, p.not());
        }
        out
    }

    /// The parts of `self` outside `other`: `self.zip(&other.not(), Op::And)`, each name's part
    /// the same, without building `other.not()`.
    ///
    /// Proof that it is that map. Write `s(n)` and `o(n)` for the parts `get` gives; the result
    /// at `n` is `s(n) & !o(n)` (`at`), and `set` leaves a name unlisted exactly when its part
    /// is the default of the result's kind, so it is enough that every name whose part may
    /// differ from that default is set. An unlisted name has the part none in a finite map and
    /// all in a cofinite one, and `!all` is none.
    /// - `self` cofinite, `other` finite: the result is cofinite (default all). At a name
    ///   `other` does not list, `!o(n)` is all and the part is `s(n)`, which `self.clone()`
    ///   already holds; so only `other`'s names are set.
    /// - Both cofinite: the result is finite (default none). At a name `other` does not list,
    ///   `!o(n)` is none; so only `other`'s names can be other than none.
    /// - `self` finite, `other` cofinite: finite. A name either map leaves unlisted gives none
    ///   (`s(n)` none, or `!o(n)` none), so only names both list matter, and setting the
    ///   names of either map, the smaller, covers them.
    /// - Both finite: finite. A name `self` leaves unlisted gives none, so setting `self`'s
    ///   names is enough; or, from `self.clone()`, a name `other` leaves unlisted keeps
    ///   `s(n) & all = s(n)`, so setting `other`'s names is enough.
    ///
    /// Each case reads the names of one map and gets `s(n)` and `o(n)` in O(log) each.
    // Complexity tradeoff: `O(min(s, o) log max(s, o))` for the `s` and `o` names listed, where
    // `self & !other` complemented each of `other`'s names first, `O(o log o)` whatever `self`
    // is. So `#a <: (#r1 | ... | #rk)`, asked of each arm of an `else if` chain of `n` links
    // returning `n` atoms, cost `O(k)` at depth `k`, the chain `Θ(n²)`: 25.2 times the
    // instructions for 8 times the links, 8.0 now (row BENCH-if-chain-other-paths; test
    // `l08_02_remaps::bench::an_else_if_chain_returning_n_different_types_is_checked_in_n_log_n_time`;
    // COMPLEXITY.md K119).
    pub(super) fn minus(&self, other: &Atoms) -> Atoms {
        let at = |n: &Arc<str>| self.get(n).zip(&other.get(n).not(), Op::And);
        let fresh = |cofinite: bool, names: &OrdMap<Arc<str>, AtomPart>| {
            let mut out = Atoms {
                cofinite,
                ..Atoms::default()
            };
            for n in names.keys() {
                out.set(n, at(n));
            }
            out
        };
        let changed = |names: &OrdMap<Arc<str>, AtomPart>| {
            let mut out = self.clone();
            for n in names.keys() {
                out.set(n, at(n));
            }
            out
        };
        let smaller_self = self.names.len() <= other.names.len();
        match (self.cofinite, other.cofinite) {
            (true, false) => changed(&other.names),
            (true, true) => fresh(false, &other.names),
            (false, true) if smaller_self => fresh(false, &self.names),
            (false, true) => fresh(false, &other.names),
            (false, false) if smaller_self => fresh(false, &self.names),
            (false, false) => changed(&other.names),
        }
    }
}
