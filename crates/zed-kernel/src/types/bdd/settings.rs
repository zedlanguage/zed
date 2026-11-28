//! Persistent ordered sets of settings, each an atom and a value, for [`Part::forced`]: treaps
//! whose union and intersection split one set at the other's root and join the halves, so `k`
//! settings meet `n` in `O(k log(n/k + 1))` expected time (Blelloch, Ferizovic and Sun, "Just
//! join for parallel ordered sets", SPAA 2016, doi:10.1145/2935764.2935768, Theorem 4 of the
//! full version, for independent
//! priorities, cited in full and quoted in module `zed_collections::treap`; for the 8-wise
//! independent priorities here, module [`zed_collections::priority`]), where adding the smaller
//! set's settings to the larger one at a time takes `O(k log n)`. The treap, its union and its
//! intersection are those of module [`zed_collections::treap`] (DRY-persistent-trees-2026-11-26),
//! over an item [`Setting`] with no summary.
//!
//! Unlike the sets of module `set`, these nodes are kept in no table: [`Part::forced`] never asks
//! whether two sets are one node, so a table lookup per node made would be cost with no use
//! (PERF-forced-balanced-union measured the shared treaps at 3.4 times these instructions).
//! A node's priority is a function of its setting drawn at random once per run ([`priority`]),
//! ties broken by the setting's order, so in a run one set has one shape whatever order its
//! settings came in. The shape is never shown: a set is read only in order.
//!
//! [`Part::forced`]: super::Part::forced

use super::set::Atom;
use zed_collections::priority::Priorities;
use zed_collections::treap;

/// A setting: an atom and its value.
pub(super) type Key<A> = (A, bool);

/// A setting as an item of a treap: its key is itself, and its priority [`priority`].
#[derive(Clone)]
pub(super) struct Setting<A>(Key<A>);

impl<A: Atom> treap::Item for Setting<A> {
    type Key = Key<A>;
    type Sum = ();
    fn key(&self) -> &Key<A> {
        &self.0
    }
    fn priority(&self) -> u64 {
        priority(&self.0)
    }
    fn sum(&self, _: Option<&()>, _: Option<&()>) {}
}

/// A set: its root, or `None` when empty.
pub(super) type Tree<A> = treap::Tree<Setting<A>>;

/// The priorities of the settings of each value, drawn once per run (module
/// [`zed_collections::priority`]): two uses, so that the two settings of one atom are two
/// independent points.
static PRIORITIES: [Priorities; 2] = [
    Priorities::eight_wise(1).fixed_in_unit_tests(cfg!(test)),
    Priorities::eight_wise(2).fixed_in_unit_tests(cfg!(test)),
];

/// The priority of `key`: the run's random polynomial of degree 7 at its atom's digest, one for
/// each value. Distinct digests take 8-wise independent uniform priorities, which bounds every
/// node's expected depth by `O(log n)` for every set of settings (Seidel and Aragon 1996,
/// doi:10.1007/BF01940876, Theorem 3.3 and section 6, cited in full and quoted in module
/// [`zed_collections::priority`]) and the work of [`union`] and [`meet`] by the finger bound
/// (module [`zed_collections::priority`] has both proofs), where the fixed hash this replaces had
/// no bound for chosen settings (COMPLEXITY.md K123). Atoms of one digest share a point: they tie
/// whatever the draw, and each such atom adds at most one to a depth. The treap reads it once per
/// setting, when [`from_keys`] makes its node; a node made again keeps its priority.
fn priority<A: Atom>(key: &Key<A>) -> u64 {
    PRIORITIES[usize::from(key.1)].of(key.0.digest())
}

/// The number of settings.
pub(super) fn len<A: Atom>(t: &Tree<A>) -> usize {
    treap::len(t)
}

/// Whether `key` is in the set.
#[cfg(test)]
fn contains<A: Atom>(t: &Tree<A>, key: &Key<A>) -> bool {
    treap::get(t, key).is_some()
}

/// The settings in order, by one walk with a stack of its own, `O(k)`.
pub(super) fn keys<A: Atom>(t: &Tree<A>) -> Vec<Key<A>> {
    let mut out = Vec::with_capacity(len(t));
    out.extend(treap::iter(t).map(|s| s.0.clone()));
    out
}

/// The set of `keys`, in any order, each once: sorted, then made by
/// `zed_collections::treap::from_sorted`, `O(k log k)` for the sort and `O(k)` after it (a
/// Cartesian tree by priority made with one stack, `zed_collections::cartesian::build`, shared
/// with `bdd::set::from_sorted`; its module comment cites and quotes its sources and proves it).
/// Tested by `settings::tests`, against ordered sets.
pub(super) fn from_keys<A: Atom>(mut keys: Vec<Key<A>>) -> Tree<A> {
    zed_collections::sorted::sort_dedup(&mut keys);
    treap::from_sorted(keys.into_iter().map(Setting))
}

/// The settings in either set (`zed_collections::treap::union`).
pub(super) fn union<A: Atom>(x: &Tree<A>, y: &Tree<A>) -> Tree<A> {
    treap::union(x, y)
}

/// The settings in both sets (`zed_collections::treap::meet`).
pub(super) fn meet<A: Atom>(x: &Tree<A>, y: &Tree<A>) -> Tree<A> {
    treap::meet(x, y)
}

/// The settings in any of `sets`: the settings of all but the largest gathered, sorted and
/// made into one set ([`from_keys`]), which is then joined to the largest ([`union`]). For `R`
/// settings outside the largest set of `L`, `O(R log R + R log(L/R + 1))`.
// Complexity tradeoff (COMPLEXITY.md K32, PERF-forced-balanced-union): the naive union of `m`
// sets folds [`union`] over them, two at a time; on a balanced tree of `m` single settings
// each level of the tree joins sets of equal size, `O(m)` node copies per level and
// `O(m log m)` copies in all, where this sorts the `m` settings once (`O(m log m)` comparisons,
// no node made) and makes `m` nodes. A set much larger than the rest is never copied: it is
// the one the rest are joined to, so a chain adding one setting at a time to a shared set
// stays `O(log L)` per link.
pub(super) fn union_all<A: Atom>(sets: &[&Tree<A>]) -> Tree<A> {
    let big = (0..sets.len()).max_by_key(|&i| (len(sets[i]), std::cmp::Reverse(i)))?;
    let mut rest = Vec::new();
    for (i, t) in sets.iter().enumerate() {
        if i != big {
            rest.extend(keys(t));
        }
    }
    if rest.is_empty() {
        return sets[big].clone();
    }
    union(sets[big], &from_keys(rest))
}

/// The settings in every one of `sets` (at least one): the smallest met with each of the rest
/// in turn, stopping when nothing is left. Each step keeps at most the settings of the one
/// before, so for `m` sets the smallest of which is `s`, `O(m s log(L/s + 1))`, `L` the largest.
pub(super) fn meet_all<A: Atom>(sets: &[&Tree<A>]) -> Tree<A> {
    let small = (0..sets.len())
        .min_by_key(|&i| len(sets[i]))
        .expect("a meet of one set at least");
    let mut out = sets[small].clone();
    for (i, t) in sets.iter().enumerate() {
        if out.is_none() {
            break;
        }
        if i != small {
            out = meet(&out, t);
        }
    }
    out
}

#[cfg(test)]
mod tests;
