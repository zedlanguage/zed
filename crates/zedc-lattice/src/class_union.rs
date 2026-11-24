//! A set of integers as a union of [`Classed`] sets, at most one for each class: the values of
//! a strided part, or of several cases of different classes, held without listing them.
//!
//! Moved here from zedc-presburger `presburger/exact/classes.rs` (row
//! LIMITS-classed-listing-per-set), so that zedc-preimage's reduced product can hold the
//! integers of cases joined with different classes ([`ClassUnion::join`]) as the cover of
//! zedc-presburger holds the values of its parts (row PERF-exact-strided-unlisted); the
//! operations that charge the cover's work meter (`minus`, `met`) stay there, as the trait
//! `Charged` of that module.
//!
//! Complexity tradeoff: naive version, the values as one [`IntervalSet`], each value of a
//! strided set a range of its own: O(v) pieces for v values, made, joined and read (the cover
//! of `w` in `0 <= a, b <= R && (a <= 2 || b >= 8) && a + b == w && w == 2·t` read 8.4M units
//! at R = 10^5, `l01_38_presburger::strided`, 2026-11-23). Used: one [`Classed`] for each
//! class, O(p) pieces for p ranges, whatever the number of values.

use std::collections::HashMap;

use crate::classed::Classed;
use crate::interval::{End, IntervalSet};
use crate::lattice::Congruence;

/// The union of `sets`.
#[derive(Clone, Debug)]
pub struct ClassUnion {
    /// Each set nonempty and in the one form of [`Classed::new`], no two with the same class,
    /// in an order made by the joins alone (so that nothing hangs on a hash order).
    sets: Vec<Classed>,
    /// The place in `sets` of each class.
    at: HashMap<Congruence, usize>,
}

impl ClassUnion {
    /// No value.
    pub fn empty() -> ClassUnion {
        ClassUnion {
            sets: Vec::new(),
            at: HashMap::new(),
        }
    }

    /// The values of `set`, read in the one form of [`Classed`] (which finds its class).
    pub fn plain(set: IntervalSet) -> ClassUnion {
        ClassUnion::of(Classed::plain(set))
    }

    /// The values of `set`.
    pub fn of(set: Classed) -> ClassUnion {
        let mut u = ClassUnion::empty();
        u.add(set);
        u
    }

    /// The sets, each with its class.
    pub fn sets(&self) -> &[Classed] {
        &self.sets
    }

    /// `set` joined. Two sets of one class are made one ([`Classed::new`] of the union of their
    /// ranges); that may give the set a class another set has, which is then joined in turn.
    /// Each join leaves one set fewer, so this ends. Each class found in O(1) expected (`at`),
    /// each join O(p log p) for p ranges.
    pub fn add(&mut self, mut set: Classed) {
        while !set.is_empty() {
            let Some(&i) = self.at.get(&set.class) else {
                self.at.insert(set.class.clone(), self.sets.len());
                self.sets.push(set);
                return;
            };
            let old = self.sets.swap_remove(i);
            self.at.remove(&old.class);
            if let Some(moved) = self.sets.get(i) {
                self.at.insert(moved.class.clone(), i);
            }
            set = Classed::new(old.ranges.join(&set.ranges), set.class);
        }
    }

    /// Whether the union has no value: every set is nonempty.
    pub fn is_empty(&self) -> bool {
        self.sets.is_empty()
    }

    /// Whether `v` is a value of the union. O(k log p) for k sets of p ranges.
    pub fn contains(&self, v: &End) -> bool {
        self.sets.iter().any(|s| s.contains_end(v))
    }

    /// The number of ranges of all the sets.
    pub fn len(&self) -> usize {
        self.sets.iter().map(|s| s.ranges.len()).sum()
    }

    /// The union of the two.
    pub fn join(&self, other: &ClassUnion) -> ClassUnion {
        let mut u = self.clone();
        for s in &other.sets {
            u.add(s.clone());
        }
        u
    }

    /// The values within `range`: each set's ranges met with it, in its own class.
    pub fn meet_range(&self, range: &IntervalSet) -> ClassUnion {
        let mut u = ClassUnion::empty();
        for s in &self.sets {
            u.add(s.meet_ranges(range));
        }
        u
    }

    /// The values in `set`, exact: `(A1 ∪ … ∪ Ak) ∩ B = (A1 ∩ B) ∪ … ∪ (Ak ∩ B)`, each meet
    /// [`Classed::meet`] (the ranges met, the classes met by the Chinese remainder theorem).
    /// O(k p log p) for k sets of p ranges.
    pub fn meet_classed(&self, set: &Classed) -> ClassUnion {
        let mut u = ClassUnion::empty();
        for s in &self.sets {
            u.add(s.meet(set));
        }
        u
    }

    /// The range with the least lower end of any set, with that set's class: the piece a
    /// question of the cover asks next.
    pub fn first(&self) -> Option<((End, End), Congruence)> {
        (self.sets.iter())
            .filter_map(|s| s.ranges.first().map(|p| (p.clone(), s.class.clone())))
            .min_by(|a, b| a.0.0.cmp(&b.0.0))
    }

    /// The ranges of the sets as one set, every member of each set's class within them dropped
    /// or not: the hull of each range, `self` within it.
    pub fn ranges(&self) -> IntervalSet {
        IntervalSet::from_pieces(
            (self.sets.iter())
                .flat_map(|s| s.ranges.pieces().cloned())
                .collect(),
        )
    }

    /// The union in the one form of [`Classed`] ([`Classed::join_all`], which lists only the
    /// sets of a class other than the union's).
    pub fn into_classed(self) -> Classed {
        Classed::join_all(self.sets)
    }
}

/// Equal where the two hold the same sets, each with its class, in any order: the form of a
/// union is made by its joins ([`ClassUnion::add`]), so two unions of the same values may
/// differ in form (the even and the odd values of `0..=4` as two sets, or `0..=4` as one), and
/// are then unequal; a reader that compares values reads [`ClassUnion::into_classed`].
/// O(k) expected for k sets, each class found by `at`.
impl PartialEq for ClassUnion {
    fn eq(&self, other: &ClassUnion) -> bool {
        self.sets.len() == other.sets.len()
            && (self.sets.iter())
                .all(|s| (other.at.get(&s.class)).is_some_and(|&i| other.sets[i] == *s))
    }
}

#[cfg(test)]
mod tests;
