//! The integers the forward transfer of the preimage finds for a term (item S22-fwd-holes): a
//! set shared by every value that holds it, whose pieces are listed only when a reader asks
//! for them, and whose bounds are known at once.
//!
//! A chain of `k` levels over an input with `H` holes, each level `if g { t } else { max(t,
//! c) }`, made a new set of `O(H)` pieces at each level, `O(k H)`, though the test above the
//! chain read only its bounds. Here a join and a monotone operator (`+`, `-`, negation, `min`,
//! `max`) keep their operands and the bounds of their result, in `O(1)`; the first reader that
//! asks for the pieces lists them with the same functions as before ([`IntervalSet::join`],
//! [`revision::forward`]), each set once, so every answer is the same. Every other operator
//! lists its operands and its result at once.

use std::cell::{Cell, OnceCell, RefCell};
use std::fmt;
use std::rc::Rc;

use zed_kernel::value::fresh_id;
use zedc_lattice::interval::{End, IntervalSet};
use zedc_lattice::revision::{self, Op};

/// A set of integers, shared: a clone is `O(1)`.
// Complexity tradeoff: naive version, an `IntervalSet` made at each level, O(k·H) pieces for k
// levels over a domain of H holes (2,362,372 pieces at k = 64). Used: a shared node whose
// join and monotone operators keep their operands and bounds in O(1), its pieces listed only
// when a reader asks, each set once on an explicit stack (130 pieces at k = 64). Tradeoffs:
// an `Rc` node per operation, kept alive until the run ends; a reader of the pieces pays the
// listing then; `preimage::SharedInts` keys operator entries by the operands' ids
// ([`Ints::id`]), which no other set has, even after the operands are dropped. Tests
// `l01_25_preimage_catalog::s22::forward_sets_of_a_chain_share_the_holes_scale` and
// `shared_ints::tests::made_sets_list_as_the_listed_operations_give`; COMPLEXITY.md row
// S22-fwd-holes.
#[derive(Clone)]
pub(crate) struct Ints(Rc<Node>);

struct Node {
    /// The least and greatest member; `None` for the empty set.
    bounds: Option<(End, End)>,
    /// The pieces, once listed.
    listed: OnceCell<Rc<IntervalSet>>,
    /// How the set is made from others, until it is listed.
    made: RefCell<Option<Made>>,
    /// The id ([`Ints::id`]), 0 until it is first asked for.
    id: Cell<u64>,
}

enum Made {
    /// The union of two sets.
    Join(Ints, Ints),
    /// [`revision::forward`] of a monotone operator ([`monotone`]) on two sets.
    Forward(Op, Ints, Ints),
}

impl Made {
    fn operands(self) -> [Ints; 2] {
        match self {
            Made::Join(a, b) | Made::Forward(_, a, b) => [a, b],
        }
    }
}

/// Whether the bounds of `revision::forward(op, x, y)` are those of the operator on the hulls
/// of `x` and `y`: an operator monotone in each operand, whose extremes over the pieces are
/// taken at the outer ends of the outer pieces, which are the ends of the hulls. Merging pieces
/// to cap their number (`map2`) keeps the outer ends.
fn monotone(op: &Op) -> bool {
    matches!(op, Op::Add | Op::Sub | Op::Neg | Op::Min | Op::Max)
}

impl Ints {
    /// The empty set, one for the thread, so that a value of no integer allocates nothing.
    pub(crate) fn empty() -> Ints {
        thread_local! {
            static EMPTY: Ints = Ints::of(IntervalSet::empty());
        }
        EMPTY.with(Ints::clone)
    }

    /// The set `s`, listed, whose pieces count as made ([`count_forward`]).
    pub(crate) fn of(s: IntervalSet) -> Ints {
        count_forward(s.len());
        Ints::shared(Rc::new(s))
    }

    /// The set `s`, listed, without a copy.
    pub(crate) fn shared(s: Rc<IntervalSet>) -> Ints {
        let bounds = s.bounds().map(|(lo, hi)| (lo.clone(), hi.clone()));
        Ints(Rc::new(Node {
            bounds,
            listed: OnceCell::from(s),
            made: RefCell::new(None),
            id: Cell::new(0),
        }))
    }

    fn made(bounds: Option<(End, End)>, made: Made) -> Ints {
        if bounds.is_none() {
            return Ints::empty();
        }
        Ints(Rc::new(Node {
            bounds,
            listed: OnceCell::new(),
            made: RefCell::new(Some(made)),
            id: Cell::new(0),
        }))
    }

    /// The least and greatest member, or `None` for the empty set. `O(1)`.
    pub(crate) fn bounds(&self) -> Option<(&End, &End)> {
        self.0.bounds.as_ref().map(|(lo, hi)| (lo, hi))
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.bounds.is_none()
    }

    /// The smallest interval that holds the set. `O(1)`.
    fn hull(&self) -> IntervalSet {
        match self.bounds() {
            Some((lo, hi)) => IntervalSet::range(lo.clone(), hi.clone()),
            None => IntervalSet::empty(),
        }
    }

    /// What tells this set apart from every other set made: two values with one id are one
    /// set, and a set dropped does not pass its id on, as it may pass on its address, so a
    /// memo keyed by ids need not hold the sets. Drawn by `fresh_id` the first time it is
    /// asked for.
    // Complexity tradeoff: naive version, the node's address, O(1), valid as a key only while
    // the entry holding it keeps the node alive (each `SharedInts` operator entry held its two
    // operands for that alone). Used: an id drawn once per node asked, O(1) (a thread-local
    // counter), never reused. Tradeoffs: 8 bytes per node; the operator entries no longer hold
    // their operands. Test `shared_ints::tests::a_dropped_set_passes_on_no_id`; COMPLEXITY.md
    // F153.
    pub(crate) fn id(&self) -> u64 {
        if self.0.id.get() == 0 {
            self.0.id.set(fresh_id());
        }
        self.0.id.get()
    }

    /// The union, `O(1)`.
    pub(crate) fn join(&self, other: &Ints) -> Ints {
        if other.is_empty() || Rc::ptr_eq(&self.0, &other.0) {
            return self.clone();
        }
        let (Some((alo, ahi)), Some((blo, bhi))) = (self.bounds(), other.bounds()) else {
            return other.clone();
        };
        let bounds = (alo.min(blo).clone(), ahi.max(bhi).clone());
        Ints::made(Some(bounds), Made::Join(self.clone(), other.clone()))
    }

    /// [`revision::forward`]: `O(1)` for a monotone operator, whose result is listed when it
    /// is read, and otherwise the pieces of both operands and of the result, listed now.
    pub(crate) fn forward(op: &Op, x: &Ints, y: &Ints) -> Ints {
        if monotone(op) {
            let bounds = revision::forward(op, &x.hull(), &y.hull())
                .bounds()
                .map(|(lo, hi)| (lo.clone(), hi.clone()));
            return Ints::made(bounds, Made::Forward(op.clone(), x.clone(), y.clone()));
        }
        Ints::of(revision::forward(op, x.set(), y.set()))
    }

    /// The pieces, listed now if they were not: each set not yet listed that this one is made
    /// from is listed once, in the order of their making.
    pub(crate) fn set(&self) -> &IntervalSet {
        if self.0.listed.get().is_none() {
            self.list();
        }
        self.0.listed.get().expect("listed")
    }

    /// Lists the sets this one is made from, then this one, on an explicit stack, since a
    /// chain of `k` levels makes sets `k` deep; a set listed already is not read again, so the
    /// work is that of the sets listed and the links between them.
    fn list(&self) {
        let mut todo = vec![(self.clone(), false)];
        while let Some((s, ready)) = todo.pop() {
            if s.0.listed.get().is_some() {
                continue;
            }
            if !ready {
                todo.push((s.clone(), true));
                let made = s.0.made.borrow();
                let (Made::Join(a, b) | Made::Forward(_, a, b)) =
                    made.as_ref().expect("a set not listed is made from others");
                for o in [a, b] {
                    if o.0.listed.get().is_none() {
                        todo.push((o.clone(), false));
                    }
                }
                continue;
            }
            let made = s.0.made.borrow_mut().take();
            let listed = match made.as_ref().expect("a set not listed is made from others") {
                Made::Join(a, b) => a.listed().join(b.listed()),
                Made::Forward(op, a, b) => revision::forward(op, a.listed(), b.listed()),
            };
            debug_assert_eq!(
                listed.bounds(),
                s.bounds(),
                "the bounds known before listing are the bounds of the pieces"
            );
            count_forward(listed.len());
            s.0.listed.set(Rc::new(listed)).expect("listed once");
        }
    }

    fn listed(&self) -> &IntervalSet {
        self.0.listed.get().expect("operands are listed first")
    }
}

impl Drop for Node {
    /// Drops a chain of sets made from one another without recursion: each set that is not
    /// shared gives its operands to the loop before it is dropped.
    fn drop(&mut self) {
        let mut todo: Vec<Ints> = (self.made.get_mut().take())
            .into_iter()
            .flat_map(Made::operands)
            .collect();
        while let Some(s) = todo.pop() {
            if let Ok(mut node) = Rc::try_unwrap(s.0) {
                todo.extend(
                    node.made
                        .get_mut()
                        .take()
                        .into_iter()
                        .flat_map(Made::operands),
                );
            }
        }
    }
}

impl PartialEq for Ints {
    /// The same members.
    fn eq(&self, other: &Ints) -> bool {
        Rc::ptr_eq(&self.0, &other.0) || self.set() == other.set()
    }
}

impl fmt::Display for Ints {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.set().fmt(f)
    }
}

thread_local! {
    /// The pieces of the integer sets that the forward transfer made on this thread since
    /// [`forward_pieces`] last read it.
    static FORWARD_PIECES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// The pieces of the integer sets that the forward transfer made on this thread since the
/// last call, which resets the count: each set listed, once, and none for a domain it shares
/// (COMPLEXITY.md S22-fwd-holes).
pub fn forward_pieces() -> u64 {
    FORWARD_PIECES.replace(0)
}

/// Counts `n` pieces made for [`forward_pieces`].
pub(crate) fn count_forward(n: usize) {
    FORWARD_PIECES.with(|c| c.set(c.get() + n as u64));
}

#[cfg(test)]
mod tests {
    use super::*;
    use zedc_lattice::interval::{End, Num};

    /// A small generator, so that the cases are the same on every run.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }

        /// A set of up to 6 pieces in `[-40, 40]`, each outer end infinite one time in five.
        fn set(&mut self) -> IntervalSet {
            let mut ps = Vec::new();
            for _ in 0..self.below(7) {
                let a = self.below(81) as i64 - 40;
                let b = a + self.below(6) as i64;
                ps.push((End::of(a), End::of(b)));
            }
            if self.below(5) == 0 {
                ps.push((End::NegInf, End::of(self.below(81) as i64 - 60)));
            }
            if self.below(5) == 0 {
                ps.push((End::of(self.below(81) as i64 - 20), End::PosInf));
            }
            IntervalSet::from_pieces(ps)
        }
    }

    const OPS: [Op; 9] = [
        Op::Add,
        Op::Sub,
        Op::Neg,
        Op::Min,
        Op::Max,
        Op::Mul,
        Op::Div,
        Op::Mod,
        Op::Abs,
    ];

    /// Every set made by joins and operators, listed when read, is the set the operations on
    /// listed sets give, and its bounds known before listing are the bounds of its pieces:
    /// chains of 6 random steps from random sets, 4,000 of them.
    #[test]
    fn made_sets_list_as_the_listed_operations_give() {
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        for _ in 0..4000 {
            let mut lazy = vec![];
            let mut flat = vec![];
            for _ in 0..3 {
                let s = rng.set();
                lazy.push(Ints::of(s.clone()));
                flat.push(s);
            }
            for _ in 0..6 {
                let (i, j) = (rng.below(lazy.len() as u64), rng.below(lazy.len() as u64));
                let (i, j) = (i as usize, j as usize);
                let k = rng.below(OPS.len() as u64 + 1) as usize;
                let (l, f) = match OPS.get(k) {
                    Some(op) => (
                        Ints::forward(op, &lazy[i], &lazy[j]),
                        revision::forward(op, &flat[i], &flat[j]),
                    ),
                    None => (lazy[i].join(&lazy[j]), flat[i].join(&flat[j])),
                };
                assert_eq!(
                    l.bounds(),
                    f.bounds(),
                    "bounds of {f} from {} and {}",
                    flat[i],
                    flat[j]
                );
                lazy.push(l);
                flat.push(f);
            }
            // Read in a random order, so that some sets are listed through others.
            for _ in 0..lazy.len() {
                let i = rng.below(lazy.len() as u64) as usize;
                assert_eq!(lazy[i].set(), &flat[i]);
            }
            for (l, f) in lazy.iter().zip(&flat) {
                assert_eq!(l.set(), f);
            }
        }
    }

    /// Sets made and dropped one after another have ids of their own, though each new node may
    /// take the place the one before it was freed from; a copy has its set's id.
    #[test]
    fn a_dropped_set_passes_on_no_id() {
        let mut ids = std::collections::HashSet::new();
        for n in 0..1000 {
            let one = Ints::of(IntervalSet::of(n, n));
            let made = Ints::forward(&Op::Add, &one, &one);
            assert_eq!(made.clone().id(), made.id());
            assert!(ids.insert(one.id()), "the id of {{{n}}} was another set's");
            assert!(
                ids.insert(made.id()),
                "the id of {{{}}} was another set's",
                2 * n
            );
        }
    }

    /// A chain of 200,000 levels `s + 1` joined with `{0}`, each made from the one before, is
    /// listed and dropped without recursion: `[0, 200000]`.
    #[test]
    fn a_long_chain_lists_and_drops() {
        let (zero, one) = (
            Ints::of(IntervalSet::of(0, 0)),
            Ints::of(IntervalSet::of(1, 1)),
        );
        let chain = || {
            (0..200_000).fold(zero.clone(), |s, _| {
                Ints::forward(&Op::Add, &s, &one).join(&zero)
            })
        };
        let s = chain();
        let top = End::Fin(Num::from(200_000));
        assert_eq!(s.bounds(), Some((&End::of(0), &top)));
        assert_eq!(s.set(), &IntervalSet::range(End::of(0), top.clone()));
        drop(s);
        // Dropped before it is listed.
        drop(chain());
    }
}
