//! The spans `[l, h]` of the cases of kept tests on one name ([`crate::product`]'s
//! `KeptTests`), each with the addresses of the tests kept under it, in a persistent tree
//! ordered by `(l, h)`. Each node holds the least `h` of its subtree, so that the spans that
//! lie inside a run of integers the name has no member in, and reach into a part of it just
//! taken out, are found in time that grows with how many there are.
//!
//! Complexity tradeoff: naive, a watched member per span, the least member of the name in the
//! span, moved to the next member when a test takes it out: `O(log k)` a move, but `k` spans
//! that watch one member all move each time it is taken out, so `m` holes cut one after
//! another at that member cost `Θ(k·m)`. An index by `l` alone, or by `h` alone, visits each
//! live span that starts (or ends) inside the run, `Θ(k·m)` again. Used: a treap (Seidel and
//! Aragon, "Randomized search trees", Algorithmica 16, 1996, doi:10.1007/BF01940876; the full
//! comment is in module [`zed_collections::priority`]), the generic one of
//! [`zed_collections::treap`] (plan row DRY-persistent-structures-rest), ordered by `(l, h)` with a
//! priority drawn at random once per run ([`priority`]), each node's summary the least `h` below
//! it, as McCreight's priority search tree answers a three-sided query ("Priority search
//! trees", SIAM J. Comput. 14, 1985, doi:10.1137/0214021, cited in this crate's `lib.rs`,
//! References; read 2026-11-21, PDF, LibGen, verification only: the abstract, operation (4),
//! "enumerate those pairs [x, y] in D such that x0 <= x <= x1 and y <= y1", "in at most
//! O(log n + s) time", and insert and delete in `O(log n)`; the full comment is at
//! `Pst` in `product.rs`): the spans with `l` in a range and `h` below a bound in
//! `O((f + 1) log k)` expected for `f` found, where the tree's depth is `O(log k)` in
//! expectation over the draw for every set of spans. In a run the shape depends on the set
//! alone, so two trees of one set are equal as values; the shape is never shown (the tree's
//! `Debug` lists the spans in order). Tradeoff: the bound holds in expectation, not for every
//! draw, and the bound is `O((f + 1) log k)`, not McCreight's `O(log k + f)`, since each span
//! found is reached by its own descent. Correction (2026-11-21): this said a McCreight tree
//! bounds the depth "at the cost of rebuilding on deletion"; his sec. 3 gives balanced
//! insertion and deletion in logarithmic time on a balanced tree with a constant number of
//! rotations per update, and no rebuilding. The cost of a McCreight tree here is the extra
//! code for those rotations, not a rebuild. Test
//! `l01_39_scope_relations::xst::s4::bench::holes_cut_one_at_a_time_scale`.

use zed_collections::priority::Priorities;
use zed_collections::treap::{self, Item, Tree};
use zedc_lattice::interval::Num;

use crate::address::Address;

/// A span `[l, h]`, its key `(l, h)`, with the tests kept under it; the summary of a subtree is
/// its least `h`.
#[derive(Clone, PartialEq, Eq)]
struct Span {
    key: (Num, Num),
    at: imbl::OrdSet<Address>,
}

impl Item for Span {
    type Key = (Num, Num);
    type Sum = Num;

    fn key(&self) -> &(Num, Num) {
        &self.key
    }

    fn priority(&self) -> u64 {
        priority(&self.key.0, &self.key.1)
    }

    fn sum(&self, left: Option<&Num>, right: Option<&Num>) -> Num {
        let mut least = &self.key.1;
        for c in [left, right].into_iter().flatten() {
            if c < least {
                least = c;
            }
        }
        least.clone()
    }
}

/// A persistent set of spans, each with the tests kept under it.
#[derive(Clone, Default)]
pub(crate) struct Spans {
    root: Tree<Span>,
}

/// The same spans, each with the same tests: in a run one set has one shape, so this is the
/// equality of the trees as values.
impl PartialEq for Spans {
    fn eq(&self, other: &Spans) -> bool {
        treap::len(&self.root) == treap::len(&other.root)
            && treap::iter(&self.root).eq(treap::iter(&other.root))
    }
}

impl Eq for Spans {}

/// The spans in order, each with its tests: the shape, which depends on the run's draw of
/// priorities, is left out.
impl std::fmt::Debug for Spans {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(treap::iter(&self.root).map(|s| (&s.key.0, &s.key.1, &s.at)))
            .finish()
    }
}

/// The priorities of the spans, drawn once per run ([`zed_collections::priority`]).
static PRIORITIES: Priorities = Priorities::new(4);

/// The priority of the span `[l, h]`: the run's random polynomial of degree 4 at a random
/// polynomial hash ([`Priorities::hash`]) of the ends as [`end_key`]s, not as `Num`s. `Num`'s
/// `Hash` writes an end in `i64` as 8 bytes and one past it as 16 with nothing between, so two
/// spans can write one stream (`[0, 2^64 - 1]` and `[-2^64, 0]` both write `0^8, 0xff^8, 0^8`)
/// and would tie whatever the draw. An [`end_key`] writes its variant first (8 bytes), and the
/// variant fixes the length of what follows (16 bytes for `Ok`, 1 for `Err`), so the stream of
/// a pair of keys is read back into the pair: distinct pairs of keys write distinct streams.
///
/// The bound. A stream is at most 48 bytes, 6 words and the length word, at most 14 symbols
/// (two a word, module [`zed_collections::priority`]), so two spans of distinct keys tie with
/// probability at most `15/p < 1/2^58` a pair (`p = 2^64 - 59`); the priorities are otherwise
/// 5-wise independent and uniform, and every node's depth is `O(log k)` in expectation for
/// every set of spans (Seidel and Aragon, "Randomized search trees", Algorithmica 16, 1996,
/// doi:10.1007/BF01940876, Theorem 3.3 and section 6: 5-wise independence suffices for
/// logarithmic expected depth; the full comment and the proof are in module
/// [`zed_collections::priority`]), where the fixed hash this replaces had no bound for chosen spans
/// (COMPLEXITY.md K123). Two ends outside `i128` of one sign have one key, so spans that
/// differ only in such ends tie whatever the draw, each adding at most one to a depth: not
/// proved small for chosen spans with ends past `i128` (cost only: a priority sets a node's
/// place in the treap, never which spans it holds). Test
/// `spans_of_one_num_hash_stream_take_two_priorities` (the two spans above, which tied before
/// [`end_key`]); it cannot catch a tie of probability `15/p`, nor measure the depth.
fn priority(l: &Num, h: &Num) -> u64 {
    PRIORITIES.hash(&(end_key(l), end_key(h)))
}

/// An end as a hash key: its value when it is in `i128`, else its sign, the variant telling
/// the two apart ([`priority`]).
fn end_key(n: &Num) -> Result<i128, i8> {
    n.to_i128().ok_or_else(|| n.signum())
}

/// Adds to `out` the tests of the spans of `t` with `l` above `after` and at most `upto`, and
/// `h` below `before`; `None` is no bound.
fn within(
    t: &Tree<Span>,
    after: Option<&Num>,
    upto: Option<&Num>,
    before: Option<&Num>,
    out: &mut std::collections::BTreeSet<Address>,
) {
    let Some(n) = t else {
        return;
    };
    if before.is_some_and(|b| n.sum() >= b) {
        return;
    }
    let s = n.item();
    let (l, h) = (&s.key.0, &s.key.1);
    let past = after.is_none_or(|a| l > a);
    let short = upto.is_none_or(|u| l <= u);
    if past && short && before.is_none_or(|b| h < b) {
        out.extend(s.at.iter().cloned());
    }
    if past {
        within(n.left(), after, upto, before, out);
    }
    if short {
        within(n.right(), after, upto, before, out);
    }
}

impl Spans {
    pub(crate) fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Adds the test `k` under the span `[l, h]`. `O(log k)` expected: a walk to find the span,
    /// and [`treap::insert_mut`], which puts the span with its new tests in place of the old.
    pub(crate) fn insert(&mut self, l: &Num, h: &Num, k: &Address) {
        let key = (l.clone(), h.clone());
        let at = match treap::get(&self.root, &key) {
            Some(s) => s.at.update(k.clone()),
            None => imbl::OrdSet::unit(k.clone()),
        };
        treap::insert_mut(&mut self.root, Span { key, at });
    }

    /// Takes the test `k` from the span `[l, h]`, and the span when no test is left under it.
    /// `O(log k)` expected. A span without `k`, or no span, leaves the tree as it is.
    pub(crate) fn remove(&mut self, l: &Num, h: &Num, k: &Address) {
        let key = (l.clone(), h.clone());
        let Some(s) = treap::get(&self.root, &key).filter(|s| s.at.contains(k)) else {
            return;
        };
        let at = s.at.without(k);
        if at.is_empty() {
            treap::remove_mut(&mut self.root, &key);
        } else {
            treap::insert_mut(&mut self.root, Span { key, at });
        }
    }

    /// Adds to `out` the tests of the spans whose `l` is above `after` and at most `upto`, and
    /// whose `h` is below `before`; `None` is no bound. `O((f + 1) log k)` expected for `f`
    /// spans found.
    pub(crate) fn within(
        &self,
        after: Option<&Num>,
        upto: Option<&Num>,
        before: Option<&Num>,
        out: &mut std::collections::BTreeSet<Address>,
    ) {
        within(&self.root, after, upto, before, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;
    use zed_kernel::Term;
    use zed_kernel::Value;
    use zed_kernel::bits::BitLen;

    fn addr(i: i64) -> Address {
        Address::of(&Term::Lit(Value::Int(i)))
    }

    fn num(i: i64) -> Num {
        Num::from(i)
    }

    /// The tree's shape and its least ends hold, and the heap order of the priorities.
    fn check(t: &Tree<Span>) -> usize {
        let Some(n) = t else {
            return 0;
        };
        let mut least = n.item().key.1.clone();
        for c in [n.left(), n.right()].into_iter().flatten() {
            assert!(c.rank() < n.rank());
            least = least.min(c.sum().clone());
        }
        if let Some(c) = n.left() {
            assert!(c.item().key < n.item().key);
        }
        if let Some(c) = n.right() {
            assert!(c.item().key > n.item().key);
        }
        assert_eq!(&least, n.sum());
        assert!(!n.item().at.is_empty());
        1 + check(n.left()).max(check(n.right()))
    }

    /// Random inserts, removals and queries agree with a list; one set built in two orders is
    /// one tree; the depth stays near `log2` of the size.
    #[test]
    fn spans_agree_with_a_list() {
        let (mut rng, _) = crate::seed::Rng::fresh("spans_agree_with_a_list");
        let mut next = |n: u64| rng.below_u64(n) as i64;
        for round in 0..16 {
            let w = if round % 2 == 0 { 8 } else { 400 };
            let mut s = Spans::default();
            let mut list: BTreeSet<(i64, i64, i64)> = BTreeSet::new();
            for _ in 0..(if round % 2 == 0 { 40 } else { 600 }) {
                let l = next(w as u64);
                let h = l + next(6);
                let k = next(5);
                if next(3) == 0 {
                    s.remove(&num(l), &num(h), &addr(k));
                    list.remove(&(l, h, k));
                } else {
                    s.insert(&num(l), &num(h), &addr(k));
                    list.insert((l, h, k));
                }
                let depth = check(&s.root);
                assert!(depth <= 4 * list.len().bit_len() as usize + 4);
                let (a, u, b) = (next(w as u64) - 1, next(w as u64 + 8), next(w as u64 + 8));
                let pick = [Some(a), None];
                let (a, u, b) = (
                    pick[next(2) as usize],
                    [Some(u), None][next(2) as usize],
                    [Some(b), None][next(2) as usize],
                );
                let mut got = BTreeSet::new();
                s.within(
                    a.map(num).as_ref(),
                    u.map(num).as_ref(),
                    b.map(num).as_ref(),
                    &mut got,
                );
                let want: BTreeSet<Address> = list
                    .iter()
                    .filter(|(l, h, _)| {
                        a.is_none_or(|a| *l > a)
                            && u.is_none_or(|u| *l <= u)
                            && b.is_none_or(|b| *h < b)
                    })
                    .map(|&(_, _, k)| addr(k))
                    .collect();
                assert_eq!(got, want);
            }
            let mut again = Spans::default();
            for &(l, h, k) in list.iter().rev() {
                again.insert(&num(l), &num(h), &addr(k));
            }
            assert_eq!(again, s);
        }
    }

    /// `Num`'s `Hash` writes an end in `i64` as 8 bytes and an end past it as 16, with nothing
    /// between two ends, so `[0, 2^64 - 1]` and `[-2^64, 0]` write the same 24 bytes
    /// (`0^8, 0xff^8, 0^8`, little-endian). Their priorities must still be drawn apart: they
    /// tie with probability at most `15/p` ([`priority`]), where hashing the two `Num`s as they
    /// are made them tie under every draw.
    #[test]
    fn spans_of_one_num_hash_stream_take_two_priorities() {
        let a = (num(0), Num::from((1i128 << 64) - 1));
        let b = (Num::from(-(1i128 << 64)), num(0));
        assert_ne!(priority(&a.0, &a.1), priority(&b.0, &b.1));
    }
}
