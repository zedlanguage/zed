//! A worklist of items `0..n`, each queued at most once at a time.
//!
//! The fixed-point loops of the workspace (grammar sets, rule summaries, pair blocking, color
//! refinement, Bellman–Ford–Moore) each kept a queue of items and a flag per item saying
//! whether it was queued, so that an item waiting already is not queued twice: the queue then
//! never holds more than `n` items, and each push and pop is O(1). [`Worklist`] is that pair
//! once, taking items first in first out or last in first out as each caller did.
//!
//! Bellman–Ford–Moore: R. Bellman, "On a routing problem", Quart. Appl. Math. 16(1):87-90,
//! 1958, doi:10.1090/qam/102435; L. R. Ford, "Network flow theory", RAND paper P-923, 1956 (no
//! DOI); E. F. Moore, "The shortest path through a maze", Proc. Int. Symp. on the Theory of
//! Switching, Part II, 1959, pp. 285-292 (no DOI). Bellman read 2026-11-21 (PDF, OpenAlex's
//! cached copy, verification only): sec. 5 iterates `f_i^(k+1) = min_j (t_ij + f_j^(k))` over
//! all cities at once, and "it is clear from the physical interpretation of this iterative
//! scheme that at most (N - 1) iterations are required", since `f_i^(k)` is the least time
//! over paths of at most `k + 1` roads (sec. 5, "a path with at most one stop" for `k = 1`),
//! and a shortest path has at most `N - 1` roads; the paper assumes every `t_ij > 0` (sec. 4).
//! Ford read 2026-11-21 (scan of P-923 dated 14 August 1956, DTIC AD0422842, through the
//! Wayback Machine since DTIC was down; verification only), sec. 7, p. 9: "Scan the network
//! for a pair P_i and P_j with the property that x_i - x_j > l_ji. For this pair replace x_i
//! by x_j + l_ji. Continue this process. Eventually no such pairs can be found", with a proof
//! that the result is the least distance but no bound on the number of steps. Moore not found
//! 2026-11-21: paperclip (no result), allpapers-locate on the title (Unpaywall, OpenAlex,
//! CORE, Europe PMC: no match; dblp answered with a bot check), web search and a grounded
//! Gemini search (catalog records only; the paper was also Bell System Monograph 3523, no scan
//! found), archive.org (the proceedings, items `proceedingsofint0030vari`,
//! `proceedingsofint0030unse` and `proceedingsofint0000inte_f9v3`, are lending only, their PDF
//! and text private, and search inside is refused), LibGen title search (no match), Google
//! Scholar (sent to a block page twice), Anna's Archive (no result page, or a browser check;
//! no md5 to fetch by), welib (browser check), Sci-Hub and Sci-Net (no DOI to ask by).
//! Searched again 2026-11-21 (CITE-unfound-four), no copy found: Google Books API (429, rate
//! limit, three tries), HathiTrust full-text search (Cloudflare 403),
//! archive.org advanced search (the same lending-only items; no hit for the title or for
//! "monograph 3523"), LibGen by the proceedings title (only two reviews of the volume,
//! doi:10.1137/1003018 and doi:10.2307/3611677), bitsavers' file index (no match), a web
//! search (catalog records and secondary accounts only), a grounded agy search (timed out at
//! 300 s). Not read, so the queue form below is credited to him from secondary accounts
//! only. With the queue first in
//! first out, the items are taken in passes: pass 0 is the source, pass `k + 1` the items
//! queued while pass `k` is worked. By induction, at the end of pass `k` every item whose
//! least distance is reached by a path of at most `k` edges holds it, as in Bellman's
//! argument, so with no negative cycle `n - 1` passes settle every distance and an item is
//! queued at most `n - 1` times, O(n · m) in all.
//! `fifo_takes_items_in_the_order_queued_each_once` checks the order the bound needs; it does
//! not run a distance computation.
//!
//! Two other forms of the same pair, each written once here (DRY-graph-searches-2026-11-26):
//! [`PriorityWorklist`], which gives the queued item of least priority first (the
//! bit-weight order of zedc-presburger's modular `top_cons` loop), and [`KeyedWorklist`],
//! first in first out over keys that are not dense numbers (blocks and parts in
//! zedc-preimage's product.rs), its flags kept in an ordered set.

use crate::heap::MinHeap;
use std::collections::{BTreeSet, VecDeque};

/// Which queued item a [`Worklist`] gives next.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Order {
    /// The item queued first: the order of Bellman–Ford–Moore, whose bound on passes needs it.
    Fifo,
    /// The item queued last: a stack, which keeps the items of one change together.
    Lifo,
}

/// Items `0..n` waiting to be worked on, each queued at most once at a time.
#[derive(Clone, Debug)]
pub struct Worklist {
    items: VecDeque<usize>,
    queued: Vec<bool>,
    order: Order,
}

impl Worklist {
    /// Items `0..n`, none queued.
    pub fn new(n: usize, order: Order) -> Worklist {
        Worklist {
            items: VecDeque::new(),
            queued: vec![false; n],
            order,
        }
    }

    /// Items `0..n`, the first `k` queued in ascending order, so [`Order::Fifo`] gives `0`
    /// first and [`Order::Lifo`] gives `k - 1` first.
    pub fn first(n: usize, k: usize, order: Order) -> Worklist {
        let mut queued = vec![false; n];
        queued[..k].fill(true);
        Worklist {
            items: (0..k).collect(),
            queued,
            order,
        }
    }

    /// Items `0..n`, all queued in ascending order.
    pub fn all(n: usize, order: Order) -> Worklist {
        Worklist::first(n, n, order)
    }

    /// Queues `i` unless it is queued already; whether it was queued now.
    pub fn push(&mut self, i: usize) -> bool {
        if self.queued[i] {
            return false;
        }
        self.queued[i] = true;
        self.items.push_back(i);
        true
    }

    /// Takes the next item, in the list's order; it may be queued again from then on.
    pub fn pop(&mut self) -> Option<usize> {
        let i = match self.order {
            Order::Fifo => self.items.pop_front(),
            Order::Lifo => self.items.pop_back(),
        }?;
        self.queued[i] = false;
        Some(i)
    }

    /// Whether `i` is queued.
    pub fn is_queued(&self, i: usize) -> bool {
        self.queued[i]
    }
}

/// Items `0..n` waiting to be worked on, each queued at most once at a time with a priority
/// given when it is queued; the item of least priority comes first, ties going to the lesser
/// item.
///
/// An item queued already keeps the priority it was queued with, whatever a later push asks:
/// a caller that raises an item's priority while it waits sees the change only when the item
/// is queued again. So the heap holds at most one entry per item, no entry is ever stale, and
/// the heap never holds more than `n` entries.
// Complexity tradeoff: each push of an item not queued and each pop costs O(log n) on the
// heap, a push of a queued item O(1). The alternative, a heap with a decrease-key (a pairing
// or indexed heap), would let a waiting item move, which no caller needs; lazy deletion (a
// new entry at each push, stale ones skipped at pop, as [`crate::Dijkstra`] does) lets the
// heap grow to the number of pushes.
#[derive(Clone, Debug)]
pub struct PriorityWorklist<P> {
    heap: MinHeap<(P, usize)>,
    queued: Vec<bool>,
}

impl<P: Ord> PriorityWorklist<P> {
    /// Items `0..n`, none queued.
    pub fn new(n: usize) -> PriorityWorklist<P> {
        PriorityWorklist {
            heap: MinHeap::new(),
            queued: vec![false; n],
        }
    }

    /// Items `0..n` for the `n` priorities given, each queued with its own; the heap is built
    /// at once in O(n), not by `n` pushes in O(n log n).
    pub fn all(priorities: impl IntoIterator<Item = P>) -> PriorityWorklist<P> {
        let heap: MinHeap<(P, usize)> = priorities
            .into_iter()
            .enumerate()
            .map(|(i, p)| (p, i))
            .collect();
        PriorityWorklist {
            queued: vec![true; heap.len()],
            heap,
        }
    }

    /// Queues `i` with priority `p` unless it is queued already; whether it was queued now.
    pub fn push(&mut self, i: usize, p: P) -> bool {
        if self.queued[i] {
            return false;
        }
        self.queued[i] = true;
        self.heap.push((p, i));
        true
    }

    /// Takes the queued item of least priority, with its priority; it may be queued again
    /// from then on.
    pub fn pop(&mut self) -> Option<(P, usize)> {
        let (p, i) = self.heap.pop()?;
        self.queued[i] = false;
        Some((p, i))
    }

    /// Whether `i` is queued.
    pub fn is_queued(&self, i: usize) -> bool {
        self.queued[i]
    }
}

/// Keys waiting to be worked on, first in first out, each queued at most once at a time: a
/// [`Worklist`] for keys that are not numbers `0..n`, its flags an ordered set of the keys
/// queued.
// Complexity tradeoff: a push or pop is O(log q) comparisons of keys for the q keys queued,
// against O(1) for [`Worklist`] on dense numbers; numbering the keys first would cost a map
// from key to number of the same O(log) per lookup, and keys found as the work goes would
// need that map to grow. A hash set would save the log factor but needs `Hash` and gives
// nothing in the order, which no caller reads; the callers' keys are ordered already.
#[derive(Clone, Debug)]
pub struct KeyedWorklist<K> {
    items: VecDeque<K>,
    queued: BTreeSet<K>,
}

impl<K: Ord + Clone> KeyedWorklist<K> {
    /// No key queued.
    pub fn new() -> KeyedWorklist<K> {
        KeyedWorklist {
            items: VecDeque::new(),
            queued: BTreeSet::new(),
        }
    }

    /// Queues `k` at the back unless it is queued already; whether it was queued now.
    pub fn push(&mut self, k: K) -> bool {
        if !self.queued.insert(k.clone()) {
            return false;
        }
        self.items.push_back(k);
        true
    }

    /// Takes the key queued first; it may be queued again from then on.
    pub fn pop(&mut self) -> Option<K> {
        let k = self.items.pop_front()?;
        self.queued.remove(&k);
        Some(k)
    }

    /// Whether `k` is queued.
    pub fn is_queued(&self, k: &K) -> bool {
        self.queued.contains(k)
    }

    /// Whether no key is queued.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// The number of keys queued.
    pub fn len(&self) -> usize {
        self.items.len()
    }
}

impl<K: Ord + Clone> Default for KeyedWorklist<K> {
    fn default() -> KeyedWorklist<K> {
        KeyedWorklist::new()
    }
}

/// The keys of `iter` queued in its order, a key met again left where it was first queued.
impl<K: Ord + Clone> FromIterator<K> for KeyedWorklist<K> {
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> KeyedWorklist<K> {
        let mut w = KeyedWorklist::new();
        for k in iter {
            w.push(k);
        }
        w
    }
}

#[cfg(test)]
mod tests {
    use super::{KeyedWorklist, Order, PriorityWorklist, Worklist};
    use crate::seed::Rng;
    use std::collections::{BTreeSet, VecDeque};

    /// First in first out from `all`: ascending, an item queued while waiting is not queued
    /// twice, and one taken may be queued again.
    #[test]
    fn fifo_takes_items_in_the_order_queued_each_once() {
        let mut w = Worklist::all(4, Order::Fifo);
        assert!(!w.push(2));
        assert_eq!(w.pop(), Some(0));
        assert!(!w.is_queued(0));
        assert!(w.push(0));
        let rest: Vec<usize> = std::iter::from_fn(|| w.pop()).collect();
        assert_eq!(rest, [1, 2, 3, 0]);
    }

    /// Last in first out from `first(5, 3)`: 2 first, and items past `k` start unqueued.
    #[test]
    fn lifo_takes_the_last_queued_first() {
        let mut w = Worklist::first(5, 3, Order::Lifo);
        assert!(!w.is_queued(4));
        assert!(w.push(4));
        assert!(!w.push(1));
        let all: Vec<usize> = std::iter::from_fn(|| w.pop()).collect();
        assert_eq!(all, [4, 2, 1, 0]);
    }

    /// The least priority first, ties to the lesser item; a push of a queued item keeps its
    /// first priority, even a lower one asked later; a popped item may be queued again; an
    /// empty list and a list of no items give nothing.
    #[test]
    fn priority_takes_the_least_and_keeps_a_waiting_items_priority() {
        let mut w = PriorityWorklist::all([5u64, 3, 3, 9]);
        assert!(!w.push(3, 0));
        assert_eq!(w.pop(), Some((3, 1)));
        assert!(!w.is_queued(1));
        assert!(w.push(1, 4));
        let rest: Vec<(u64, usize)> = std::iter::from_fn(|| w.pop()).collect();
        assert_eq!(rest, [(3, 2), (4, 1), (5, 0), (9, 3)]);
        assert_eq!(w.pop(), None);
        let mut none = PriorityWorklist::<u64>::new(0);
        assert_eq!(none.pop(), None);
        assert_eq!(PriorityWorklist::<u64>::all([]).pop(), None);
    }

    /// First in first out over keys: a key queued while waiting is not queued twice, one taken
    /// may be queued again, and `collect` keeps the first place of a repeated key.
    #[test]
    fn keyed_takes_keys_in_the_order_queued_each_once() {
        let mut w: KeyedWorklist<&str> = ["b", "a", "b", "c"].into_iter().collect();
        assert_eq!(w.len(), 3);
        assert!(!w.push("a"));
        assert_eq!(w.pop(), Some("b"));
        assert!(!w.is_queued(&"b"));
        assert!(w.push("b"));
        let rest: Vec<&str> = std::iter::from_fn(|| w.pop()).collect();
        assert_eq!(rest, ["a", "c", "b"]);
        assert!(w.is_empty());
        assert_eq!(w.pop(), None);
    }

    /// Random pushes and pops on each list against the queue and flags its callers wrote
    /// inline before (DRY-graph-searches-2026-11-26), kept here as the oracle: a `VecDeque`
    /// and a `Vec<bool>`, a `MinHeap` and a `Vec<bool>` (zedc-presburger modular.rs), and a
    /// `VecDeque` and a `BTreeSet` (zedc-preimage product.rs). Each step's answer and the
    /// order taken must agree. Catches a flag not set or not cleared, a wrong end taken, a
    /// priority replaced while waiting; cannot catch a cost above the claimed one.
    #[test]
    fn each_list_agrees_with_the_inline_queue_and_flags_it_replaced() {
        let (mut rng, seed) = Rng::fresh("each_list_agrees_with_the_inline_queue_and_flags");
        for _ in 0..300 {
            let n = 1 + rng.below(12);
            let order = if rng.coin() { Order::Fifo } else { Order::Lifo };
            let mut w = Worklist::new(n, order);
            let (mut q, mut flag) = (VecDeque::new(), vec![false; n]);
            let mut p = PriorityWorklist::new(n);
            let (mut heap, mut pflag) = (crate::MinHeap::new(), vec![false; n]);
            let mut k = KeyedWorklist::new();
            let (mut kq, mut kset) = (VecDeque::new(), BTreeSet::new());
            for _ in 0..40 {
                if rng.below(3) < 2 {
                    let i = rng.below(n);
                    let pr = rng.below(4);
                    let fresh = !flag[i];
                    if fresh {
                        flag[i] = true;
                        q.push_back(i);
                    }
                    assert_eq!(w.push(i), fresh, "seed {seed}");
                    let pfresh = !pflag[i];
                    if pfresh {
                        pflag[i] = true;
                        heap.push((pr, i));
                    }
                    assert_eq!(p.push(i, pr), pfresh, "seed {seed}");
                    let key = format!("k{i}");
                    let kfresh = kset.insert(key.clone());
                    if kfresh {
                        kq.push_back(key.clone());
                    }
                    assert_eq!(k.push(key), kfresh, "seed {seed}");
                } else {
                    let want = match order {
                        Order::Fifo => q.pop_front(),
                        Order::Lifo => q.pop_back(),
                    };
                    if let Some(i) = want {
                        flag[i] = false;
                    }
                    assert_eq!(w.pop(), want, "seed {seed}");
                    let pwant = heap.pop();
                    if let Some((_, i)) = pwant {
                        pflag[i] = false;
                    }
                    assert_eq!(p.pop(), pwant, "seed {seed}");
                    let kwant = kq.pop_front();
                    if let Some(key) = &kwant {
                        kset.remove(key);
                    }
                    assert_eq!(k.pop(), kwant, "seed {seed}");
                }
                for i in 0..n {
                    assert_eq!(w.is_queued(i), flag[i], "seed {seed}");
                    assert_eq!(p.is_queued(i), pflag[i], "seed {seed}");
                    assert_eq!(
                        k.is_queued(&format!("k{i}")),
                        kset.contains(&format!("k{i}"))
                    );
                }
                assert_eq!(k.len(), kq.len(), "seed {seed}");
            }
        }
    }
}
