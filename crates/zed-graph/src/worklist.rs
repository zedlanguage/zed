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
//! Switching, 1959 (no DOI). With the queue first in first out, the items are taken in passes,
//! and with no negative cycle `n - 1` passes settle every distance. Checked 2026-11-20:
//! Bellman's DOI on Crossref; none of the three read, from memory.
//! `fifo_takes_items_in_the_order_queued_each_once` checks the order the bound needs.

use std::collections::VecDeque;

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

#[cfg(test)]
mod tests {
    use super::{Order, Worklist};

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
}
