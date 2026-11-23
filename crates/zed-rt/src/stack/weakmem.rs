//! The list of stacks under a memory limit, model-checked under the Rust memory model with loom
//! (TEST-rt-weakmem, author P379: "The scheduler's own lock-free structures are tested by
//! enumerating thread interleavings exhaustively, the method of Loom"). `list` below is the
//! very source the handler of faults runs, `growing.rs`, built with loom's atomics in place of
//! std's; `loom::model` runs each test body once for every interleaving of its threads and
//! every value a load may read under the C++20 memory model, within what loom models (loom
//! 0.7.3, the version Cargo.lock holds; its src/lib.rs, "Limitations and Caveats", lines 251 to
//! 320, read 2026-11-23: "it is not possible for loom to completely model all the
//! interleavings that relaxed memory ordering allows", since it cannot run a thread's
//! operations out of order). No preemption bound is set, so the search is exhaustive for these
//! small threads within that model.
//!
//! The claims checked are G1 and G2 of `growing.rs`'s head comment and the claim at
//! `Grows::unmapped`. What loom cannot check: the handler runs in a signal handler, and the
//! kernel's ordering of `munmap` before a later `mmap` of the same addresses, which the last
//! test models as a release and an acquire.
//!
//! Negative controls, run once each on a copy and not committed (2026-11-23). A push made not
//! atomic (the head loaded, the record's `next` set, the head stored, with no exchange) makes
//! loom fail `two_pushes_at_once_are_each_reached_once` and
//! `three_pushes_at_once_are_each_reached_once`: two pushes that load the same head lose one
//! record. Weakening the orderings is not caught: with the exchange's success ordering
//! `Relaxed`, and with all three orderings of `push`, `records` and `Records::next` `Relaxed`,
//! all four tests pass. The cause is inferred, not traced in loom's source: loom does not run
//! a thread's operations out of order (the limitation quoted above), and every record here is
//! written by `Grows::new` before it is pushed, through the same thread's program order. The
//! orderings are argued at the code instead, in `growing.rs` (G1, G2); this file checks the
//! atomicity of the list under every interleaving.

mod list {
    use loom::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
    use std::ptr;

    include!("growing.rs");

    /// An empty list, leaked, so that loom's threads may share it.
    pub(super) fn empty() -> &'static Growing {
        Box::leak(Box::new(Growing {
            head: AtomicPtr::new(ptr::null_mut()),
        }))
    }
}

use list::{Growing, Grows};
use loom::sync::atomic::{AtomicBool, Ordering};
use loom::thread;

/// A record of a stack of one page, `[1000 k, 1000 k + 100)` with its guard page below it,
/// leaked as the runtime's records are; `k` tells records apart.
fn record(k: usize) -> &'static Grows {
    Box::leak(Box::new(Grows::new(
        1000 * k,
        1000 * k + 100,
        1000 * k + 50,
        10,
    )))
}

/// The `k` of each record of `list`, newest first, each checked to read as `record` wrote it.
fn walk(list: &Growing) -> Vec<usize> {
    list.records()
        .map(|r| {
            let low = r.low.load(Ordering::Relaxed);
            assert_eq!(low % 1000, 0, "a record read before it was written");
            let k = low / 1000;
            assert_eq!(r.high.load(Ordering::Relaxed), 1000 * k + 100);
            assert_eq!(r.writable.load(Ordering::Relaxed), 1000 * k + 50);
            assert_eq!(r.page, 10);
            k
        })
        .collect()
}

#[test]
fn two_pushes_at_once_are_each_reached_once() {
    loom::model(|| {
        let list = list::empty();
        let pushes: Vec<_> = (1..=2)
            .map(|k| thread::spawn(move || list.push(record(k))))
            .collect();
        for p in pushes {
            p.join().unwrap();
        }
        let mut seen = walk(list);
        seen.sort_unstable();
        assert_eq!(seen, [1, 2]);
    });
}

#[test]
fn three_pushes_at_once_are_each_reached_once() {
    loom::model(|| {
        let list = list::empty();
        let pushes: Vec<_> = (1..=3)
            .map(|k| thread::spawn(move || list.push(record(k))))
            .collect();
        for p in pushes {
            p.join().unwrap();
        }
        let mut seen = walk(list);
        seen.sort_unstable();
        assert_eq!(seen, [1, 2, 3]);
    });
}

/// A walk that runs while two records are pushed sees a whole list: each record it reaches
/// reads as written, none twice, and every record older than the newest it reaches, the one
/// pushed before the walk began included.
#[test]
fn a_walk_beside_a_push_sees_a_whole_list() {
    loom::model(|| {
        let list = list::empty();
        list.push(record(1));
        let pushes: Vec<_> = (2..=3)
            .map(|k| thread::spawn(move || list.push(record(k))))
            .collect();
        let seen = walk(list);
        assert_eq!(seen.last(), Some(&1), "{seen:?}");
        let mut sorted = seen.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), seen.len(), "{seen:?}");
        for p in pushes {
            p.join().unwrap();
        }
    });
}

/// The case at `Grows::unmapped`: the thread that drops a stack marks it unmapped and then
/// unmaps it; a thread whose fault follows the unmap, through the kernel's lock on the address
/// space (modeled by `unmapped`, a release store and an acquire load), finds no stack at an
/// address of the old range, so it never makes that range writable again.
#[test]
fn a_walk_after_the_unmap_does_not_see_the_stack() {
    loom::model(|| {
        let list = list::empty();
        let r = record(1);
        list.push(r);
        let unmapped: &'static AtomicBool = Box::leak(Box::new(AtomicBool::new(false)));
        let drop = thread::spawn(move || {
            r.unmapped();
            unmapped.store(true, Ordering::Release);
        });
        let fault = thread::spawn(move || {
            if unmapped.load(Ordering::Acquire) {
                assert!(list.find(1020).is_none(), "an unmapped stack was found");
            }
        });
        drop.join().unwrap();
        fault.join().unwrap();
        assert!(list.find(1020).is_none());
    });
}
