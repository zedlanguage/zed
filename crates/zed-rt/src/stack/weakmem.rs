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
//! record. Those four tests do not catch a weakened ordering (b22-small9: with every ordering
//! `Relaxed` they pass), since in each a record is made on the thread that pushes it and read
//! only after a join or by that thread. The two G1 tests (TEST-rt-weakmem-orderings) make each
//! record inside the pushing thread and walk on another thread, so loom tracks the record's
//! atomics from their creation and reports a read that does not happen after it (a causality
//! violation, loom's src/rt/location.rs). Negative controls, run once each on copies of
//! `growing.rs` and not committed (2026-11-23, b22-small10): with every ordering `Relaxed`,
//! with the exchange's success `Relaxed` or `Acquire` (not a release), and with the head's
//! load in `records` `Relaxed`, both G1 tests fail and the other four pass; with the success
//! `Release`, the head's load `Acquire` and the other three orderings `Relaxed`, all six pass,
//! as G1 in `growing.rs` argues (the release sequence of the head). G2 is carried by no
//! ordering and is checked by the atomicity tests above.

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

/// G1, first case: a record pushed on one thread and reached from the head by a walk on another
/// reads as `record` wrote it. Fails when the exchange of `push` is not a release (the record's
/// writes then do not happen before the walk's reads, and loom reports a causality violation on
/// the first field the walk reads) or when the walk's load of the head is not an acquire.
#[test]
fn a_record_pushed_on_one_thread_reads_whole_on_another() {
    loom::model(|| {
        let list = list::empty();
        let push = thread::spawn(move || list.push(record(1)));
        let reader = thread::spawn(move || walk(list));
        push.join().unwrap();
        let seen = reader.join().unwrap();
        assert!(seen.is_empty() || seen == [1], "{seen:?}");
    });
}

/// G1, second case: a walk that reaches record 1 through the `next` of record 2, the two pushed
/// on different threads, reads record 1 as written. Record 1's writes happen before the walk
/// through the release sequence of record 1's exchange: record 2's exchange is a
/// read-modify-write of the head, so the walk's acquire of the head, reading record 2 or a
/// later record, synchronizes with record 1's exchange too, with no acquire in `push` or in
/// `Records::next` (the argument at G1). Fails, as the test above, when the exchange is not a
/// release.
#[test]
fn a_record_reached_through_a_newer_one_reads_whole() {
    loom::model(|| {
        let list = list::empty();
        let older = thread::spawn(move || list.push(record(1)));
        let newer = thread::spawn(move || list.push(record(2)));
        let seen = thread::spawn(move || walk(list)).join().unwrap();
        let mut sorted = seen.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), seen.len(), "{seen:?}");
        older.join().unwrap();
        newer.join().unwrap();
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
