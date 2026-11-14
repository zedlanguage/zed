//! The runtime's drop of a reference: one count write when the cell stays live, and work
//! linear in the cells freed otherwise (COMPLEXITY.md R8). The small instances are in
//! `drops.rs`.

use std::sync::Mutex;

use zed_rt::{Heap, Word};
use zed_tests::scaling::{self, FACTOR};

use crate::drops::{deep, shared, wide};

/// `what`, the time of `run` on heaps from `make`, one for each run the meter takes, all built
/// before any timing starts.
fn scales(what: &str, n: usize, make: fn(usize) -> (Heap, Word), run: fn(&mut Heap, Word, usize)) {
    let (small_runs, large_runs) = scaling::Meter::new().runs();
    let heaps = Mutex::new(
        [(n, small_runs), (FACTOR * n, large_runs)]
            .map(|(m, runs)| (m, (0..runs).map(|_| make(m)).collect::<Vec<_>>())),
    );
    // Each heap is freed after the timing ends.
    let used = Mutex::new(Vec::new());
    scaling::check(what, n, |m| {
        let (mut h, w) = {
            let mut heaps = heaps.lock().unwrap();
            let at = heaps.iter_mut().find(|(k, _)| *k == m).unwrap();
            at.1.pop().expect("a heap for each run")
        };
        run(&mut h, w, m);
        used.lock().unwrap().push(h);
    });
}

fn free(h: &mut Heap, w: Word, _: usize) {
    h.dec(w).unwrap();
    assert_eq!(h.live(), 0);
}

#[test]
fn freeing_a_wide_tuple_scales() {
    scales("a tuple of n strings freed", 700_000, wide, free);
}

#[test]
fn freeing_a_deep_list_scales() {
    scales("a list of n strings freed", 700_000, deep, free);
}

#[test]
fn drops_that_leave_a_cell_live_scale() {
    scales(
        "n drops of one string among n live cells",
        700_000,
        shared,
        |h, w, n| {
            let live = h.live();
            for _ in 0..n {
                h.dec(w).unwrap();
            }
            assert_eq!(h.live(), live);
        },
    );
}
