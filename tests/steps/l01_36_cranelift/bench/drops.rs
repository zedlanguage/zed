//! The runtime's drop of a reference: one count write when the cell stays live, and work
//! linear in the cells freed otherwise (COMPLEXITY.md R8). The small instances are in
//! `drops.rs`.

use std::sync::Mutex;

use zed_rt::{Heap, Word};
use zed_tests::scaling::{self, FACTOR};

use crate::drops::{deep, shared, wide};

/// `what`, the time of `run` on heaps from `make`, one for each run the meter takes, all built
/// before any timing starts. Its bytes are held too when `allocates`; a run that allocates
/// nothing has none to compare.
fn scales(
    what: &str,
    n: usize,
    make: fn(usize) -> (Heap, Word),
    run: fn(&mut Heap, Word, usize),
    allocates: bool,
) {
    let (small_runs, large_runs) = scaling::Meter::new().runs();
    let heaps = Mutex::new(
        [(n, small_runs), (FACTOR * n, large_runs)]
            .map(|(m, runs)| (m, (0..runs).map(|_| make(m)).collect::<Vec<_>>())),
    );
    // Each heap is freed after the timing ends.
    let used = Mutex::new(Vec::new());
    let timed = |m| {
        let (mut h, w) = {
            let mut heaps = heaps.lock().unwrap();
            let at = heaps.iter_mut().find(|(k, _)| *k == m).unwrap();
            at.1.pop().expect("a heap for each run")
        };
        run(&mut h, w, m);
        used.lock().unwrap().push(h);
    };
    if allocates {
        scaling::check(what, n, timed);
    } else {
        scaling::check_instructions_only(what, n, 1, timed);
    }
}

fn free(h: &mut Heap, w: Word, _: usize) {
    h.dec(w).unwrap();
    assert_eq!(h.live(), 0);
}

#[test]
fn freeing_a_wide_tuple_scales() {
    scales("a tuple of n strings freed", 700_000, wide, free, true);
}

#[test]
fn freeing_a_deep_list_scales() {
    scales("a list of n strings freed", 700_000, deep, free, true);
}

/// A drop that leaves its cell live writes one count and allocates nothing, so only its work is
/// compared. Its bytes were compared until FAIL-scaling-cold-8n-bytes; the one allocation in a
/// run was the growth of `used`, which came at 8n or not by the number of runs before it, and
/// since TEST-scaling-runs it did not, so the check panicked that the larger run allocated none.
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
        false,
    );
}
