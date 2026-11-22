//! The runtime's drop of a reference: one count write when the cell stays live, and work
//! linear in the cells freed otherwise (COMPLEXITY.md R8). The small instances are in
//! `drops.rs`.

use zed_rt::{Heap, Word};
use zed_tests::scaling;

use crate::drops::{deep, shared, wide};

/// `what`, the time of `run` on heaps from `make`, one for each run the meter takes, each built
/// before its run's timing starts and freed after it ends, one held at a time
/// (`scaling::check_order_fresh`, MEM-l0126-40gb). Its bytes are held too when `allocates`; a
/// run that allocates nothing has none to compare.
fn scales(
    what: &str,
    n: usize,
    make: fn(usize) -> (Heap, Word),
    run: fn(&mut Heap, Word, usize),
    allocates: bool,
) {
    let make = |m: usize, _: usize| make(m);
    let timed = |m: usize, (mut h, w): (Heap, Word)| {
        run(&mut h, w, m);
        h
    };
    if allocates {
        scaling::check_order_fresh(what, n, 1, make, timed);
    } else {
        scaling::check_instructions_only_fresh(what, n, 1, make, timed);
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
