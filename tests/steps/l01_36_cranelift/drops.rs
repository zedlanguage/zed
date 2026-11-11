//! The runtime's drop of a reference: one count write when the cell stays live, and work
//! linear in the cells freed otherwise (COMPLEXITY.md R8).

use std::collections::HashMap;
use std::sync::Mutex;

use zed_kernel::Value;
use zed_rt::{Heap, Obj, Word};
use zed_tests::scaling::{self, FACTOR, TRIES};

/// The runs one measured size can take: a warming run and five for each measurement.
const RUNS: usize = 1 + 5 * TRIES;

/// A heap of `n` strings and a tuple holding them all.
fn wide(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let parts: Vec<Word> = (0..n).map(|_| h.fresh(&Value::str("a")).unwrap()).collect();
    let w = h.alloc(Obj::Tuple(parts.into()));
    (h, w)
}

/// A heap of `n` tuples, each holding the next and a string, as a list is held.
fn deep(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let mut w = Word::int(0);
    for _ in 0..n {
        let s = h.fresh(&Value::str("a")).unwrap();
        w = h.alloc(Obj::Tuple(vec![s, w].into()));
    }
    (h, w)
}

/// A heap of `n` live strings, and the last with `n + 1` references.
fn shared(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let mut w = Word::int(0);
    for _ in 0..n {
        w = h.fresh(&Value::str("a")).unwrap();
    }
    for _ in 0..n {
        h.inc(w).unwrap();
    }
    (h, w)
}

/// `what`, the time of `run` on heaps from `make`, all built before any timing starts.
fn scales(what: &str, n: usize, make: fn(usize) -> (Heap, Word), run: fn(&mut Heap, Word, usize)) {
    let heaps: HashMap<usize, Vec<(Heap, Word)>> = [n, FACTOR * n]
        .into_iter()
        .map(|m| (m, (0..RUNS).map(|_| make(m)).collect()))
        .collect();
    let heaps = Mutex::new(heaps);
    // Each heap is freed after the timing ends.
    let used = Mutex::new(Vec::new());
    scaling::check(what, n, |m| {
        let (mut h, w) = heaps.lock().unwrap().get_mut(&m).unwrap().pop().unwrap();
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
    scales("a tuple of n strings freed", 4_000, wide, free);
}

#[test]
fn freeing_a_deep_list_scales() {
    scales("a list of n strings freed", 4_000, deep, free);
}

#[test]
fn drops_that_leave_a_cell_live_scale() {
    scales(
        "n drops of one string among n live cells",
        4_000,
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

#[test]
fn a_word_that_is_not_a_cell_writes_no_count() {
    let mut h = Heap::new();
    let k = h.uncounted(Value::tuple(Vec::new()));
    for w in [Word::int(1), Word::state(), k] {
        h.dec(w).unwrap();
    }
    assert_eq!(h.stats.decrements, 0);
}
