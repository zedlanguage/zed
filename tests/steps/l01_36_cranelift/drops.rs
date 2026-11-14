//! The runtime's drop of a reference: one count write when the cell stays live, and work
//! linear in the cells freed otherwise (COMPLEXITY.md R8). The measurements at two sizes are in
//! `bench/drops.rs`; the tests here are their small instances.

use zed_kernel::Value;
use zed_rt::{Heap, Obj, Word};

/// A heap of `n` strings and a tuple holding them all.
pub(crate) fn wide(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let parts: Vec<Word> = (0..n).map(|_| h.fresh(&Value::str("a")).unwrap()).collect();
    let w = h.alloc(Obj::Tuple(parts.into()));
    (h, w)
}

/// A heap of `n` tuples, each holding the next and a string, as a list is held.
pub(crate) fn deep(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let mut w = Word::int(0);
    for _ in 0..n {
        let s = h.fresh(&Value::str("a")).unwrap();
        w = h.alloc(Obj::Tuple(vec![s, w].into()));
    }
    (h, w)
}

/// A heap of `n` live strings, and the last with `n + 1` references.
pub(crate) fn shared(n: usize) -> (Heap, Word) {
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

/// The drop of the last reference to a tuple of strings or a list frees every cell; drops that
/// leave a string held free nothing.
#[test]
fn a_last_drop_frees_every_cell_and_an_earlier_one_none() {
    // Three strings and their tuple; three strings and the three tuples of the list.
    for (make, cells) in [(wide as fn(usize) -> (Heap, Word), 4), (deep, 6)] {
        let (mut h, w) = make(3);
        assert_eq!(h.live(), cells);
        h.dec(w).unwrap();
        assert_eq!(h.live(), 0);
    }
    let (mut h, w) = shared(3);
    for _ in 0..3 {
        h.dec(w).unwrap();
        assert_eq!(h.live(), 3);
    }
    h.dec(w).unwrap();
    assert_eq!(h.live(), 2);
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
