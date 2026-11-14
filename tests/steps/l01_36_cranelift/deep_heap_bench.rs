//! The measurements of `deep_heap.rs` at two sizes, run by `tools/run_tests.sh --bench`
//! (TEST-bench-split): making, reading, matching and releasing a list, and compiling and running
//! a wide function, each in time linear in its size; and the checks of `deep_heap.rs` at the
//! depths and widths past which the recursive runtime overflowed its stack (author P178: a test
//! that needs an unusual size is a benchmark). Their small instances are in `deep_heap.rs`.

use std::sync::Mutex;

use zed_kernel::{Evaluator, Pattern, Value, World};
use zed_rt::{Heap, Obj, Paths, Word};
use zed_tests::deep::{in_tuple, nested};
use zed_tests::scaling;
use zedc::zir::lower::lower;
use zedc::zir::memory::plan;

use super::{
    a_difference_at_the_bottom_fails, a_level_of_a_list_of_pairs_is_one_small_cell_at,
    a_pattern_binds_the_last_element, each_shape_enters_and_leaves_the_heap, in_tuples,
    list_read_from_a_port_runs_natively, one_path, release_keeps_only_the_last_element, wide,
};

/// A stack of 64 KiB for a test thread, smaller than the frame of `wide(WIDE)`.
const SMALL_STACK: usize = 64 << 10;

/// The depth of the scaling tests, and 8 times it; below about 160,000 cells the run is still
/// in the fast caches (COMPLEXITY.md K22).
const N: usize = 400_000;

/// The width of the wide function, and 8 times it.
const WIDE: usize = 5_000;

/// A heap holding the list of `n` cells.
fn list_heap(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let w = h.fresh(&nested(in_tuple, n, Value::Int(0))).unwrap();
    (h, w)
}

/// The list of [`list_heap`] built cell by cell, with no value kept in any cell: a cell made by
/// `Heap::fresh` keeps the value it was made from, so a read of it took the same few thousand
/// instructions at every size and timed nothing of the list.
fn unread_list_heap(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let mut w = Word::int(0);
    for k in 0..n {
        w = h.alloc(Obj::Tuple(vec![Word::int(k as i64), w].into()));
    }
    (h, w)
}

/// The heaps of each size, `n` and `8n`, each taken by one run.
type Heaps = Mutex<[(usize, Vec<(Heap, Word)>); 2]>;

/// A heap made by `make` for each run at each of `n` and `8n`, as many as the meter takes,
/// built before any timing starts.
fn heaps(n: usize, make: fn(usize) -> (Heap, Word)) -> Heaps {
    let (small_runs, large_runs) = scaling::Meter::new().runs();
    Mutex::new(
        [(n, small_runs), (scaling::FACTOR * n, large_runs)]
            .map(|(m, runs)| (m, (0..runs).map(|_| make(m)).collect())),
    )
}

/// One of the heaps of size `n` that [`heaps`] built.
fn take(heaps: &Heaps, n: usize) -> (Heap, Word) {
    let mut heaps = heaps.lock().unwrap();
    let at = heaps.iter_mut().find(|(m, _)| *m == n).unwrap();
    at.1.pop().expect("a heap for each run")
}

#[test]
fn making_a_deep_value_scales() {
    let n = N;
    let lists = [n, scaling::FACTOR * n].map(|m| (m, nested(in_tuple, m, Value::Int(0))));
    let used = Mutex::new(Vec::new());
    scaling::check("Heap::fresh on a list", n, |m| {
        let v = &lists.iter().find(|(k, _)| *k == m).unwrap().1;
        let mut h = Heap::new();
        h.fresh(v).unwrap();
        used.lock().unwrap().push(h);
    });
}

/// Each run reads a heap of its own: a cell keeps the value read from it, so a second read of
/// one heap would time only that kept value. A list of 3 built the same way reads as the list.
#[test]
fn reading_a_deep_value_scales() {
    let n = N;
    let heaps = heaps(n, unread_list_heap);
    let (mut h, w) = unread_list_heap(3);
    assert_eq!(h.value(w).unwrap(), nested(in_tuple, 3, Value::Int(0)));
    let used = Mutex::new(Vec::new());
    scaling::check("Heap::value on a list", n, |m| {
        let (mut h, w) = take(&heaps, m);
        let v = h.value(w).unwrap();
        used.lock().unwrap().push((h, v));
    });
}

#[test]
fn matching_a_deep_pattern_scales() {
    let n = N;
    let heaps = Mutex::new([n, scaling::FACTOR * n].map(|m| (m, list_heap(m))));
    let patterns = [n, scaling::FACTOR * n].map(|m| (m, in_tuples(m, Pattern::Wild)));
    scaling::check("Heap::matches on a list", n, |m| {
        let mut heaps = heaps.lock().unwrap();
        let (_, (h, w)) = heaps.iter_mut().find(|(k, _)| *k == m).unwrap();
        let p = &patterns.iter().find(|(k, _)| *k == m).unwrap().1;
        assert!(
            h.matches(p, *w, &mut Paths::default(), &mut Vec::new())
                .unwrap()
        );
    });
}

#[test]
fn releasing_a_deep_value_scales() {
    let n = N;
    let paths = [n, scaling::FACTOR * n].map(|m| (m, one_path(&vec![1; m])));
    let heaps = heaps(n, list_heap);
    let used = Mutex::new(Vec::new());
    scaling::check("Heap::release on a list", n, |m| {
        let (paths, end) = &paths.iter().find(|(k, _)| *k == m).unwrap().1;
        let (mut h, w) = take(&heaps, m);
        h.release(w, paths, &[*end]).unwrap();
        used.lock().unwrap().push(h);
    });
}

/// Compiling and running the wide function natively, at `WIDE` and `8 * WIDE` concatenations, on a
/// thread of 64 KiB: the frame of each is larger than that thread's stack. The work is
/// linear in the width: the code generator's passes, Cranelift's at `OptLevel::None`
/// (COMPLEXITY.md Z15), and the stack probes, which touch each page of the frame once.
#[test]
fn a_wide_function_runs_in_time_linear_in_its_width() {
    let programs = [WIDE, scaling::FACTOR * WIDE].map(|k| {
        let g = zed_native::legalize(lower(&wide(k)).unwrap());
        let p = plan(g.graph(), true);
        (k, g, p)
    });
    scaling::on_a_thread(SMALL_STACK, || {
        scaling::check(
            "native compile and run of a function of n concatenations",
            WIDE,
            |k| {
                let (_, g, p) = programs.iter().find(|(m, _, _)| *m == k).unwrap();
                drop(zed_native::run(g, p, &mut Evaluator::new(World::new())).unwrap());
            },
        )
    });
}

/// How deep the values of the tests below go, on the 2 MiB stack of a test thread: above the
/// depths at which the recursive runtime (before commit 220f60b69) overflowed that stack,
/// measured on a list of pairs: 2,143 for `Heap::value`, 5,447 for `Heap::matches`, 6,225 for
/// `Heap::release` and 7,691 for `Heap::fresh`.
const DEPTH: usize = 10_000;

/// Small instance: `a_list_read_from_a_port_runs_natively`.
#[test]
fn a_deep_list_read_from_a_port_runs_natively() {
    list_read_from_a_port_runs_natively(DEPTH);
}

/// Small instance: `each_shape_of_value_enters_and_leaves_the_heap`.
#[test]
fn each_shape_of_deep_value_enters_and_leaves_the_heap() {
    each_shape_enters_and_leaves_the_heap(DEPTH);
}

/// Small instance: `a_nested_pattern_binds_the_last_element`.
#[test]
fn a_deep_pattern_binds_the_last_element() {
    a_pattern_binds_the_last_element(DEPTH);
}

/// Small instance: `a_difference_at_the_bottom_fails_with_no_binder`.
#[test]
fn a_difference_at_the_bottom_of_a_deep_list_fails_with_no_binder() {
    a_difference_at_the_bottom_fails(DEPTH);
}

/// Small instance: `releasing_a_list_keeps_only_the_last_element`.
#[test]
fn releasing_a_deep_list_keeps_only_the_last_element() {
    release_keeps_only_the_last_element(DEPTH);
}

/// A function of 5,000 concatenations has a frame of more than 78 KiB, larger than the stack
/// of 64 KiB its thread runs on: before generated code had a stack of its own (COMPLEXITY.md
/// R10), the run stopped at that stack's guard page. A thread of 2 MiB would need about 150,000
/// concatenations, which compile in about 20 s alone and over 120 s at a load of 180. Small
/// instance: `a_function_of_concatenations_runs_as_the_kernel_does`.
#[test]
fn a_function_of_5000_concatenations_runs_on_a_smaller_thread_stack() {
    let t = wide(WIDE);
    let want = Evaluator::new(World::new()).run(&t).unwrap();
    let g = zed_native::legalize(lower(&t).unwrap());
    let p = plan(g.graph(), true);
    let got = scaling::on_a_thread(SMALL_STACK, || {
        zed_native::run(&g, &p, &mut Evaluator::new(World::new())).unwrap()
    });
    assert!(
        got.value == want,
        "the native value differs from the kernel's"
    );
}

/// The bytes a level of a list of 2^17 pairs. Small instance:
/// `a_level_of_a_list_of_pairs_is_one_small_cell`.
#[test]
fn a_level_of_a_long_list_of_pairs_is_one_small_cell() {
    a_level_of_a_list_of_pairs_is_one_small_cell_at(1 << 17);
}
