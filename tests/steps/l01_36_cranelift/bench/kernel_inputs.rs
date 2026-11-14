//! A value the native runtime hands to the kernel is made from its cells once, so a record
//! handed to the kernel many times, or read many times, is read once (COMPLEXITY.md R1). The
//! small instances are in `kernel_inputs.rs`.

use std::sync::Mutex;

use zed_kernel::Evaluator;
use zed_rt::{Heap, Obj, Word};
use zed_tests::scaling;

use crate::kernel_inputs::compared;
use crate::planned;
use crate::scaling::strings;

/// The record holds `64n` strings and is handed to the kernel `n` times: read whole each time,
/// the work would grow 64 times at `8n`.
#[test]
fn a_record_handed_to_the_kernel_many_times_scales() {
    let n = 3_000;
    let at = |m: usize| (planned(&compared(m)), strings(64 * m));
    let (small, large) = (at(n), at(scaling::FACTOR * n));
    scaling::check(
        "a tuple of 64n strings handed to the kernel n times",
        n,
        |m| {
            let ((g, p), w) = if m == n { &small } else { &large };
            let o = zed_native::run(g, p, &mut Evaluator::new(w.clone())).unwrap();
            std::hint::black_box(o);
        },
    );
}

/// A heap holding a shipping manifest the program built, `64n` lines in their own cells, and
/// its word.
fn manifest(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let lines: Vec<Word> = (0..64 * n)
        .map(|i| h.alloc(Obj::Str(format!("crate {i}").into())))
        .collect();
    let w = h.alloc(Obj::Tuple(lines.into()));
    (h, w)
}

/// A record whose cells the program built, not the kernel, keeps its value from its first read:
/// read whole each time, the `n` reads of `64n` cells would grow 64 times at `8n`. Each run
/// reads a manifest of its own, so the first read, which makes the value, is timed in each.
#[test]
fn a_record_the_program_built_read_many_times_scales() {
    let n = 10_000;
    let (small_runs, large_runs) = scaling::Meter::new().runs();
    let made = Mutex::new(
        [(n, small_runs), (scaling::FACTOR * n, large_runs)]
            .map(|(m, runs)| (m, (0..runs).map(|_| manifest(m)).collect::<Vec<_>>())),
    );
    let used = Mutex::new(Vec::new());
    scaling::check(
        "the value of a tuple of 64n strings, read n times",
        n,
        |m| {
            let (mut h, w) = {
                let mut made = made.lock().unwrap();
                let at = made.iter_mut().find(|(k, _)| *k == m).unwrap();
                at.1.pop().expect("a manifest for each run")
            };
            for _ in 0..m {
                std::hint::black_box(h.value(w).unwrap());
            }
            used.lock().unwrap().push(h);
        },
    );
}
