//! Strings against their length and the number of operations on them (COMPLEXITY.md R4, R5):
//! `len` in a loop, `++` in a loop with a read after each, and `++` of two long strings, each
//! natively and in the kernel, run in time linear in the number of operations whatever the
//! strings' lengths. The small instance is in `string_scaling.rs`.
//!
//! A native run includes compiling its program, about a million instructions for each call
//! site, against well under one instruction per byte for a scan or a copy. So the strings are
//! long, `LONG` characters for each operation and lines of `LINE`, that a scan or a copy of a
//! whole string per operation would outweigh the compiling.

use zed_kernel::{Evaluator, Prim, Term, World};
use zed_tests::scaling;
use zedc::zir::legalize::Legalized;
use zedc::zir::memory::Plan;

use crate::planned;
use crate::string_scaling::{appends, cats, lens, long};

/// `f`, run on a thread whose stack holds the recursive passes over a term thousands of `let`s
/// deep: lowering, planning and the drop of a graph.
fn on_big_stack(f: impl FnOnce() + Send) {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn_scoped(s, f)
            .unwrap()
            .join()
            .unwrap()
    })
}

/// The program and world of each size, made before the timing.
type Made = [(usize, Term, (Legalized, Plan), World); 2];

fn made(n: usize, make: impl Fn(usize) -> Term, world: impl Fn(usize) -> World) -> Made {
    [n, scaling::FACTOR * n].map(|m| {
        let t = make(m);
        let p = planned(&t);
        (m, t, p, world(m))
    })
}

/// The native run of `make` in `world` at `n` and `8n`, with no call to the kernel unless
/// `kernel_calls` per operation.
fn native(what: &str, n: usize, make: fn(usize) -> Term, world: fn(usize) -> World, calls: u64) {
    on_big_stack(|| {
        let made = made(n, make, world);
        scaling::check(what, n, |m| {
            let (_, _, (g, p), w) = made.iter().find(|x| x.0 == m).unwrap();
            let o = zed_native::run(g, p, &mut Evaluator::new(w.clone())).unwrap();
            assert_eq!(o.kernel_calls, calls * m as u64, "{what}");
            std::hint::black_box(o);
        });
    });
}

/// The kernel's run of `make` in `world` at `n` and `8n`.
fn kernel(what: &str, n: usize, make: fn(usize) -> Term, world: fn(usize) -> World) {
    on_big_stack(|| {
        let made = made(n, make, world);
        scaling::check(what, n, |m| {
            let (_, t, _, w) = made.iter().find(|x| x.0 == m).unwrap();
            std::hint::black_box(Evaluator::new(w.clone()).run(t).unwrap());
        });
    });
}

#[test]
fn len_in_a_loop_scales_natively() {
    native(
        "len of one long string, n times, natively",
        1_400,
        lens,
        long,
        0,
    );
}

#[test]
fn len_in_a_loop_scales_in_the_kernel() {
    kernel(
        "len of one long string, n times, in the kernel",
        2_000,
        lens,
        long,
    );
}

#[test]
fn concatenating_two_long_strings_scales_natively() {
    native(
        "two long strings joined n times, natively",
        1_400,
        cats,
        long,
        0,
    );
}

#[test]
fn concatenating_two_long_strings_scales_in_the_kernel() {
    kernel(
        "two long strings joined n times, in the kernel",
        2_000,
        cats,
        long,
    );
}

#[test]
fn appending_then_len_scales_natively() {
    native(
        "n lines appended, len after each, natively",
        1_500,
        |n| appends(n, Prim::Len, false),
        |_| World::new(),
        0,
    );
}

#[test]
fn appending_then_len_scales_in_the_kernel() {
    kernel(
        "n lines appended, len after each, in the kernel",
        1_500,
        |n| appends(n, Prim::Len, false),
        |_| World::new(),
    );
}

/// `show` of a string runs in the kernel, so each line's report crosses to the kernel and back,
/// and the next line is appended to what comes back.
#[test]
fn appending_then_a_kernel_read_scales_natively() {
    native(
        "n lines appended, show after each, natively",
        1_500,
        |n| appends(n, Prim::Show, true),
        |_| World::new(),
        1,
    );
}
