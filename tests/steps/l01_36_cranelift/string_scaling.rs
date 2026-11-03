//! Strings against their length and the number of operations on them (COMPLEXITY.md R4, R5):
//! `len` in a loop, `++` in a loop with a read after each, and `++` of two long strings, each
//! natively and in the kernel, run in time linear in the number of operations whatever the
//! strings' lengths. Each string's length in characters is kept in its piece, so neither `len`
//! nor `++` counts it again, and a string handed to the kernel is shared, so no read copies it.
//!
//! A native run includes compiling its program, about a million instructions for each call
//! site, against well under one instruction per byte for a scan or a copy. So the strings are
//! long, `LONG` characters for each operation and lines of `LINE`, that a scan or a copy of a
//! whole string per operation would outweigh the compiling.

use std::sync::Arc;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_tests::scaling;
use zedc::zir::Region;
use zedc::zir::memory::Plan;

use super::planned;

/// The characters of each input string for each operation; `ä` is two bytes in UTF-8.
const LONG: usize = 16384;

/// A world whose input ports `x` and `y` hold `ä` and `ö` repeated `LONG * n` times.
fn long(n: usize) -> World {
    let mut w = World::new();
    w.inputs
        .insert("x".into(), Value::str(&"ä".repeat(LONG * n)));
    w.inputs
        .insert("y".into(), Value::str(&"ö".repeat(LONG * n)));
    w
}

/// `s = read x; f = (i) -> body; (f(0), …, f(n-1))`: `body` run `n` times on one string.
fn called(n: usize, body: Term) -> Term {
    let calls = (0..n).map(|i| app(var("f"), vec![lit(i as i64)])).collect();
    let_(
        "s",
        Term::Read("x".into()),
        let_(
            "t",
            Term::Read("y".into()),
            let_("f", lam(&["i"], body), prim(Prim::Tuple, calls)),
        ),
    )
}

/// The length of a document read `n` times, once per page it is cut into.
fn lens(n: usize) -> Term {
    called(n, prim(Prim::Len, vec![var("s")]))
}

/// A header and a body joined `n` times, once per copy of a message sent out.
fn cats(n: usize) -> Term {
    called(n, prim(Prim::Concat, vec![var("s"), var("t")]))
}

/// The characters of each line of a report; `ü` is two bytes in UTF-8.
const LINE: usize = 32768;

/// A report built line by line, `n` lines of `LINE` characters, with `read` after each line,
/// and the reads and the report made a tuple: `s1 = s0 ++ line; r1 = read(s1); s2 = s1 ++
/// line; …`. When `chained`, the next line is appended to the read, `s2 = r1 ++ line`, so the
/// read's result is the string the next step builds on.
fn appends(n: usize, read: Prim, chained: bool) -> Term {
    let line = "ü".repeat(LINE - 1) + "\n";
    let last = if chained { 'r' } else { 's' };
    let mut body = prim(
        Prim::Tuple,
        (1..=n).map(|i| var(&format!("r{i}"))).collect(),
    );
    body = prim(Prim::Tuple, vec![body, var(&format!("s{n}"))]);
    for i in (1..=n).rev() {
        let s = format!("s{i}");
        let before = if i == 1 {
            "s0".into()
        } else {
            format!("{last}{}", i - 1)
        };
        body = let_(
            &s,
            prim(Prim::Concat, vec![var(&before), lit(line.as_str())]),
            let_(&format!("r{i}"), prim(read, vec![var(&s)]), body),
        );
    }
    let_("s0", lit("report\n"), body)
}

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
type Made = [(usize, Term, (Arc<Region>, Plan), World); 2];

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
        100,
        lens,
        long,
        0,
    );
}

#[test]
fn len_in_a_loop_scales_in_the_kernel() {
    kernel(
        "len of one long string, n times, in the kernel",
        100,
        lens,
        long,
    );
}

#[test]
fn concatenating_two_long_strings_scales_natively() {
    native(
        "two long strings joined n times, natively",
        100,
        cats,
        long,
        0,
    );
}

#[test]
fn concatenating_two_long_strings_scales_in_the_kernel() {
    kernel(
        "two long strings joined n times, in the kernel",
        100,
        cats,
        long,
    );
}

#[test]
fn appending_then_len_scales_natively() {
    native(
        "n lines appended, len after each, natively",
        60,
        |n| appends(n, Prim::Len, false),
        |_| World::new(),
        0,
    );
}

#[test]
fn appending_then_len_scales_in_the_kernel() {
    kernel(
        "n lines appended, len after each, in the kernel",
        60,
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
        60,
        |n| appends(n, Prim::Show, true),
        |_| World::new(),
        1,
    );
}
