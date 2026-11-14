//! Strings against their length and the number of operations on them (COMPLEXITY.md R4, R5):
//! `len` in a loop, `++` in a loop with a read after each, and `++` of two long strings, each
//! natively and in the kernel, run in time linear in the number of operations whatever the
//! strings' lengths. Each string's length in characters is kept in its piece, so neither `len`
//! nor `++` counts it again, and a string handed to the kernel is shared, so no read copies it.
//!
//! The measurements at two sizes are in `bench/string_scaling.rs`; the test here is their small
//! instance: each program gives the kernel's value natively, with the calls to the kernel the
//! measurements count.

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};

use super::planned;

/// The characters of each input string for each operation; `ä` is two bytes in UTF-8.
pub(crate) const LONG: usize = 16384;

/// A world whose input ports `x` and `y` hold `ä` and `ö` repeated `LONG * n` times.
pub(crate) fn long(n: usize) -> World {
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
pub(crate) fn lens(n: usize) -> Term {
    called(n, prim(Prim::Len, vec![var("s")]))
}

/// A header and a body joined `n` times, once per copy of a message sent out.
pub(crate) fn cats(n: usize) -> Term {
    called(n, prim(Prim::Concat, vec![var("s"), var("t")]))
}

/// The characters of each line of a report; `ü` is two bytes in UTF-8.
pub(crate) const LINE: usize = 32768;

/// A report built line by line, `n` lines of `LINE` characters, with `read` after each line,
/// and the reads and the report made a tuple: `s1 = s0 ++ line; r1 = read(s1); s2 = s1 ++
/// line; …`. When `chained`, the next line is appended to the read, `s2 = r1 ++ line`, so the
/// read's result is the string the next step builds on.
pub(crate) fn appends(n: usize, read: Prim, chained: bool) -> Term {
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

/// The small instances of `bench::string_scaling`: three of each operation give the kernel's
/// value natively, with no call to the kernel but one per `show`.
#[test]
fn string_loops_give_the_kernels_value_natively() {
    let short = || {
        let mut w = World::new();
        w.inputs.insert("x".into(), Value::str("äb"));
        w.inputs.insert("y".into(), Value::str("ö"));
        w
    };
    let programs = [
        (lens(3), short(), 0),
        (cats(3), short(), 0),
        (appends(3, Prim::Len, false), World::new(), 0),
        (appends(3, Prim::Show, true), World::new(), 3),
    ];
    for (t, w, calls) in programs {
        let (g, p) = planned(&t);
        let o = zed_native::run(&g, &p, &mut Evaluator::new(w.clone())).unwrap();
        assert_eq!(o.kernel_calls, calls, "{t}");
        assert_eq!(o.value, Evaluator::new(w).run(&t).unwrap(), "{t}");
    }
}
