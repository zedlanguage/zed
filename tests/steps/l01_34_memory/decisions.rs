//! A decision that is a failure value, and a read of a port, under the machine: an `if` whose
//! condition is an atom gives the atom and drops the inputs it owns (DESIGN.md sec:failure: a
//! loose atom bubbles out); a `match` no arm of which matches stops as the kernel stops; a
//! port's value is a fresh cell, counted like any other, and a port the run was not given is
//! the kernel's error. In each case the machine gives the kernel's outcome and frees every
//! cell it made.

use zed_kernel::Shared;
use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Evaluator, Pattern, Prim, Term, Value, World};
use zedc::zir::memory;

use super::{cat, planned};

/// A world with the input port `inp` holding "hello".
fn with_input() -> World {
    let mut w = World::new();
    w.inputs.insert("inp".into(), Value::str("hello"));
    w
}

/// `match t { (x, _) -> x }`.
fn first(t: Term) -> Term {
    let p = Pattern::Tuple(vec![Pattern::Bind("x".into()), Pattern::Wild]);
    Term::Match(Shared::new(t), vec![(p, var("x"))])
}

#[test]
fn the_machine_gives_the_kernels_outcome_on_failures_and_ports() {
    let nope = || lit(Value::atom("nope"));
    let read = || Term::Read("inp".into());
    let cases: Vec<(&str, Term, fn() -> World, Result<&str, &str>)> = vec![
        (
            "an `if` on an atom, an arm borrowing a string",
            let_(
                "s",
                cat("a", "b"),
                if_(nope(), prim(Prim::Len, vec![var("s")]), lit(0)),
            ),
            World::new,
            Ok("#nope"),
        ),
        (
            "an `if` on an atom, an arm owning a string",
            let_(
                "s",
                cat("a", "b"),
                if_(nope(), prim(Prim::Tuple, vec![var("s"), lit(1)]), lit(0)),
            ),
            World::new,
            Ok("#nope"),
        ),
        (
            "a `match` of an int no arm matches",
            first(lit(3)),
            World::new,
            Err("no arm matches a value of type `int`"),
        ),
        (
            "a `match` of a fresh string no arm matches",
            first(cat("a", "b")),
            World::new,
            Err("no arm matches a value of type `String`"),
        ),
        (
            "a `match` of an atom no arm matches",
            first(nope()),
            World::new,
            Err("no arm matches a value of type `#nope`"),
        ),
        (
            "a port read once",
            prim(Prim::Upper, vec![read()]),
            with_input,
            Ok(r#""HELLO""#),
        ),
        (
            "a port read and used twice",
            let_("s", read(), prim(Prim::Tuple, vec![var("s"), var("s")])),
            with_input,
            Ok(r#"("hello", "hello")"#),
        ),
        (
            "a port the run was not given",
            read(),
            World::new,
            Err(
                "the program uses the port `inp`, and the run was given no port of that name. \
                 To repair it, declare `inp` as a port of `main`, or remove the use",
            ),
        ),
    ];
    for (case, t, world, want) in cases {
        let kernel = Evaluator::new(world())
            .run(&t)
            .map(|v| v.to_string())
            .map_err(|e| e.to_string());
        for fuse in [true, false] {
            let (g, p) = planned(&t, fuse);
            let got = memory::run(&g, &p, &mut Evaluator::new(world())).map(|(v, s)| {
                assert_eq!(s.allocations, s.frees, "{case}, fused {fuse}: a cell left");
                v.to_string()
            });
            assert_eq!(got, kernel, "{case}, fused {fuse}: the kernel's outcome");
            match (&got, want) {
                (Ok(v), Ok(w)) => assert_eq!(v, w, "{case}"),
                (Err(e), Err(w)) => assert!(e.contains(w), "{case}: {e}"),
                _ => panic!("{case}: {got:?}, expected {want:?}"),
            }
        }
    }
}
