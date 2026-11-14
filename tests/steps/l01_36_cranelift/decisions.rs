//! A decision that is a failure value, a `match` no arm of which matches, and a read of a port,
//! in native code: each gives the kernel's outcome (DESIGN.md sec:failure: a loose atom bubbles
//! out of an `if`; a `match` with no matching arm stops), and a run that gives a value frees
//! every cell it made, which the run itself checks at its end.

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Pattern, Prim, Shared, Term, Value, World};

use super::planned;

/// `"a" ++ "b"`-style concatenation: a fresh string cell.
fn cat(a: &str, b: &str) -> Term {
    prim(Prim::Concat, vec![lit(a), lit(b)])
}

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

/// `#point(x: "a" ++ "b", y: 3)`, a struct value, its payload sorted by field name.
fn point() -> Term {
    let names = Value::tuple(vec![Value::str("x"), Value::str("y")]);
    prim(
        Prim::Atom,
        vec![lit("point"), lit(names), cat("a", "b"), lit(3)],
    )
}

/// A case: what it is, the term, the world it runs in, and the outcome expected (the value
/// shown, or text the error contains).
type Case = (
    &'static str,
    Term,
    fn() -> World,
    Result<&'static str, &'static str>,
);

#[test]
fn native_code_gives_the_kernels_outcome_on_failures_ports_and_unmatched_values() {
    let nope = || lit(Value::atom("nope"));
    let read = || Term::Read("inp".into());
    let fields = |name: &str, field: &str| {
        Pattern::Fields(name.into(), vec![(field.into(), Pattern::Bind("v".into()))])
    };
    let cases: Vec<Case> = vec![
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
            "an `if` on a computed atom inside a lambda body",
            let_(
                "f",
                lam(&["c"], if_(var("c"), lit(1), lit(2))),
                app(var("f"), vec![nope()]),
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
            "a struct matched by its field",
            Term::Match(Shared::new(point()), vec![(fields("point", "x"), var("v"))]),
            World::new,
            Ok(r#""ab""#),
        ),
        (
            "a struct no field pattern of which matches",
            Term::Match(Shared::new(point()), vec![(fields("other", "x"), var("v"))]),
            World::new,
            Err("no arm matches"),
        ),
        (
            "a function matched by a binder, then called",
            Term::Match(
                Shared::new(lam(&["x"], prim(Prim::Add, vec![var("x"), lit(1)]))),
                vec![(Pattern::Bind("g".into()), app(var("g"), vec![lit(2)]))],
            ),
            World::new,
            Ok("3"),
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
        let (g, p) = planned(&t);
        let got = zed_native::run(&g, &p, &mut Evaluator::new(world())).map(|o| {
            assert_eq!(o.stats.allocations, o.stats.frees, "{case}: a cell left");
            o.value.to_string()
        });
        assert_eq!(got, kernel, "{case}: the kernel's outcome");
        match (&got, want) {
            (Ok(v), Ok(w)) => assert_eq!(v, w, "{case}"),
            (Err(e), Err(w)) => assert!(e.contains(w), "{case}: {e}"),
            _ => panic!("{case}: {got:?}, expected {want:?}"),
        }
    }
}
