//! The oracle gives each binding the outcome a run of it alone gives (DESIGN.md step L1.37),
//! though it runs a unit's bindings together: checked against such runs on units built by
//! hand, where a let stops or a binding the checker types `_` is a function, so the bindings
//! cannot be run as one tuple.

use std::sync::Arc;

use zed_kernel::{Evaluator, Prim, Shared, Term, Value, World};
use zed_tests::oracle::{Engine, Report, bindings, native};
use zed_tests::scaling::{check, inputs};
use zedc::elab::{Cones, Def, Unit};
use zedc::interp;
use zedc::run;

/// The interpreter as an engine, so each outcome is compared and none differs.
fn same(t: &Term, ev: &mut Evaluator) -> Result<Value, String> {
    run::direct(t, ev)
}

/// An engine that gives no value, so each mismatch prints the interpreter's outcome.
fn refuse(_: &Term, _: &mut Evaluator) -> Result<Value, String> {
    Err("refused".into())
}

/// The interpreter, its error messages changed, so a mismatch shows which run stopped.
fn marked(t: &Term, ev: &mut Evaluator) -> Result<Value, String> {
    run::direct(t, ev).map_err(|e| format!("marked {e}"))
}

const ENGINES: &[Engine<'_>] = &[("same", &same), ("refuse", &refuse), ("marked", &marked)];

/// The report of the oracle before it ran the bindings together: each binding run alone,
/// closed over the definitions it reaches.
fn alone(u: &Unit, engines: &[Engine<'_>]) -> Report {
    let printed = |out: Result<Value, String>| match out {
        Ok(v) => format!("the value {v}"),
        Err(e) => format!("the error `{e}`"),
    };
    let mut r = Report::default();
    let cones = Cones::new(u);
    for d in u.defs.iter().filter(|d| d.first_order) {
        let t = interp::prelude(cones.close(Term::Var(d.kernel.clone())));
        let want = printed(run::direct(&t, &mut Evaluator::new(World::new())));
        for (name, engine) in engines {
            let got = printed(engine(&t, &mut Evaluator::new(World::new())));
            r.compared += 1;
            if want != got {
                r.mismatches.push(format!(
                    "binding `{}`: the interpreter gives {want}, and {name} gives {got}",
                    d.name
                ));
            }
        }
    }
    r
}

/// A definition named `name`, its kernel name the same.
fn def(name: &str, term: Term, first_order: bool) -> Def {
    Def {
        name: name.into(),
        kernel: Arc::from(name),
        term: Shared::new(term),
        first_order,
    }
}

fn var(name: &str) -> Term {
    Term::Var(Arc::from(name))
}

fn int(i: i64) -> Term {
    Term::Lit(Value::Int(i))
}

/// `a + b`.
fn add(a: Term, b: Term) -> Term {
    Term::Prim(Prim::Add, vec![a, b])
}

/// A let that stops: `p` applied to `true` and `1`, which the kernel refuses as it runs, its
/// error naming `p`, so that each stop of a unit has its own error.
fn stops(p: Prim) -> Term {
    Term::Prim(p, vec![Term::Lit(Value::Bool(true)), int(1)])
}

/// `(x) -> x`.
fn identity() -> Term {
    Term::Lam(vec![Arc::from("x")], Shared::new(var("x")))
}

fn unit(defs: Vec<Def>) -> Unit {
    Unit {
        defs,
        ..Unit::default()
    }
}

/// The unit with a binding that is a function, which the native code leaves live when a run
/// stops.
const FUNCTION: &str = "a binding that is a function";

/// The units the tests compare, each with its name.
fn units() -> Vec<(&'static str, Unit)> {
    vec![
        (
            // A chain with a stop in it: those after it that reach it stop with its error,
            // and those beside it keep their values.
            "a chain through a stop",
            unit(vec![
                def("a", int(1), true),
                def("b", add(var("a"), stops(Prim::Add)), true),
                def("c", add(var("b"), int(1)), true),
                def("d", add(var("a"), int(1)), true),
                def("e", add(var("c"), var("d")), true),
            ]),
        ),
        (
            // A definition with a function component that stops, reached by two bindings:
            // the second finds the stop already known.
            "a stop in a definition that is no binding",
            unit(vec![
                def("g", stops(Prim::Sub), false),
                def("h", add(var("g"), int(1)), true),
                def("i", add(var("g"), int(2)), true),
                def("j", int(3), true),
            ]),
        ),
        (
            // Two stops reached by one binding: its own run stops at the first.
            "two stops reached",
            unit(vec![
                def("p", stops(Prim::Mul), true),
                def("q", stops(Prim::Lt), true),
                def("r", add(var("q"), var("p")), true),
            ]),
        ),
        (
            // A stop not yet known before a known one: the earlier stops first.
            "an unknown stop before a known one",
            unit(vec![
                def("g", stops(Prim::Le), false),
                def("b", stops(Prim::Gt), true),
                def("c", add(var("b"), var("g")), true),
            ]),
        ),
        (
            // A binding the checker typed `_` that is a function: its run gives the
            // function and so an error, and those after it run it as a let; one puts it in
            // a tuple, which stops.
            FUNCTION,
            unit(vec![
                def("f", identity(), true),
                def("k", Term::App(Shared::new(var("f")), vec![int(7)]), true),
                def("m", Term::Prim(Prim::Tuple, vec![var("f")]), true),
                def("n", add(var("k"), int(1)), true),
            ]),
        ),
        (
            // A binding whose own let stops, reached after a function: the bisection finds
            // the binding itself.
            "a stop after a function",
            unit(vec![
                def("f", identity(), false),
                def(
                    "s",
                    add(
                        Term::App(Shared::new(var("f")), vec![int(8)]),
                        stops(Prim::Ge),
                    ),
                    true,
                ),
                def("t", add(var("s"), int(1)), true),
            ]),
        ),
        ("no definitions", unit(Vec::new())),
    ]
}

#[test]
fn each_binding_gives_what_its_run_alone_gives() {
    for (what, u) in units() {
        let (want, got) = (alone(&u, ENGINES), bindings(&u, ENGINES));
        assert_eq!(got.compared, want.compared, "{what}");
        assert_eq!(got.mismatches, want.mismatches, "{what}");
    }
}

#[test]
fn natively_too() {
    // A native run that stops leaves the cells it holds live (item NATIVE-stop-cells), and
    // `native` refuses that: the run of `FUNCTION`'s `m` alone, as the run of all its
    // bindings, stops holding the function.
    for (what, u) in units().into_iter().filter(|(what, _)| *what != FUNCTION) {
        let ((want, got), _) = native(|engines| (alone(&u, engines), bindings(&u, engines)));
        assert_eq!(got.compared, want.compared, "{what}");
        assert_eq!(got.mismatches, want.mismatches, "{what}");
    }
}

#[test]
fn the_outcomes_are_those_expected() {
    // What the interpreter gives each binding of the first unit, as the refusing engine's
    // mismatches print it: the stop of `b` reaches `c` and `e`, not `d`.
    let (_, u) = &units()[0];
    let r = bindings(u, &[("refuse", &refuse)]);
    let outcomes: Vec<&str> = r
        .mismatches
        .iter()
        .map(|m| {
            m.split_once(": the interpreter gives ")
                .and_then(|(_, rest)| rest.split_once(", and refuse"))
                .map_or(m.as_str(), |(o, _)| o)
        })
        .collect();
    assert_eq!(outcomes.len(), 5, "{:?}", r.mismatches);
    assert!(outcomes[0] == "the value 1", "{outcomes:?}");
    assert!(outcomes[1].starts_with("the error"), "{outcomes:?}");
    assert_eq!(outcomes[2], outcomes[1], "`c` stops with `b`'s error");
    assert_eq!(outcomes[3], "the value 2");
    assert_eq!(outcomes[4], outcomes[1], "`e` stops with `b`'s error");
}

/// `x0 = 0; x1 = x0 + 1; …` to `n` bindings, the last of which stops, so that the bindings
/// cannot run as one tuple.
fn stopped_chain(n: usize) -> Unit {
    let name = |i: usize| format!("x{i}");
    unit(
        (0..n)
            .map(|i| match i {
                _ if i + 1 == n => def(&name(i), add(var(&name(i - 1)), stops(Prim::Add)), true),
                0 => def(&name(0), int(0), true),
                _ => def(&name(i), add(var(&name(i - 1)), int(1)), true),
            })
            .collect(),
    )
}

#[test]
fn a_chain_that_stops_scales() {
    let units = inputs(500, stopped_chain);
    check("a chain of n bindings, the last stopping", 500, |k| {
        let r = bindings(&units[&k], &[("refuse", &refuse)]);
        assert_eq!(r.mismatches.len(), k);
        assert!(r.mismatches[k - 1].contains("the interpreter gives the error"));
    });
}

/// `n` functions, each `(x) -> if false { f(x) } else { x }` with `f` the one before, `n`
/// bindings each calling the last, and a binding that stops: each binding reaches every
/// function, though its run calls one.
fn shared_cone(n: usize) -> Unit {
    let name = |i: usize| format!("f{i}");
    let mut defs = vec![def(&name(0), identity(), false)];
    for i in 1..n {
        let call = Term::App(Shared::new(var(&name(i - 1))), vec![var("x")]);
        let body = Term::If(
            Shared::new(Term::Lit(Value::Bool(false))),
            Shared::new(call),
            Shared::new(var("x")),
        );
        defs.push(def(
            &name(i),
            Term::Lam(vec![Arc::from("x")], Shared::new(body)),
            false,
        ));
    }
    let last = name(n - 1);
    for j in 0..n {
        let call = Term::App(Shared::new(var(&last)), vec![int(j as i64)]);
        defs.push(def(&format!("b{j}"), call, true));
    }
    defs.push(def("s", stops(Prim::Add), true));
    unit(defs)
}

#[test]
fn bindings_that_share_a_cone_scale() {
    // Run one by one, the bindings would bind every function once each: n² in all.
    let u = shared_cone(3);
    assert_eq!(
        bindings(&u, ENGINES).mismatches,
        alone(&u, ENGINES).mismatches
    );
    let units = inputs(100, shared_cone);
    check("n bindings reaching n functions, and a stop", 100, |k| {
        let r = bindings(&units[&k], &[("refuse", &refuse)]);
        assert_eq!(r.mismatches.len(), k + 1);
        assert!(r.mismatches[k].contains("the interpreter gives the error"));
    });
}
