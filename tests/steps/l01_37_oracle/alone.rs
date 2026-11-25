//! The oracle gives each binding the outcome a run of it alone gives (DESIGN.md step L1.37),
//! though it runs a unit's bindings together: checked against such runs on units built by
//! hand, where a let stops or a binding the checker types `_` is a function, so the bindings
//! cannot be run as one tuple.

use std::sync::Arc;

use zed_kernel::{Evaluator, Prim, Shared, Term, Value, World};
use zed_tests::oracle::{Engine, Report, bindings, native};
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
    // Every unit, `FUNCTION` included: its run of `m` stops holding the function in a tuple,
    // and `native` checks that the stopped run leaves no cell live (item NATIVE-stop-cells,
    // which left that unit out; it passes on main at 7b58d316e).
    for (what, u) in units() {
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
pub(super) fn stopped_chain(n: usize) -> Unit {
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

/// Compares the `n` bindings of [`stopped_chain`] with an engine that refuses: each differs,
/// and the last stops with the interpreter's error.
pub(super) fn the_last_stops(u: &Unit, n: usize) {
    let r = bindings(u, &[("refuse", &refuse)]);
    assert_eq!(r.mismatches.len(), n);
    assert!(r.mismatches[n - 1].contains("the interpreter gives the error"));
}

#[test]
fn a_chain_whose_last_binding_stops_is_compared() {
    the_last_stops(&stopped_chain(3), 3);
}

/// The search for the first stop binds O(n) lets in all, not O(n log n): each run is counted
/// by the lets of the term an engine is given. Before BENCH-over-nlogn-prediction each halving
/// ran the whole prefix again, about `log2` of the stretch after the last prefix that ran
/// times the prefix: 60,509 lets at 4,096 definitions (14.8 a definition), where the walk now
/// binds 20,042 (4.9) and 75,600 at 16,384 (4.6), measured 2026-11-20. A let is O(log n) in the
/// environment (COMPLEXITY.md K8), so the walk was O(n log^2 n), 10.24 times the instructions
/// at 8 times 20,000 definitions (bench `a_chain_that_stops_scales`).
#[test]
fn the_search_for_the_stop_binds_each_definition_a_bounded_number_of_times() {
    fn lets(mut t: &Term) -> usize {
        let mut count = 0;
        while let Term::Let(_, _, body) = t {
            count += 1;
            t = body;
        }
        count
    }
    for n in [4096, 16_384] {
        let bound = std::cell::Cell::new(0);
        let counting = |t: &Term, ev: &mut Evaluator| {
            bound.set(bound.get() + lets(t));
            run::direct(t, ev)
        };
        let r = bindings(&stopped_chain(n), &[("counting", &counting)]);
        assert!(r.mismatches.is_empty(), "{:?}", &r.mismatches[..1]);
        assert!(
            bound.get() <= 6 * n,
            "{} lets for {n} definitions",
            bound.get()
        );
    }
}

/// The walk over [`stops_reaching_functions`] binds the `n` functions a bounded number of
/// times. A function has no literal, and every run of the search for the first stop
/// (`first_stop` in `zed_tests::oracle`) reaches the last function, which reaches every other.
/// The search halved its window, about `log2 n` probes, so `n log n` lets, each `O(log n)` in
/// the kernel's environment (COMPLEXITY.md K8): `n log² n` work (plan row
/// SCALE-near-oracle-stops; 23.15 lets a function at 512, measured on b24-scale1 with
/// the halving put back). Now the stop is located by one run of the interpreter, which is not
/// counted here, and confirmed by the engine. For `n` a power of 2, the engine's runs, counted
/// here, bind exactly `9n + 2p + 6 + 44 (log2 p + 8)` lets, for `p = 2n` the least power of 2
/// at least `n + 2`, the position past `b0`, and 44 the lets of the prelude
/// (`interp::prelude`), which each of the `log2 p + 8` runs binds (for another `n`, the last
/// prefix that runs may hold `c0`, and step 3 then runs `c0` once less):
/// 1. the tuple of all the bindings, the `3n` definitions;
/// 2. the doubling prefixes `1, 2, 4, …, p`, the first to hold `b0`, `2p − 1` in all
///    (`Runs::outcomes`), the definitions they reach lying inside them;
/// 3. in `first_stop`, the run of `c0` that confirms it runs, the run of its value, and the
///    run of `b0` that confirms it stops, each `n + 1` with the `n` functions `c0` and `b0`
///    reach;
/// 4. after `b0`, the prefix `c1` (`n + 1`), the prefix `c1, b1` (`n + 2`), which binds again
///    the functions and stops, and so ends the walk (`End::Again`), and the run of `c1`'s
///    value (`n + 1`).
///
/// At 512 that is 7,454 lets, 14.56 a function, and at 4,096 54,178, 13.23 a function: the
/// `9n` and the prefixes' `4n − 1` are 13 lets a function, and the prelude adds `O(log n)` in
/// all.
#[test]
fn the_search_for_a_stop_through_functions_binds_them_once_a_probe() {
    fn lets(mut t: &Term) -> usize {
        let mut count = 0;
        while let Term::Let(_, _, body) = t {
            count += 1;
            t = body;
        }
        count
    }
    for (n, want) in [(2usize, 472), (512, 7_454), (4096, 54_178)] {
        let p = (n + 2).next_power_of_two();
        assert_eq!(want, 9 * n + 2 * p + 6 + 44 * (p.ilog2() as usize + 8));
        let bound = std::cell::Cell::new(0);
        let counting = |t: &Term, ev: &mut Evaluator| {
            bound.set(bound.get() + lets(t));
            marked(t, ev)
        };
        let r = bindings(&stops_reaching_functions(n), &[("counting", &counting)]);
        assert_eq!(r.mismatches.len(), 1, "{:?}", r.mismatches);
        assert_eq!(bound.get(), want, "lets at n = {n}");
    }
}

/// `n` functions, each `(x) -> if false { f(x) } else { x }` with `f` the one before, `n`
/// bindings each calling the last, and a binding that stops: each binding reaches every
/// function, though its run calls one.
pub(super) fn shared_cone(n: usize) -> Unit {
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

/// Compares the `n + 1` bindings of [`shared_cone`] at `n` with an engine that refuses: each
/// differs, and the last, `s`, stops with the interpreter's error.
pub(super) fn the_cone_is_compared(u: &Unit, n: usize) {
    let r = bindings(u, &[("refuse", &refuse)]);
    assert_eq!(r.mismatches.len(), n + 1);
    assert!(r.mismatches[n].contains("the interpreter gives the error"));
}

#[test]
fn bindings_that_share_a_cone_are_compared() {
    // Run one by one, the bindings would bind every function once each: n² in all.
    let u = shared_cone(3);
    assert_eq!(
        bindings(&u, ENGINES).mismatches,
        alone(&u, ENGINES).mismatches
    );
    the_cone_is_compared(&u, 3);
}

/// `n` functions as in [`shared_cone`], then `n` pairs of bindings, `c_j = f(j)` and
/// `b_j = f(j) + (true + 1)` with `f` the last function: `n` stops, each reaching every
/// function.
pub(super) fn stops_reaching_functions(n: usize) -> Unit {
    let mut u = shared_cone(n);
    u.defs.truncate(n);
    let last = Shared::new(var(&format!("f{}", n - 1)));
    for j in 0..n {
        let call = Term::App(last.clone(), vec![int(j as i64)]);
        u.defs.push(def(&format!("c{j}"), call.clone(), true));
        u.defs
            .push(def(&format!("b{j}"), add(call, stops(Prim::Add)), true));
    }
    u
}

/// Why the bindings of [`stops_reaching_functions`] from `b1` on have no outcome.
const AFTER_B0: &str = "no outcome, as the run of the definitions from `b1` on, after the \
                        stop at `b0`, binds again definitions with a function component, and \
                        stops";

/// Compares the bindings of [`stops_reaching_functions`] at `n` with [`marked`]. Run to each
/// stop, the bindings would bind every function once per stop: n² in all. The walk ends at the
/// second stop, so `b0`, whose error differs, is the one mismatch, `c0` and `c1` are compared,
/// and the 2n − 3 bindings from `b1` on are not.
pub(super) fn the_walk_ends_at_the_second_stop(u: &Unit, n: usize) {
    let r = bindings(u, &[("marked", &marked)]);
    assert_eq!(r.mismatches.len(), 1, "{:?}", r.mismatches);
    assert_eq!(r.compared, 3);
    assert_eq!(r.not_compared.len(), 2 * n - 3);
}

#[test]
fn stops_that_reach_functions_end_the_walk_at_the_second() {
    the_walk_ends_at_the_second_stop(&stops_reaching_functions(3), 3);
}

#[test]
fn a_second_stop_through_functions_is_not_compared() {
    // The unit of the test above at 3, and `z`, which reads `b0` and so stops with its error
    // though it comes after the end of the walk, and `y`, which reads only a function.
    let mut u = stops_reaching_functions(3);
    u.defs.push(def("z", add(var("b0"), int(1)), true));
    u.defs.push(def("y", var("f0"), false));
    let error = format!(
        "the error `{}`",
        zed_kernel::KernelError::Type("`+` applied to `bool`, `int`".into())
    );
    let r = bindings(&u, &[("refuse", &refuse)]);
    let expected = |b: &str, want: &str| {
        format!("binding `{b}`: the interpreter gives {want}, and refuse gives the error `refused`")
    };
    assert_eq!(
        r.mismatches,
        vec![
            expected("c0", "the value 0"),
            expected("b0", &error),
            expected("c1", "the value 1"),
            expected("b1", AFTER_B0),
            expected("c2", AFTER_B0),
            expected("b2", AFTER_B0),
            expected("z", &error),
        ]
    );
    let not = |b: &str| format!("binding `{b}`: not compared, as {}", &AFTER_B0[15..]);
    assert_eq!(r.not_compared, vec![not("b1"), not("c2"), not("b2")]);
    // An engine that gives what the interpreter gives leaves the same bindings with no
    // outcome, and so differs nowhere. Not natively: a native run that stops leaves the
    // closures it holds live (item NATIVE-stop-cells), and `native` refuses that.
    let r = bindings(&u, &[("same", &same)]);
    assert!(r.mismatches.is_empty(), "{:?}", r.mismatches);
    assert_eq!((r.compared, r.not_compared.len()), (4, 3));
}

/// `n` bindings `x0`, …, where `x{k}` stops and the others are `i`; in a chain each binding
/// after `x0` reads the one before, so those after the stop stop with its error, and among
/// independent bindings none reads another, so those after it run.
fn one_stop(n: usize, k: usize, chain: bool) -> Unit {
    let name = |i: usize| format!("x{i}");
    unit(
        (0..n)
            .map(|i| {
                let own = if i == k {
                    stops(Prim::Add)
                } else {
                    int(i as i64)
                };
                let term = if chain && i > 0 {
                    add(var(&name(i - 1)), own)
                } else {
                    own
                };
                def(&name(i), term, true)
            })
            .collect(),
    )
}

#[test]
fn a_stop_at_each_place_gives_each_binding_what_its_run_alone_gives() {
    // Each place of the stop, in chains and among independent bindings of 1 to 6, takes the
    // prefixes of 1, 2, 4, … definitions and the halvings between them each way they go.
    for n in 1..=6 {
        for k in 0..n {
            for chain in [true, false] {
                let u = one_stop(n, k, chain);
                let what = format!("{n} bindings, the stop at {k}, chained: {chain}");
                let (want, got) = (alone(&u, ENGINES), bindings(&u, ENGINES));
                assert_eq!(got.compared, want.compared, "{what}");
                assert_eq!(got.mismatches, want.mismatches, "{what}");
                assert_eq!(got.not_compared, Vec::<String>::new(), "{what}");
                // `refuse` differs on every binding, and `marked` on each that stops: the
                // stop and, in a chain, each binding after it.
                let stopped = if chain { n - k } else { 1 };
                assert_eq!(
                    got.mismatches.len(),
                    n + stopped,
                    "{what}: {:?}",
                    got.mismatches
                );
                let ((want, got), _) =
                    native(|engines| (alone(&u, engines), bindings(&u, engines)));
                assert_eq!(got.compared, want.compared, "{what}, natively");
                assert_eq!(got.mismatches, want.mismatches, "{what}, natively");
            }
        }
    }
}
