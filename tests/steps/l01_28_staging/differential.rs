//! Mixing a term whose parts are shared gives what mixing its tree form gives (ledger
//! STAGE-dag, verify 6). `mix` mixes a part held in one `Shared` node once for each map of the
//! names it reads to their bindings and for each set of answers its calls of functions bound
//! outside it took; these cases put one node under bindings that differ in what the build knows
//! of them: a literal on one path and another or a parameter on the other, functions that
//! differ or agree on the arguments the part calls them at, a function bound outside the part
//! that reads another which differs, a name the part rebinds, a part under a lambda or a match
//! arm that binds a name it reads, and a part left to run. Each case is mixed as built and as
//! its tree form, every node copied once for each place it is reached from, and the two mixed
//! terms must print alike; the residual program must also give what the program gives.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::term::build::{lam, lit, var};
use zed_kernel::{Evaluator, F64, Pattern, Prim, Shared, Term, Value, World};
use zedc::elab::{Def, Unit};
use zedc::interp;
use zedc::stage::{self, Report};

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

fn add(a: Term, b: Term) -> Term {
    prim(Prim::Add, vec![a, b])
}

fn call(f: &str, args: Vec<Term>) -> Term {
    Term::App(Shared::new(var(f)), args)
}

fn let_(x: &str, e: Term, body: Shared) -> Term {
    Term::Let(x.into(), Shared::new(e), body)
}

fn if_(c: Term, a: Shared, b: Shared) -> Term {
    Term::If(Shared::new(c), a, b)
}

/// `t` as a tree: each node copied once for each place it is reached from, so no two places
/// share one. Only for the small terms of these cases.
fn tree(t: &Term) -> Term {
    let s = |s: &Shared| Shared::new(tree(s));
    let all = |ts: &[Term]| ts.iter().map(tree).collect();
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => t.clone(),
        Term::Lam(ps, b) => Term::Lam(ps.clone(), s(b)),
        Term::App(g, args) => Term::App(s(g), all(args)),
        Term::Prim(p, args) => Term::Prim(*p, all(args)),
        Term::Let(x, e, b) => Term::Let(x.clone(), s(e), s(b)),
        Term::If(c, a, b) => Term::If(s(c), s(a), s(b)),
        Term::Match(m, arms) => Term::Match(
            s(m),
            arms.iter().map(|(p, a)| (p.clone(), tree(a))).collect(),
        ),
        Term::Push(port, v) => Term::Push(port.clone(), s(v)),
        other => panic!("not in these cases: {other}"),
    }
}

fn unit(defs: Vec<(&str, Term)>) -> Unit {
    let defs = defs
        .into_iter()
        .map(|(name, term)| Def {
            name: name.into(),
            kernel: name.into(),
            term: Shared::new(term),
            first_order: false,
        })
        .collect();
    Unit {
        defs,
        tests: Arc::from([]),
        warnings: Vec::new(),
        int_params: Default::default(),
        limits: Default::default(),
    }
}

/// `main = (c) -> body` after the definitions `before`.
fn program(before: Vec<(&str, Term)>, body: Term) -> Unit {
    let mut defs = before;
    defs.push(("main", Term::Lam(vec!["c".into()], Shared::new(body))));
    unit(defs)
}

/// The value of `main(c)` in `u`, its definitions bound by `let`s; `None` when it fails or
/// runs out of steps.
fn run(u: &Unit, c: &Value) -> Option<Value> {
    let main = Term::App(Shared::new(var("main")), vec![Term::Lit(c.clone())]);
    let t = u.defs.iter().rev().fold(main, |body, d| {
        Term::Let(d.kernel.clone(), d.term.clone(), Shared::new(body))
    });
    let t = interp::prelude(t);
    Evaluator::new(World::new()).with_fuel(100_000).run(&t).ok()
}

/// What a report says, each entry once: the definitions built, those nothing read, and the
/// terms left to run, printed in their tree form (the text of a shared term names its parts),
/// with why. The tree form lists a part once per place, the graph once per map of the names
/// it reads, so the lists are compared as sets.
fn said(r: &Report) -> (Vec<String>, BTreeSet<String>, BTreeSet<(String, String)>) {
    let left = r
        .left
        .iter()
        .map(|(t, why)| (tree(t).to_string(), why.clone()));
    (
        r.built.clone(),
        r.unread.iter().cloned().collect(),
        left.collect(),
    )
}

/// Mixes `u` as built and as its tree form and checks that the two agree, and that the residual
/// program gives what `u` gives at each value of `c` in `inputs`. Returns the mixed `main`.
fn agree(name: &str, u: &Unit, inputs: &[Value]) -> String {
    let t = Unit {
        defs: u
            .defs
            .iter()
            .map(|d| Def {
                term: Shared::new(tree(&d.term)),
                ..d.clone()
            })
            .collect(),
        ..u.clone()
    };
    for (a, b) in u.defs.iter().zip(&t.defs) {
        assert_eq!(a.term, b.term, "{name}: the tree form is the same term");
    }
    let (mixed, report) = stage::mix(u, &["main"]);
    let (mixed_tree, report_tree) = stage::mix(&t, &["main"]);
    let main = |u: &Unit| {
        let d = u.defs.iter().find(|d| d.name == "main").expect("`main`");
        d.term.clone()
    };
    assert_eq!(
        main(&mixed),
        main(&mixed_tree),
        "{name}: graph and tree mix alike"
    );
    let out = main(&mixed).to_string();
    assert_eq!(said(&report), said(&report_tree), "{name}: the reports");
    for c in inputs {
        let want = run(u, c);
        assert!(want.is_some(), "{name}: the program runs at {c:?}");
        assert_eq!(
            run(&mixed, c),
            want,
            "{name}: the residual program at {c:?}"
        );
    }
    out
}

fn bools() -> [Value; 2] {
    [Value::Bool(true), Value::Bool(false)]
}

/// `if c { t } else { other }`: a part that reads the parameter `c`, so the build mixes it
/// rather than evaluating the term around it, and keys it in its memo.
fn reads_c(t: Term, other: Term) -> Shared {
    Shared::new(if_(var("c"), Shared::new(t), Shared::new(other)))
}

fn float(x: f64) -> Term {
    Term::Lit(Value::Float(F64::new(x)))
}

#[test]
fn a_part_shared_under_two_literals_mixes_to_each_ones_result() {
    // `if c { let x = 1; p } else { let x = 2; p }` with `p` deciding `x >= 2`, which the build
    // decides a different way on each path.
    let x10 = Shared::new(add(var("x"), lit(10i64)));
    let decide = if_(
        prim(Prim::Ge, vec![var("x"), lit(2i64)]),
        x10,
        Shared::new(var("x")),
    );
    let p = reads_c(decide, lit(0i64));
    let body = if_(
        var("c"),
        Shared::new(let_("x", lit(1i64), p.clone())),
        Shared::new(let_("x", lit(2i64), p.clone())),
    );
    let out = agree("two literals", &program(vec![], body), &bools());
    assert!(out.contains("if c { 1 } else { 0 }"), "{out}");
    assert!(out.contains("if c { 12 } else { 0 }"), "{out}");
    // One literal on both paths: the part mixed once, under each path's own `let`.
    let same = if_(
        var("c"),
        Shared::new(let_("x", lit(3i64), p.clone())),
        Shared::new(let_("x", lit(3i64), p)),
    );
    let out = agree("one literal", &program(vec![], same), &bools());
    assert_eq!(out.matches("if c { 13 } else { 0 }").count(), 2, "{out}");
}

#[test]
fn a_part_shared_under_a_literal_and_a_parameter_is_built_only_under_the_literal() {
    // `x * 2 + c` with `x = 1` on one path and `x = c` on the other.
    let p = Shared::new(add(prim(Prim::Mul, vec![var("x"), lit(2i64)]), var("c")));
    let body = if_(
        prim(Prim::Ge, vec![var("c"), lit(0i64)]),
        Shared::new(let_("x", lit(1i64), p.clone())),
        Shared::new(let_("x", var("c"), p)),
    );
    let ints = [Value::Int(4), Value::Int(-3)];
    let out = agree("literal and parameter", &program(vec![], body), &ints);
    assert!(out.contains("2 + c"), "{out}");
    assert!(out.contains("x * 2"), "{out}");
}

#[test]
fn a_shared_test_under_a_name_rebound_between_its_places_is_decided_at_each() {
    // `t = x >= 1` at two levels, with `x` rebound between them:
    // `let x = 5; if t { let x = 0; if t { 1 } else { c } } else { 3 }`, and the same with `x`
    // the parameter at the top.
    let t = Shared::new(prim(Prim::Ge, vec![var("x"), lit(1i64)]));
    let inner = Shared::new(Term::If(
        t.clone(),
        Shared::new(lit(1i64)),
        Shared::new(var("c")),
    ));
    let nested = |x: Term| {
        let_(
            "x",
            x,
            Shared::new(Term::If(
                t.clone(),
                Shared::new(let_("x", lit(0i64), inner.clone())),
                Shared::new(lit(3i64)),
            )),
        )
    };
    let out = agree(
        "one test, x rebound",
        &program(vec![], nested(lit(5i64))),
        &bools(),
    );
    assert_eq!(out, "c -> c", "both tests are built");
    let ints = [Value::Int(4), Value::Int(-3)];
    let out = agree(
        "one test, x the parameter",
        &program(vec![], nested(var("c"))),
        &ints,
    );
    assert_eq!(
        out.matches("x >= 1").count(),
        1,
        "the outer test stays: {out}"
    );
}

#[test]
fn a_part_shared_under_functions_that_differ_calls_each() {
    // `p = f(3) + f(4)` below `let f = (y) -> y * 2` on one path and `(y) -> y + y`, which gives
    // the same values, or `(y) -> y + 1`, which does not, on the other.
    let p = reads_c(
        add(call("f", vec![lit(3i64)]), call("f", vec![lit(4i64)])),
        lit(0i64),
    );
    let double = lam(&["y"], prim(Prim::Mul, vec![var("y"), lit(2i64)]));
    for (other, want) in [
        (lam(&["y"], add(var("y"), var("y"))), 14),
        (lam(&["y"], add(var("y"), lit(1i64))), 9),
    ] {
        let body = if_(
            var("c"),
            Shared::new(let_("f", double.clone(), p.clone())),
            Shared::new(let_("f", other, p.clone())),
        );
        let out = agree("two functions", &program(vec![], body), &bools());
        assert!(out.contains("if c { 14 } else { 0 }"), "{out}");
        assert!(
            out.contains(&format!("if c {{ {want} }} else {{ 0 }}")),
            "{out}"
        );
    }
}

#[test]
fn a_function_bound_outside_a_part_that_reads_one_which_differs_is_asked_of_each() {
    // One lambda node `f = (y) -> g(y) * 2` bound on both paths over `g = (y) -> y + 1` or
    // `(y) -> y + 2`, and one part `f(3)` below both: `f` is the same term on both paths, the
    // values it gives are not.
    let f = Shared::new(lam(
        &["y"],
        prim(Prim::Mul, vec![call("g", vec![var("y")]), lit(2i64)]),
    ));
    let p = reads_c(call("f", vec![lit(3i64)]), lit(0i64));
    let path = |k: i64| {
        let g = lam(&["y"], add(var("y"), lit(k)));
        let inner = Term::Let("f".into(), f.clone(), p.clone());
        Shared::new(let_("g", g, Shared::new(inner)))
    };
    let body = if_(var("c"), path(1), path(2));
    let out = agree(
        "a function reading one that differs",
        &program(vec![], body),
        &bools(),
    );
    assert!(out.contains("if c { 8 } else { 0 }"), "{out}");
    assert!(out.contains("if c { 10 } else { 0 }"), "{out}");
}

#[test]
fn a_part_that_rebinds_a_function_it_reads_asks_the_outer_one() {
    // `p = let g = (z) -> f(z) + 10; let f = (z) -> z; g(1) + f(1)` below two outer `f`s: `g`
    // reads the outer `f`, the last call the inner one.
    let g = lam(&["z"], add(call("f", vec![var("z")]), lit(10i64)));
    let tail = add(call("g", vec![lit(1i64)]), call("f", vec![lit(1i64)]));
    let rebinds = let_(
        "g",
        g,
        Shared::new(let_("f", lam(&["z"], var("z")), Shared::new(tail))),
    );
    let p = reads_c(rebinds, lit(0i64));
    let path = |k: i64| {
        let f = lam(&["y"], add(var("y"), lit(k)));
        Shared::new(let_("f", f, p.clone()))
    };
    let body = if_(var("c"), path(100), path(200));
    let out = agree("a part rebinding `f`", &program(vec![], body), &bools());
    assert!(out.contains("if c { 112 } else { 0 }"), "{out}");
    assert!(out.contains("if c { 212 } else { 0 }"), "{out}");
}

#[test]
fn parts_shared_inside_a_shared_part_ask_for_it() {
    // `p = if c { q } else { q }` with `q = f(1)`, below two `f`s: what `q` asked of `f`, `p`
    // asked too, so `p` is not taken from the first path for the second.
    let q = Shared::new(call("f", vec![lit(1i64)]));
    let p = Shared::new(if_(var("c"), q.clone(), q));
    let path = |k: i64| {
        let f = lam(&["y"], add(var("y"), lit(k)));
        Shared::new(let_("f", f, p.clone()))
    };
    let body = if_(var("c"), path(1), path(2));
    let out = agree("nested shared parts", &program(vec![], body), &bools());
    let (two, three) = ("if c { 2 } else { 2 }", "if c { 3 } else { 3 }");
    assert!(out.contains(two) && out.contains(three), "{out}");
    // And `q` reached first outside `p`, then inside it under the other function.
    let q = Shared::new(call("f", vec![lit(1i64)]));
    let p = Shared::new(if_(var("c"), q.clone(), q.clone()));
    let f = |k: i64| lam(&["y"], add(var("y"), lit(k)));
    let body = if_(
        var("c"),
        Shared::new(let_("f", f(1), q)),
        Shared::new(let_("f", f(2), p)),
    );
    let out = agree(
        "a shared part met outside first",
        &program(vec![], body),
        &bools(),
    );
    assert!(out.contains(three), "{out}");
}

#[test]
fn a_function_reading_a_literal_that_differs_gives_each_paths_value() {
    // `let k = 1 or 2; let f = (y) -> y + k; p` with `f` one node and `p = f(10)`.
    let f = Shared::new(lam(&["y"], add(var("y"), var("k"))));
    let p = reads_c(call("f", vec![lit(10i64)]), lit(0i64));
    let path = |k: i64| {
        let inner = Term::Let("f".into(), f.clone(), p.clone());
        Shared::new(let_("k", lit(k), Shared::new(inner)))
    };
    let body = if_(var("c"), path(1), path(2));
    let out = agree(
        "a function over a literal",
        &program(vec![], body),
        &bools(),
    );
    assert!(out.contains("if c { 11 } else { 0 }"), "{out}");
    assert!(out.contains("if c { 12 } else { 0 }"), "{out}");
}

#[test]
fn a_part_calling_a_function_at_a_float_zero_gives_each_functions_value() {
    // `p = f(0.0)`: a table of answers keys a float by its bits, so `0.0` and `-0.0` are two
    // answers (item STAGE-stub-fast), and the part is keyed by what `f` gives at `0.0`. Below
    // `f = (y) -> y + 1.0` and `(y) -> y + 2.0`, `p` mixes to each one's value.
    let p = reads_c(call("f", vec![float(0.0)]), float(0.0));
    let path = |k: f64| {
        let f = lam(&["y"], add(var("y"), float(k)));
        Shared::new(let_("f", f, p.clone()))
    };
    let body = if_(var("c"), path(1.0), path(2.0));
    let out = agree("a call run as written", &program(vec![], body), &bools());
    assert!(out.contains("if c { 1.0 } else { 0.0 }"), "{out}");
    assert!(out.contains("if c { 2.0 } else { 0.0 }"), "{out}");
    // And `f` one node over a `g` that differs: what `f` is depends on what `g` is.
    let f = Shared::new(lam(&["y"], add(call("g", vec![var("y")]), float(0.5))));
    let path = |k: f64| {
        let g = lam(&["y"], add(var("y"), float(k)));
        let inner = Term::Let("f".into(), f.clone(), p.clone());
        Shared::new(let_("g", g, Shared::new(inner)))
    };
    let body = if_(var("c"), path(1.0), path(2.0));
    let u = program(vec![], body);
    let out = agree(
        "a call run as written, its function over one that differs",
        &u,
        &bools(),
    );
    assert!(out.contains("if c { 1.5 } else { 0.0 }"), "{out}");
    assert!(out.contains("if c { 2.5 } else { 0.0 }"), "{out}");
}

#[test]
fn a_part_under_a_binder_of_a_name_it_reads_is_left_and_built_outside() {
    // `p = x + 1` reached under `let x = 1` and inside `(x) -> p`, where `x` is a parameter;
    // and under a match arm that binds `x`.
    let p = Shared::new(add(var("x"), lit(1i64)));
    let inner = Term::Let(
        "g".into(),
        Shared::new(Term::Lam(vec!["x".into()], p.clone())),
        Shared::new(call("g", vec![var("c")])),
    );
    let body = let_(
        "x",
        lit(1i64),
        Shared::new(if_(
            prim(Prim::Ge, vec![var("c"), lit(0i64)]),
            p.clone(),
            Shared::new(inner),
        )),
    );
    let ints = [Value::Int(4), Value::Int(-3)];
    let out = agree("a lambda binding `x`", &program(vec![], body), &ints);
    assert!(out.contains("{ 2 }") && out.contains("x + 1"), "{out}");
    // `match p { x => { u = c; p } }`: `p` is the scrutinee, read under the outer `x`, and,
    // through a `let`, since an arm holds its body inline, the arm's body under the arm's `x`;
    // the `let` reads `c`, so the match is mixed and not evaluated whole.
    let arms = vec![(
        Pattern::Bind("x".into()),
        Term::Let("u".into(), Shared::new(var("c")), p.clone()),
    )];
    let m = Shared::new(Term::Match(p.clone(), arms));
    let body = let_("x", lit(1i64), Shared::new(if_(var("c"), p.clone(), m)));
    let out = agree("a match arm binding `x`", &program(vec![], body), &bools());
    let arm = "match 2 { x -> { u = c; (x + 1) } }";
    assert!(
        out.ends_with(&format!("if c {{ 2 }} else {{ {arm} }}")),
        "{out}"
    );
}

#[test]
fn a_part_left_to_run_under_two_bindings_is_reported_for_each() {
    // `w = (f) -> f(f)`; `p = x + w(w)`, a build-stage term whose form does not show that it
    // ends, below `let x = 1` and `let x = 2`, and `q = if x >= 2 { p } else { p }` between.
    let w = lam(&["f"], Term::App(Shared::new(var("f")), vec![var("f")]));
    let p = Shared::new(add(var("x"), call("w", vec![var("w")])));
    let q = Shared::new(if_(prim(Prim::Ge, vec![var("x"), lit(2i64)]), p.clone(), p));
    let body = Term::If(
        Shared::new(var("c")),
        Shared::new(let_("x", lit(1i64), q.clone())),
        Shared::new(let_("x", lit(2i64), q)),
    );
    let u = program(vec![("w", w)], body);
    let out = agree("a part left to run", &u, &[]);
    assert!(out.contains("x + w(w)"), "{out}");
    let (_, report) = stage::mix(&u, &["main"]);
    // The `let` of each `x` is left to run whole, once for each binding of `x`.
    assert_eq!(report.left.len(), 2, "{report:?}");
    for (t, why) in &report.left {
        let text = t.to_string();
        assert!(text.contains("part1 = (x + w(w));"), "{text}");
        assert!(
            text.contains("if (x >= 2) { part1 } else { part1 }"),
            "{text}"
        );
        assert_eq!(why, "its form does not show that it ends");
    }
}

#[test]
fn a_part_that_hands_a_function_to_one_that_calls_it_is_mixed_as_written() {
    // `apply = (k, v) -> k(v)` calls through a parameter, so its calls are not shown to end and
    // it has no stub; `p = apply(f, 2)` below two `f`s is left to run under each.
    let apply = lam(
        &["k", "v"],
        Term::App(Shared::new(var("k")), vec![var("v")]),
    );
    let p = Shared::new(call("apply", vec![var("f"), lit(2i64)]));
    let path = |k: i64| {
        let f = lam(&["y"], add(var("y"), lit(k)));
        Shared::new(let_("f", f, p.clone()))
    };
    let body = if_(var("c"), path(1), path(2));
    let out = agree(
        "a function handed on",
        &program(vec![("apply", apply)], body),
        &bools(),
    );
    assert!(out.contains("apply(f, 2)"), "{out}");
}
