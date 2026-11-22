//! How far a port's state reaches (DESIGN L1.33): into a `match` arm and into a function bound
//! by `let` and called by its name, whatever the body holds, and nowhere else; each refusal
//! names where the port was used. Also: a fields pattern, a variadic primitive as a value, and
//! the ops `raise` has no kernel term for.

use std::sync::Arc;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, GuardPos, Pattern, Prim, Term, Value, World};
use zed_tests::kernel::{fam, fix_defined, fold};
use zedc::zir::lower::{lower, raise};
use zedc::zir::text::parse;
use zedc::zir::{Op, Region, Src, op_name};

use super::count;

fn push(port: &str, v: Term) -> Term {
    Term::Push(port.into(), v.into())
}

fn read(port: &str) -> Term {
    Term::Read(port.into())
}

fn set() -> Term {
    lit(Family::set([1, 2].map(Value::Int)))
}

/// The value of `t` and what it pushed to `stdout`, with `stdin` holding "ada".
fn run(t: &Term) -> (String, Vec<Value>) {
    let mut ev = Evaluator::new(World::new().input("stdin", "ada").output("stdout"));
    let v = ev
        .run(t)
        .map(|v| v.to_string())
        .unwrap_or_else(|e| e.to_string());
    (v, ev.world.log("stdout").to_vec())
}

/// `t` lowers, and raises to a term with its value and its pushes.
fn same(t: &Term) {
    let back = raise(&lower(t).unwrap()).unwrap();
    assert_eq!(run(&back), run(t));
}

/// The refusal of a read or push of `port` at a place the state cannot reach. Binding with
/// `let` is a repair only where the place is a function not so bound (MSG-lower-port-repair-kind).
fn refused(port: &str, inside: &str, out: &str) -> String {
    let bind = if out == "the function" {
        " bind the function with `let` and call it by its name;"
    } else {
        ""
    };
    format!(
        "`zedc build` cannot compile this program: it reads or pushes the port `{port}` \
         {inside}. Built code carries the state of a port only into the arms of a `match` and \
         into a function bound by `let` and called by its name. Repairs: move the reads and \
         pushes of `{port}` out of {out} and pass the values in or out;{bind} or run the program \
         with `zedc run`, which has no such limit"
    )
}

/// Each region kind's refusal lists only the repairs that apply to it: no `let` binding inside
/// a family, a loop or a recursive function, where there is no function to bind; the binding
/// inside a function passed as a value (plan row MSG-lower-port-repair-kind).
#[test]
fn a_refusal_lists_only_the_repairs_its_region_allows() {
    let in_family = fam(set(), "i", push("stdout", var("i")));
    let in_loop = fix_defined(set(), |_, k| push("stdout", k));
    for t in [&in_family, &in_loop] {
        let e = lower(t).unwrap_err();
        assert!(e.contains("inside a loop or a family"), "{e}");
        assert!(!e.contains("bind the function"), "{e}");
    }
    let passed = let_(
        "g",
        lam(&["h"], app(var("h"), vec![lit(1)])),
        app(var("g"), vec![lam(&["x"], push("stdout", var("x")))]),
    );
    let e = lower(&passed).unwrap_err();
    assert!(
        e.contains("; bind the function with `let` and call it by its name; or run"),
        "{e}"
    );
}

/// `let f = λ(m). body(m) in (f(2), f(3))`: two calls, so `f` is one lambda.
fn called_twice(body: impl FnOnce(Term) -> Term) -> Term {
    let_(
        "f",
        lam(&["m"], body(var("m"))),
        prim(
            Prim::Tuple,
            vec![app(var("f"), vec![lit(2)]), app(var("f"), vec![lit(3)])],
        ),
    )
}

#[test]
fn a_push_in_a_generation_or_a_fixpoint_is_refused_as_inside_a_loop() {
    let in_gen = Term::Gen {
        init: lit(0).into(),
        step: lam(&["f"], push("stdout", var("f"))).into(),
        guard: lam(&["f"], prim(Prim::Lt, vec![var("f"), lit(3)])).into(),
        pos: GuardPos::Before,
    };
    let in_fix = fix_defined(set(), |_, k| push("stdout", k));
    for (t, port) in [(in_gen, "stdout"), (in_fix, "stdout")] {
        assert_eq!(
            lower(&t).unwrap_err(),
            refused(port, "inside a loop or a family", "the loop or family"),
            "{t:?}"
        );
    }
}

/// The `port` nodes inside the bodies of `fam`, `fix` and `gen` nodes of `g`, at any depth.
fn ports_in_bodies(g: &Region) -> usize {
    g.nodes
        .iter()
        .map(|n| match op_name(&n.op) {
            "fam" | "fix" | "gen" => n.regions.iter().map(|r| count(r, "port")).sum::<usize>(),
            _ => n.regions.iter().map(|r| ports_in_bodies(r)).sum::<usize>(),
        })
        .sum()
}

/// A read inside a loop or a family body lowers (row FAIL-build-port-read-in-map): the read is
/// placed outside the outermost body, its value enters as a capture, and the raised term has
/// the value of the original. Under a `match` in the body, in a nest of families, in a family
/// in a `match` arm (the read stays in the arm), next to a push outside, in a family inside a
/// function called twice, and in a `fix` and a `gen`.
#[test]
fn a_read_in_a_loop_or_a_family_lowers_outside_the_body() {
    let concat = |a: Term, b: Term| prim(Prim::Concat, vec![a, b]);
    let show = |a: Term| prim(Prim::Show, vec![a]);
    let in_gen = Term::Gen {
        init: lit(0).into(),
        step: lam(
            &["f"],
            prim(
                Prim::Add,
                vec![var("f"), prim(Prim::Len, vec![read("stdin")])],
            ),
        )
        .into(),
        guard: lam(&["f"], prim(Prim::Lt, vec![var("f"), lit(7)])).into(),
        pos: GuardPos::Before,
    };
    let cases = [
        fam(set(), "i", concat(show(var("i")), read("stdin"))),
        fam(
            set(),
            "i",
            Term::If(
                prim(Prim::Eq, vec![var("i"), lit(1)]).into(),
                read("stdin").into(),
                lit("-").into(),
            ),
        ),
        fam(set(), "i", fam(set(), "j", read("stdin"))),
        Term::If(
            lit(true).into(),
            fam(set(), "i", read("stdin")).into(),
            lit(0).into(),
        ),
        prim(
            Prim::Tuple,
            vec![
                push("stdout", lit("x")),
                fam(set(), "i", concat(read("stdin"), read("stdin"))),
                read("stdin"),
            ],
        ),
        called_twice(|m| fam(set(), "i", concat(read("stdin"), show(m)))),
        fix_defined(set(), |_, k| concat(show(k), read("stdin"))),
        in_gen,
    ];
    for (k, t) in cases.iter().enumerate() {
        let g = lower(t).unwrap_or_else(|e| panic!("{k}: {e}"));
        assert!(count(&g, "port") > 0, "{k}");
        assert_eq!(ports_in_bodies(&g), 0, "{k}");
        same(t);
    }
}

/// A read in a function that does not push to its port lowers, the read placed outside the
/// function, so the function takes no state and may be called in a family or passed as a
/// value: a lambda passed to a fold, a read in a family inside a lambda called in place, and a
/// `let`-bound function that reads, called twice inside a family and passed as a value.
#[test]
fn a_read_in_a_function_lowers_outside_the_function() {
    let reader = lam(&["x"], prim(Prim::Concat, vec![var("x"), read("stdin")]));
    let cases = [
        fold(
            set(),
            lam(
                &["a", "b"],
                prim(
                    Prim::Add,
                    vec![var("a"), prim(Prim::Len, vec![read("stdin")])],
                ),
            ),
            Some(lit(0)),
        ),
        app(lam(&["m"], fam(set(), "i", read("stdin"))), vec![lit(0)]),
        let_(
            "r",
            reader,
            prim(
                Prim::Tuple,
                vec![
                    fam(
                        set(),
                        "i",
                        app(var("r"), vec![prim(Prim::Show, vec![var("i")])]),
                    ),
                    app(var("r"), vec![lit("x")]),
                    fold(
                        fam(set(), "i", lit("y")),
                        lam(&["a", "b"], app(var("r"), vec![var("a")])),
                        Some(lit("z")),
                    ),
                ],
            ),
        ),
    ];
    for (k, t) in cases.iter().enumerate() {
        let g = lower(t).unwrap_or_else(|e| panic!("{k}: {e}"));
        assert!(count(&g, "port") > 0, "{k}");
        assert_eq!(ports_in_bodies(&g), 0, "{k}");
        same(t);
    }
}

/// A read of a port that the term also pushes to stays where it is written (row
/// PROOF-read-hoist-no-earlier-push). DESIGN sec:ports: "a read reads the port's state when it
/// runs", so a read made after a push to its port, as `@after(a) s = fs["a.txt"]` after
/// `a = fs["a.txt"] <- x`, sees the push, and one made before it does not; one read node
/// placed outside a function called on both sides of the push would give both calls the
/// state before it. So the function takes the port's state and the call after the push takes
/// the state the push gives; in a family the read is refused as a push there is (QUESTIONS
/// A108); and a function that reads such a port, used as a value, names it.
#[test]
fn a_read_of_a_port_the_term_pushes_to_stays_in_place() {
    // `let r = λ(m). f in (r(2), f <- "x", r(3))`: `r(3)` reads after the push.
    let t = let_(
        "r",
        lam(&["m"], read("f")),
        prim(
            Prim::Tuple,
            vec![
                app(var("r"), vec![lit(2)]),
                push("f", lit("x")),
                app(var("r"), vec![lit(3)]),
            ],
        ),
    );
    let g = lower(&t).unwrap();
    let text = zedc::zir::text::print(&g);
    assert!(
        !g.nodes.iter().any(|n| matches!(n.op, Op::Read(_))),
        "the read is placed outside `r`: {text}"
    );
    let w = g
        .nodes
        .iter()
        .position(|n| matches!(n.op, Op::Push(_)))
        .unwrap();
    let after = g
        .nodes
        .iter()
        .rposition(|n| op_name(&n.op) == "apply")
        .unwrap();
    assert!(
        g.nodes[after].inputs.contains(&Src::Out(w, 1)),
        "the call after the push takes the state it gives: {text}"
    );
    let in_family = prim(
        Prim::Tuple,
        vec![push("f", lit("x")), fam(set(), "i", read("f"))],
    );
    assert_eq!(
        lower(&in_family).unwrap_err(),
        refused("f", "inside a loop or a family", "the loop or family")
    );
    let echo = lam(
        &["p"],
        prim(Prim::Tuple, vec![push("g", var("p")), read("f")]),
    );
    let as_value = let_(
        "echo",
        echo,
        prim(Prim::Tuple, vec![push("f", lit("x")), var("echo")]),
    );
    let e = lower(&as_value).unwrap_err();
    assert!(e.contains("reads or pushes the ports `g`, `f`,"), "{e}");
}

#[test]
fn a_push_in_a_family_or_in_a_lambda_passed_as_an_argument_is_refused() {
    // The wording for a family is FAIL-zir-lower-port-in-family-message; here only that it is
    // refused and names the port. A read there lowers (`a_read_in_a_loop_or_a_family_...`).
    let e = lower(&fam(set(), "i", push("stdout", var("i")))).unwrap_err();
    assert!(e.contains("the port `stdout` inside"), "{e}");
    let passed = let_(
        "g",
        lam(&["h"], app(var("h"), vec![lit(1)])),
        app(var("g"), vec![lam(&["x"], push("stdout", var("x")))]),
    );
    assert_eq!(
        lower(&passed).unwrap_err(),
        refused(
            "stdout",
            "inside a function that is not bound by `let` and called by its name",
            "the function"
        )
    );
}

#[test]
fn a_function_using_two_ports_used_as_a_value_names_both() {
    // A port the function only reads is not named: the read is placed outside the function
    // and takes no state through the call (FAIL-build-port-read-in-map).
    let echo = lam(
        &["p"],
        prim(
            Prim::Tuple,
            vec![
                push("stdout", prim(Prim::Concat, vec![var("p"), read("stdin")])),
                push("stderr", var("p")),
            ],
        ),
    );
    let t = let_("echo", echo, prim(Prim::Tuple, vec![var("echo")]));
    assert_eq!(
        lower(&t).unwrap_err(),
        "`zedc build` cannot compile this program: the function `echo`, of 1 parameter, reads \
         or pushes the ports `stdout`, `stderr`, and the program uses `echo` as a value (it \
         passes, stores or returns it) instead of calling it. Built code carries the state of \
         a port only through a call that names the function, so `echo` can only be called by \
         its name. Repairs: call `echo` by its name where it is used; move the reads and \
         pushes out of `echo` and pass the values in or out; or run the program with `zedc \
         run`, which has no such limit"
    );
}

#[test]
fn a_function_that_reads_and_pushes_called_twice_threads_both_states() {
    let t = called_twice(|m| {
        push(
            "stdout",
            prim(Prim::Concat, vec![prim(Prim::Show, vec![m]), read("stdin")]),
        )
    });
    let g = lower(&t).unwrap();
    assert_eq!((count(&g, "lambda"), count(&g, "apply")), (1, 2));
    same(&t);
}

#[test]
fn a_function_that_only_reads_called_twice_is_one_lambda() {
    let t = called_twice(|_| read("stdin"));
    let g = lower(&t).unwrap();
    assert_eq!((count(&g, "lambda"), count(&g, "apply")), (1, 2));
    same(&t);
}

#[test]
fn a_port_function_whose_body_holds_a_family_a_fold_or_a_fixpoint_keeps_them_pure() {
    let total = |m: Term| {
        push(
            "stdout",
            prim(
                Prim::Show,
                vec![fold(
                    fam(set(), "i", prim(Prim::Mul, vec![var("i"), m])),
                    Term::PrimFn(Prim::Add),
                    Some(lit(0)),
                )],
            ),
        )
    };
    let shifted = |m: Term| {
        push(
            "stdout",
            prim(
                Prim::Show,
                vec![fix_defined(set(), move |_, k| prim(Prim::Add, vec![k, m]))],
            ),
        )
    };
    for (t, op) in [(called_twice(total), "fam"), (called_twice(shifted), "fix")] {
        let g = lower(&t).unwrap();
        assert_eq!((count(&g, "lambda"), count(&g, op)), (1, 1), "{op}");
        same(&t);
    }
}

#[test]
fn equal_reads_and_equal_pushes_are_never_merged() {
    let t = prim(
        Prim::Tuple,
        vec![
            read("stdin"),
            read("stdin"),
            push("stdout", lit("x")),
            push("stdout", lit("x")),
        ],
    );
    let g = lower(&t).unwrap();
    assert_eq!(count(&g, "port"), 4);
    same(&t);
}

fn point(x: i64, y: i64) -> Value {
    Value::atom_named(
        "c",
        vec![
            (Arc::from("x"), Value::Int(x)),
            (Arc::from("y"), Value::Int(y)),
        ],
    )
    .unwrap()
}

fn fields_arm(body: Term) -> (Pattern, Term) {
    (
        Pattern::Fields(
            "c".into(),
            vec![
                ("x".into(), Pattern::Bind("a".into())),
                ("y".into(), Pattern::Bind("b".into())),
            ],
        ),
        body,
    )
}

#[test]
fn a_fields_pattern_lowers_and_raises_to_the_same_value() {
    let diff = || prim(Prim::Sub, vec![var("a"), var("b")]);
    for v in [point(5, 2), point(0, 7)] {
        let t = Term::Match(
            lit(v).into(),
            vec![fields_arm(diff()), (Pattern::Wild, lit(0))],
        );
        assert_eq!(count(&lower(&t).unwrap(), "match"), 1);
        same(&t);
    }
    // In the arm of a function that pushes and is called twice.
    let t = let_(
        "f",
        lam(
            &["v"],
            Term::Match(
                var("v").into(),
                vec![
                    fields_arm(push("stdout", prim(Prim::Show, vec![diff()]))),
                    (Pattern::Wild, lit(0)),
                ],
            ),
        ),
        prim(
            Prim::Tuple,
            vec![
                app(var("f"), vec![lit(point(5, 2))]),
                app(var("f"), vec![lit(3)]),
            ],
        ),
    );
    same(&t);
}

#[test]
fn a_variadic_primitive_as_a_value_is_refused() {
    assert_eq!(
        lower(&Term::PrimFn(Prim::Tuple)).unwrap_err(),
        super::errors::bug(
            "`(..)` takes any number of arguments, so with no inputs its node is a call, not \
             the function"
        )
    );
}

#[test]
fn raise_refuses_the_ops_the_lowering_does_not_make() {
    let rec = "\
zir 1
r region function ()
r.0 rec () -> ((-> int bool))
r.0/0 region rec ((-> int bool))
r.0/0.0 lambda (r.0/0^0) -> ((-> int bool))
r.0/0.0/0 region function (int; (-> int bool))
r.0/0.0/0.0 apply (r.0/0.0/0^1, r.0/0.0/0^0) -> (bool)
r.0/0.0/0 results (r.0/0.0/0.0^0)
r.0/0 results (r.0/0.0^0)
r results (r.0^0)
";
    let wave = "\
zir 1
r region port (state out)
r.0 wave (r^0) -> (state out)
r.0/0 region port (state out)
r.0/0.0 port push out (r.0/0^0, \"hi\") -> (_; state out)
r.0/0 results (r.0/0.0^1)
r results (0, r.0^0)
";
    for (text, op) in [(rec, "rec"), (wave, "wave")] {
        assert_eq!(
            raise(&parse(text).unwrap()).unwrap_err(),
            format!("r.0: `{op}` has no kernel term here; the lowering does not make it")
        );
    }
}
