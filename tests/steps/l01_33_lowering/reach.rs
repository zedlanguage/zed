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

/// The refusal of a read or push of `port` at a place the state cannot reach.
fn refused(port: &str, inside: &str, out: &str) -> String {
    format!(
        "`zedc build` cannot compile this program: it reads or pushes the port `{port}` \
         {inside}. Built code carries the state of a port only into the arms of a `match` and \
         into a function bound by `let` and called by its name. Repairs: move the reads and \
         pushes of `{port}` out of {out} and pass the values in or out; bind the function with \
         `let` and call it by its name; or run the program with `zedc run`, which has no such \
         limit"
    )
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
    let read_in_fix = fix_defined(set(), |_, _| read("stdin"));
    for (t, port) in [
        (in_gen, "stdout"),
        (in_fix, "stdout"),
        (read_in_fix, "stdin"),
    ] {
        assert_eq!(
            lower(&t).unwrap_err(),
            refused(port, "inside a loop or a family", "the loop or family"),
            "{t:?}"
        );
    }
}

#[test]
fn a_push_in_a_family_or_in_a_lambda_passed_as_an_argument_is_refused() {
    // The wording for a family is FAIL-zir-lower-port-in-family-message; here only that it is
    // refused and names the port.
    for (t, port) in [
        (fam(set(), "i", push("stdout", var("i"))), "stdout"),
        (fam(set(), "i", read("stdin")), "stdin"),
    ] {
        let e = lower(&t).unwrap_err();
        assert!(e.contains(&format!("the port `{port}` inside")), "{e}");
    }
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
    let echo = lam(
        &["p"],
        push("stdout", prim(Prim::Concat, vec![var("p"), read("stdin")])),
    );
    let t = let_("echo", echo, prim(Prim::Tuple, vec![var("echo")]));
    assert_eq!(
        lower(&t).unwrap_err(),
        "`zedc build` cannot compile this program: the function `echo`, of 1 parameter, reads \
         or pushes the ports `stdout`, `stdin`, and the program uses `echo` as a value (it \
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
        "zedc could not compile the program because of a bug in zedc, not in the program. \
         Please report it to the Zed developers with the program's source and this line: \
         `(..)` takes any number of arguments, so with no inputs its node is a call, not the \
         function. Until it is fixed, `zedc run` runs the program without compiling it"
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
