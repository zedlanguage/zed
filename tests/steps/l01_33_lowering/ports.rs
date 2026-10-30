//! Ports: each port's state edge enters the root as an argument, passes from node to node
//! in the order of the effects, and leaves as a result; an arm that does not touch a port
//! passes its state through.

use zed_kernel::term::build::{if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zedc::zir::lower::{lower, raise};
use zedc::zir::{Edge, RegionKind, Src};

use super::count;

fn push(port: &str, v: Term) -> Term {
    Term::Push(port.into(), v.into())
}

/// The value of `t` and what it pushed to `stdout`, with `stdin` holding `line`.
fn run(t: &Term, line: &str) -> (String, Vec<Value>) {
    let mut ev = Evaluator::new(World::new().input("stdin", line).output("stdout"));
    let v = ev
        .run(t)
        .map(|v| v.to_string())
        .unwrap_or_else(|e| e.to_string());
    (v, ev.world.log("stdout").to_vec())
}

fn same(t: &Term, line: &str) {
    let back = raise(&lower(t).unwrap()).unwrap();
    assert_eq!(run(&back, line), run(t, line));
}

#[test]
fn two_pushes_thread_one_state_edge() {
    let t = let_(
        "a",
        push(
            "stdout",
            prim(
                Prim::Concat,
                vec![lit("hello, "), Term::Read("stdin".into())],
            ),
        ),
        let_(
            "b",
            push("stdout", lit("bye")),
            prim(Prim::Tuple, vec![var("a"), var("b")]),
        ),
    );
    let g = lower(&t).unwrap();
    assert_eq!(g.kind, RegionKind::Port);
    // The value is computed before the push takes the port, so `stdin` comes first.
    assert_eq!(
        g.args,
        [Edge::State("stdin".into()), Edge::State("stdout".into())]
    );
    let push2 = g.nodes.len() - 2;
    assert_eq!(g.nodes[push2].inputs[0], Src::Out(push2 - 1, 1));
    assert_eq!(g.results[2], Src::Out(push2, 1));
    same(&t, "ada");
}

#[test]
fn an_arm_that_does_not_push_passes_the_state_through() {
    let t = if_(
        prim(Prim::Eq, vec![Term::Read("stdin".into()), lit("x")]),
        push("stdout", lit("yes")),
        lit(Value::atom("skip")),
    );
    let g = lower(&t).unwrap();
    let node = g.nodes.last().unwrap();
    assert_eq!(node.outputs[1], Edge::State("stdout".into()));
    assert_eq!(node.regions[0].results[1], Src::Out(0, 1));
    assert_eq!(node.regions[1].results[1], Src::Arg(0));
    same(&t, "x");
    same(&t, "y");
}

#[test]
fn a_function_that_pushes_is_inlined_at_each_call() {
    let say = lam(&["m"], push("stdout", var("m")));
    let t = let_(
        "say",
        say,
        prim(
            Prim::Tuple,
            vec![
                Term::App(var("say").into(), vec![lit("a")]),
                Term::App(var("say").into(), vec![lit("b")]),
            ],
        ),
    );
    let g = lower(&t).unwrap();
    assert_eq!((count(&g, "port"), count(&g, "lambda")), (2, 0));
    same(&t, "");
    assert_eq!(run(&t, "").1, [Value::str("a"), Value::str("b")]);
}

#[test]
fn each_arm_passes_through_the_ports_it_does_not_touch() {
    // One arm pushes, the other reads: each arm returns both states, its own and the other's.
    let t = if_(
        prim(Prim::Lt, vec![lit(1), lit(2)]),
        push("stdout", lit("yes")),
        Term::Read("stdin".into()),
    );
    let g = lower(&t).unwrap();
    let node = g.nodes.last().unwrap();
    assert_eq!(
        node.outputs[1..],
        [Edge::State("stdout".into()), Edge::State("stdin".into())]
    );
    assert_eq!(node.regions[0].results[1..], [Src::Out(0, 1), Src::Arg(1)]);
    assert_eq!(node.regions[1].results[1..], [Src::Arg(0), Src::Out(0, 1)]);
    same(&t, "z");
}
