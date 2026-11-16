//! A closure holds only the values it reads (DESIGN.md sec:generations; row
//! CLOSURE-captures-read-only): the lowering gives a `lambda` node one capture input per name
//! its body reads, nested lambdas' bodies included, and none for a name in scope it does not
//! read, so the counting machine releases an unread value while the closure lives. The kernel
//! evaluator's side is `zed_kernel` `eval::tests::a_closure_holds_only_the_values_its_body_reads`.

use std::sync::Arc;

use zed_kernel::eval::MadeNode;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, Prim, Shared, Term, Value, World};
use zedc::zir::{Op, Region};

use super::{planned, run};

/// A pair built by the program, so that it is a cell of the machine and not a constant.
fn pair(a: i64, b: i64) -> Term {
    prim(Prim::Tuple, vec![lit(a), lit(b)])
}

/// `a = (1, 2); b = (3, 4); f = <lambda>; (f(0)…(0), b)`, `f` called `calls` times in a row:
/// `b` is in scope where the lambda is made and read after it, so only the lambda's capture
/// would make the closure hold it.
fn program(lambda: Term, calls: usize) -> Term {
    let called = (0..calls).fold(var("f"), |f, _| app(f, vec![lit(0i64)]));
    let_(
        "a",
        pair(1, 2),
        let_(
            "b",
            pair(3, 4),
            let_("f", lambda, prim(Prim::Tuple, vec![called, var("b")])),
        ),
    )
}

/// The number of inputs, all of them captures, of each `lambda` node of `g`, outermost first.
fn lambdas(g: &Region) -> Vec<usize> {
    let mut out = Vec::new();
    let mut todo: Vec<&Region> = vec![g];
    while let Some(r) = todo.pop() {
        for n in &r.nodes {
            if n.op == Op::Lambda {
                out.push(n.inputs.len());
            }
            todo.extend(n.regions.iter().map(Arc::as_ref));
        }
    }
    out
}

/// `x0 = 0; …; x(n-1) = n - 1; map(0..n, i -> f)`, `f` the lambda `y -> x(n/2) + y`: n
/// closures, each made in a scope of n names and reading one. Called on `i` when `called`, so
/// the family holds `n/2 + i` at `i`; kept as they are otherwise, a family of n closures.
pub(super) fn closures_in_scope(n: usize, called: bool) -> Term {
    let read = format!("x{}", n / 2);
    let f = lam(&["y"], prim(Prim::Add, vec![var(&read), var("y")]));
    let entry = if called { app(f, vec![var("i")]) } else { f };
    let keys = Value::Family(Family::set((0..n as i64).map(Value::from)));
    let map = Term::Fam {
        domain: Shared::new(lit(keys)),
        var: "i".into(),
        body: Shared::new(entry),
    };
    (0..n)
        .rev()
        .fold(map, |body, k| let_(&format!("x{k}"), lit(k as i64), body))
}

/// [`closures_in_scope`] at a few sizes: the family of sums is the one expected, and the
/// family of closures is given back apart from the run with one capture each, the name read.
/// Benchmarks: `bench::closures_made_in_a_scope_of_n_names_scale` and
/// `bench::closures_kept_from_a_scope_of_n_names_scale`.
#[test]
fn closures_made_in_a_scope_of_many_names_hold_the_one_they_read() {
    for n in [1, 2, 5, 16] {
        let mut ev = Evaluator::new(World::new());
        let sums = ev.run(&closures_in_scope(n, true)).unwrap();
        let want = Family::of((0..n as i64).map(|i| (i, n as i64 / 2 + i)));
        assert_eq!(sums, Value::Family(want), "n {n}");
        let made = ev.run_made(&closures_in_scope(n, false)).unwrap();
        let caps: Vec<Vec<String>> = made
            .nodes
            .iter()
            .filter_map(|node| match node {
                MadeNode::Fun(f) => Some(f.caps.iter().map(|(x, _)| x.to_string()).collect()),
                _ => None,
            })
            .collect();
        assert_eq!(caps, vec![vec![format!("x{}", n / 2)]; n], "n {n}");
    }
}

#[test]
fn a_lambda_node_captures_only_the_names_its_body_reads() {
    // The lambda, the calls of it in a row, and the capture inputs of its node and of the node
    // of the lambda inside it.
    let cases = [
        (lam(&["x"], var("a")), 1, vec![1]),
        (lam(&["x"], var("x")), 1, vec![0]),
        (lam(&["x"], lam(&["y"], var("a"))), 2, vec![1, 1]),
        (
            lam(&["x"], prim(Prim::Tuple, vec![var("a"), var("b")])),
            1,
            vec![2],
        ),
    ];
    for (lambda, calls, want) in cases {
        let t = program(lambda, calls);
        let what = zed_kernel::print::pretty(&t, 80);
        let kernel = Evaluator::new(World::new())
            .run(&t)
            .unwrap_or_else(|e| panic!("{what}: {e}"));
        for fuse in [true, false] {
            let (g, p) = planned(&t, fuse);
            assert_eq!(lambdas(&g), want, "{what}");
            let (v, _) = run(&g, &p).unwrap_or_else(|e| panic!("{what}: {e}"));
            assert_eq!(v, kernel.to_string(), "{what}");
        }
    }
}
