//! The machine keeps the one-node region it hands the kernel for each node by the node's
//! occurrence id, numbered by one walk of the plan in path order, never by the node's address
//! (step ADDR-memory): the same program built in different allocation orders, or with a body
//! shared between two lambdas, runs to the same value with the same counts.

use std::sync::Arc;

use zed_kernel::Prim;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, Term, Value, World};
use zed_tests::kernel::{add, fold};
use zed_tests::scaling::check_order;
use zedc::zir::lower::lower;
use zedc::zir::memory;
use zedc::zir::{Op, Region};

use super::{cat, planned, run};

/// `f{i} = (x) -> x ++ "{i}"; g{i} = (y) -> f{i}(y); …` for `i` below `n`, then a tuple of
/// `(g{i}("a"), len(f{i}("b")), fold({0: 1, 1: 2}, (a, b) -> a + b + len(g{i}("z"))))` for each:
/// every body runs a kernel node, and the fold hands the kernel a closure that captures a
/// closure that captures a closure. `keep` is called between
/// the parts built, so a caller can place other allocations among them.
fn callers(n: usize, keep: &mut dyn FnMut()) -> Term {
    let ones = Value::Family(Family::of(
        [(0, 1), (1, 2)].map(|(k, x)| (Value::Int(k), Value::Int(x))),
    ));
    let mut parts = Vec::new();
    for i in 0..n {
        keep();
        let (f, g) = (format!("f{i}"), format!("g{i}"));
        let z = prim(Prim::Len, vec![app(var(&g), vec![lit("z")])]);
        let op = lam(&["a", "b"], add(add(var("a"), var("b")), z));
        keep();
        parts.push(prim(
            Prim::Tuple,
            vec![
                app(var(&g), vec![lit("a")]),
                prim(Prim::Len, vec![app(var(&f), vec![lit("b")])]),
                fold(lit(ones.clone()), op, None),
            ],
        ));
    }
    let mut t = prim(Prim::Tuple, parts);
    for i in (0..n).rev() {
        keep();
        let (f, g) = (format!("f{i}"), format!("g{i}"));
        let body = prim(Prim::Concat, vec![var("x"), lit(i.to_string().as_str())]);
        t = let_(
            &f,
            lam(&["x"], body),
            let_(&g, lam(&["y"], app(var(&f), vec![var("y")])), t),
        );
    }
    t
}

/// The value and counts of `t` lowered, planned with fusion and run, with its plan.
fn outcome(t: &Term) -> (String, memory::Stats, memory::Plan) {
    let (g, p) = planned(t, true);
    let (v, s) = run(&g, &p).unwrap_or_else(|e| panic!("{e}"));
    (v, s, p)
}

/// The same program built in three allocation orders gives the same plan, value and counts.
#[test]
fn the_machine_keeps_nodes_by_place_not_address() {
    let plain = callers(5, &mut || {});
    let mut held: Vec<Vec<u64>> = Vec::new();
    let mut n = 0;
    let interleaved = callers(5, &mut || {
        n += 1;
        held.push(vec![0; 1 + n % 7]);
    });
    let mut big: Vec<Box<[u8]>> = (0..1000).map(|i| vec![0; 16 + i % 64].into()).collect();
    big.retain(|b| b.len() % 2 == 0);
    let shifted = callers(5, &mut || {});
    assert!(plain == interleaved && plain == shifted);
    let want = outcome(&plain);
    assert_eq!(
        want.0,
        r#"(("a0", 2, 5), ("a1", 2, 5), ("a2", 2, 5), ("a3", 2, 5), ("a4", 2, 5))"#
    );
    assert_eq!(outcome(&interleaved), want);
    assert_eq!(outcome(&shifted), want);
    drop((held, big));
}

/// The indices of the lambda nodes of `g`'s root region.
fn lambdas(g: &Region) -> Vec<usize> {
    let is_lambda = |k: &usize| matches!(g.nodes[*k].op, Op::Lambda);
    (0..g.nodes.len()).filter(is_lambda).collect()
}

/// Two lambdas with the same body and different captures, once with a body each and once
/// sharing one body, as a pass that hash-conses regions would leave them: the shared body is
/// run at two places, each its own occurrence, and the runs agree.
#[test]
fn a_body_shared_by_two_lambdas_runs_as_two_occurrences() {
    // `s = "a" ++ "!"; u = "c" ++ "?"; f = (x) -> x ++ s; h = (x) -> x ++ u;
    // (f("p"), h("q"), len(h("r")))`: both bodies are `x ++` their capture.
    let body = |c: &str| lam(&["x"], prim(Prim::Concat, vec![var("x"), var(c)]));
    let t = let_(
        "s",
        cat("a", "!"),
        let_(
            "u",
            cat("c", "?"),
            let_(
                "f",
                body("s"),
                let_(
                    "h",
                    body("u"),
                    prim(
                        Prim::Tuple,
                        vec![
                            app(var("f"), vec![lit("p")]),
                            app(var("h"), vec![lit("q")]),
                            prim(Prim::Len, vec![app(var("h"), vec![lit("r")])]),
                        ],
                    ),
                ),
            ),
        ),
    );
    // The bodies differ only in the hint naming their capture; `apart` gives the second lambda
    // a copy of the first body, and `shared` the first body itself.
    let mut apart = lower(&t).unwrap();
    let ls = lambdas(&apart);
    assert_eq!(ls.len(), 2);
    let (first, second) = (ls[0], ls[1]);
    let body = &apart.nodes[first].regions[0];
    assert_eq!(body.nodes, apart.nodes[second].regions[0].nodes);
    apart.nodes[second].regions[0] = Arc::new(Region::clone(body));
    let mut shared = apart.clone();
    shared.nodes[second].regions[0] = Arc::clone(&shared.nodes[first].regions[0]);
    assert!(!Arc::ptr_eq(
        &apart.nodes[first].regions[0],
        &apart.nodes[second].regions[0]
    ));
    assert!(Arc::ptr_eq(
        &shared.nodes[first].regions[0],
        &shared.nodes[second].regions[0]
    ));
    assert_eq!(shared, apart);
    for fuse in [true, false] {
        let (pa, ps) = (memory::plan(&apart, fuse), memory::plan(&shared, fuse));
        assert_eq!(ps, pa);
        let (va, sa) = run(&apart, &pa).unwrap_or_else(|e| panic!("{e}"));
        let (vs, ss) = run(&shared, &ps).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(va, r#"("pa!", "qc?", 3)"#);
        assert_eq!((vs, ss), (va, sa));
    }
}

/// Running `n` lambdas, each called twice and once handed to the kernel inside a closure, is
/// linear in `n`: each node occurrence finds its one-node region by its id.
#[test]
fn running_many_node_occurrences_is_linear() {
    let (small, large) = (lower(&callers(1_000, &mut || {})).unwrap(), {
        lower(&callers(8_000, &mut || {})).unwrap()
    });
    let (ps, pl) = (memory::plan(&small, true), memory::plan(&large, true));
    check_order(
        "running n lambdas, each node by its occurrence id",
        1_000,
        1,
        |n| {
            let (g, p) = if n == 1_000 {
                (&small, &ps)
            } else {
                (&large, &pl)
            };
            memory::run(g, p, &mut Evaluator::new(World::new())).unwrap();
        },
    );
}
