//! The size of the graph at the rule of low complexity (DESIGN.md Part G): a function that uses
//! a port is one `lambda` node, called by `apply` nodes that thread the state, so a chain of
//! such functions, each calling the one before twice, lowers to a graph linear in the chain's
//! length and not exponential in it.

use zed_kernel::term::build::{app, lam, let_, lit, var};
use zed_kernel::{Evaluator, Term, World};
use zed_tests::scaling;
use zedc::zir::Region;
use zedc::zir::lower::{lower, raise};

fn push(port: &str, v: Term) -> Term {
    Term::Push(port.into(), v.into())
}

/// `f0 m = push m`, and `f{i} m = (f{i-1} m; f{i-1} m)`, with `f{k}` called once.
pub(crate) fn chain(k: usize) -> Term {
    let mut t = app(var(&format!("f{k}")), vec![lit("x")]);
    for i in (1..=k).rev() {
        let g = var(&format!("f{}", i - 1));
        let body = let_("a", app(g.clone(), vec![var("m")]), app(g, vec![var("m")]));
        t = let_(&format!("f{i}"), lam(&["m"], body), t);
    }
    let_("f0", lam(&["m"], push("stdout", var("m"))), t)
}

fn nodes(g: &Region) -> usize {
    g.nodes
        .iter()
        .map(|n| 1 + n.regions.iter().map(nodes).sum::<usize>())
        .sum()
}

#[test]
fn a_chain_of_functions_that_push_lowers_to_a_graph_linear_in_its_length() {
    let (small, large) = (
        nodes(&lower(&chain(4)).unwrap()),
        nodes(&lower(&chain(16)).unwrap()),
    );
    assert!(
        large <= 5 * small,
        "a chain of 4 functions that push lowers to {small} nodes and one of 16 to {large}, \
         and the graph is to grow linearly in the chain's length"
    );
}

#[test]
fn the_chain_raises_to_a_term_that_pushes_as_often_as_the_original() {
    for k in [0, 1, 3] {
        let t = chain(k);
        let back = raise(&lower(&t).unwrap()).unwrap();
        let log = |t: &Term| {
            let mut ev = Evaluator::new(World::new().output("stdout"));
            ev.run(t).unwrap();
            ev.world.log("stdout").len()
        };
        assert_eq!(log(&back), 1 << k);
        assert_eq!(log(&back), log(&t));
    }
}

#[test]
fn lowering_the_chain_scales() {
    // The lowering recurses once for each nested `let`, so the chain of 800 runs on a stack
    // large enough for a debug build.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check("lowering a chain of functions that push", 100, |k| {
                lower(&chain(k)).unwrap();
            })
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `if i < d then (let y{i} = (if ...) + 1 in y{i}) else i`, `d` deep: each level a match node
/// whose arm holds the next, its edge carrying the hint of a `let`.
pub(crate) fn nest(d: usize) -> Term {
    use zed_kernel::Prim;
    use zed_kernel::term::build::{if_, prim};
    let mut t = lit(0);
    for i in 0..d {
        let y = format!("y{i}");
        let inner = let_(&y, prim(Prim::Add, vec![t, lit(1)]), var(&y));
        t = if_(
            prim(Prim::Lt, vec![lit(i as i64), lit(d as i64)]),
            inner,
            lit(i as i64),
        );
    }
    t
}

/// CSE keys each node by the hashes of its regions, so a nest is not canonicalized again at
/// every level above it (COMPLEXITY.md Z2, Z3).
#[test]
fn lowering_a_deep_nest_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check("lowering a nest of `if`s", 100, |d| {
                lower(&nest(d)).unwrap();
            })
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `let x0 = 1 in let x1 = x0 + 1 in … in x{n-1}`: each binding reads the name bound
/// farthest out.
pub(crate) fn far(n: usize) -> Term {
    use zed_kernel::Prim;
    use zed_kernel::term::build::prim;
    let mut t = var(&format!("x{}", n - 1));
    for i in (1..n).rev() {
        t = let_(
            &format!("x{i}"),
            prim(Prim::Add, vec![var("x0"), lit(i as i64)]),
            t,
        );
    }
    let_("x0", lit(1), t)
}

/// A name is found by a map, not by searching the scope (COMPLEXITY.md Z6).
#[test]
fn reading_a_name_bound_far_out_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            scaling::check("lowering lets that read the outermost name", 2000, |n| {
                lower(&far(n)).unwrap();
            })
        })
        .unwrap()
        .join()
        .unwrap();
}
