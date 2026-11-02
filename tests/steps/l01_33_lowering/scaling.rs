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
        .map(|n| 1 + n.regions.iter().map(|r| nodes(r)).sum::<usize>())
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

/// `g{d} = (x{d}) -> (… (g1 = (x1) -> 1; g1(1)) …); g{d}(d)`: `let`-bound lambdas nested `d`
/// deep.
fn lets_of_lambdas(d: usize) -> Term {
    (1..=d).fold(lit(1i64), |b, i| {
        let g = format!("g{i}");
        let_(
            &g,
            lam(&[&format!("x{i}")], b),
            app(var(&g), vec![lit(i as i64)]),
        )
    })
}

#[test]
fn lowering_lambdas_bound_by_nested_lets_scales() {
    // The ports of each `let`-bound lambda were found by reading its whole body, the lambdas
    // nested in it included.
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            scaling::check("lowering let-bound lambdas nested n deep", 500, |d| {
                lower(&lets_of_lambdas(d)).unwrap();
            });
            let t = lets_of_lambdas(3);
            let back = raise(&lower(&t).unwrap()).unwrap();
            let run = |t: &Term| Evaluator::new(World::new()).run(t).unwrap();
            assert_eq!(run(&back), run(&t));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `c{i} = (m) -> stdout <- m; r{i} = c{i}(i); …` for `i` from 1 to `n`, then `0`: functions that
/// push, each called once, so each call lowers in place under the scope it was defined in.
fn calls_in_place(n: usize) -> Term {
    (1..=n).rev().fold(lit(0i64), |t, i| {
        let c = format!("c{i}");
        let_(
            &c,
            lam(&["m"], push("stdout", var("m"))),
            let_(&format!("r{i}"), app(var(&c), vec![lit(i as i64)]), t),
        )
    })
}

#[test]
fn lowering_many_functions_called_in_place_scales() {
    // Each such function kept a copy of the whole scope it was defined in, and its call rebuilt
    // the index of that scope.
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            scaling::check(
                "lowering n functions each called once in place",
                2000,
                |n| {
                    lower(&calls_in_place(n)).unwrap();
                },
            );
            let t = calls_in_place(3);
            let back = raise(&lower(&t).unwrap()).unwrap();
            let run = |t: &Term| {
                let mut ev = Evaluator::new(World::new().output("stdout"));
                let v = ev.run(t).unwrap();
                (v, ev.world.log("stdout").to_vec())
            };
            let (v, pushed) = run(&t);
            assert_eq!(pushed.len(), 3);
            assert_eq!(run(&back), (v, pushed));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The graph of `n` pushes in a row is checked in time that scales: each state edge's uses
/// are counted in a map, not by searching the edges counted before (COMPLEXITY.md Z10).
#[test]
fn checking_a_graph_of_many_pushes_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            let graphs: std::collections::BTreeMap<usize, Region> = [N, N * scaling::FACTOR]
                .into_iter()
                .map(|n| (n, lower(&calls_in_place(n)).unwrap()))
                .collect();
            scaling::check("checking a graph of n pushes", N, |n| {
                zedc::zir::validate(&graphs[&n]).unwrap();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

const N: usize = 4000;

/// `r{i} = p{i} <- i; …` for `i` from 1 to `n`, then `0`: pushes to `n` different ports.
fn pushes_to_many_ports(n: usize) -> Term {
    (1..=n).rev().fold(lit(0i64), |t, i| {
        let_(&format!("r{i}"), push(&format!("p{i}"), lit(i as i64)), t)
    })
}

/// The current state of each port is found by a map, not by searching the ports used before
/// (COMPLEXITY.md Z13).
#[test]
fn lowering_pushes_to_many_ports_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            scaling::check("lowering pushes to n ports", 2000, |n| {
                lower(&pushes_to_many_ports(n)).unwrap();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A price table: `base = 2 * 5; if base < 0 then 0 else if base < 1 then 1 else …`, `d` tests
/// in a chain, each reading `base` from outside its own region, ending at `d`.
fn prices(d: usize) -> Term {
    use zed_kernel::Prim;
    use zed_kernel::term::build::{if_, prim};
    let chain = (0..d).rev().fold(lit(d as i64), |rest, i| {
        let c = prim(Prim::Lt, vec![var("base"), lit(i as i64)]);
        if_(c, lit(i as i64), rest)
    });
    let_("base", prim(Prim::Mul, vec![lit(2i64), lit(5i64)]), chain)
}

/// The most inputs of any node in `g`.
fn widest(g: &Region) -> usize {
    g.nodes
        .iter()
        .map(|n| {
            let below = n.regions.iter().map(|r| widest(r)).max().unwrap_or(0);
            n.inputs.len().max(below)
        })
        .max()
        .unwrap_or(0)
}

#[test]
fn a_name_read_at_every_depth_enters_each_region_once() {
    // The condition and `base`, however many reads of `base` lie below.
    assert_eq!(widest(&lower(&prices(40)).unwrap()), 2);
}

#[test]
fn a_name_read_at_every_depth_keeps_its_meaning() {
    use zed_kernel::Prim;
    use zed_kernel::term::build::{if_, prim};
    let run = |t: &Term| Evaluator::new(World::new()).run(t).unwrap();
    for t in [
        prices(0),
        prices(1),
        prices(12),
        prices(40),
        // Read in both arms, and in the second through a name bound inside the first level.
        let_(
            "a",
            prim(Prim::Mul, vec![lit(2i64), lit(3i64)]),
            if_(
                prim(Prim::Lt, vec![var("a"), lit(9i64)]),
                let_(
                    "b",
                    prim(Prim::Add, vec![var("a"), var("a")]),
                    if_(
                        prim(Prim::Lt, vec![var("b"), var("a")]),
                        var("a"),
                        prim(Prim::Add, vec![var("b"), var("a")]),
                    ),
                ),
                var("a"),
            ),
        ),
    ] {
        assert_eq!(run(&raise(&lower(&t).unwrap()).unwrap()), run(&t), "{t}");
    }
}

#[test]
fn a_name_read_at_every_depth_scales() {
    // Each read carried the name through every region above it, as a new input of each.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            scaling::check("lowering n nested reads of one name", 500, |d| {
                lower(&prices(d)).unwrap();
            })
        })
        .unwrap()
        .join()
        .unwrap();
}
