//! Common subexpressions: a node whose canonical form has the address of one already in its
//! region is not added again.

use zed_kernel::Prim;
use zed_kernel::Term;
use zed_kernel::term::build::{lam, let_, lit, prim, var};
use zedc::zir::lower::lower;

use super::{count, eval, graph, round_trip};

#[test]
fn a_repeated_product_is_one_node() {
    // `x * 2 + x * 2`: one product, one sum.
    let g = graph("f(positional x) = x * 2 + x * 2\ntest { 3 -> 12 }\n", "f");
    assert_eq!(count(&g, "prim"), 2);
}

#[test]
fn let_names_do_not_separate_equal_nodes() {
    // `a = x + 1; b = x + 1; a * b`: the two sums differ only in the name hint.
    let body = let_(
        "a",
        prim(Prim::Add, vec![var("x"), lit(1)]),
        let_(
            "b",
            prim(Prim::Add, vec![var("x"), lit(1)]),
            prim(Prim::Mul, vec![var("a"), var("b")]),
        ),
    );
    let t = Term::App(lam(&["x"], body).into(), vec![lit(6)]);
    let g = lower(&t).unwrap();
    // The call of a literal lambda is lowered in place, with `x` the constant 6.
    assert_eq!(
        (count(&g, "prim"), count(&g, "lambda"), g.nodes.len()),
        (2, 0, 2)
    );
    // The sum keeps the first name as a hint, and the graph prints and reads back.
    let text = zedc::zir::text::print(&g);
    assert!(text.contains("hint name \"a\""), "{text}");
    assert!(!text.contains("hint name \"b\""), "{text}");
    assert_eq!(zedc::zir::text::parse(&text), Ok(g));
    assert_eq!(round_trip(&t), Ok("49".into()));
}

#[test]
fn equal_lambdas_are_one_node() {
    let inc = || lam(&["n"], prim(Prim::Add, vec![var("n"), lit(1)]));
    let t = prim(Prim::Tuple, vec![inc(), inc()]);
    let g = lower(&t).unwrap();
    assert_eq!(count(&g, "lambda"), 1);
    // Different bodies stay apart.
    let dec = lam(&["n"], prim(Prim::Sub, vec![var("n"), lit(1)]));
    let g = lower(&prim(Prim::Tuple, vec![inc(), dec])).unwrap();
    assert_eq!(count(&g, "lambda"), 2);
}

#[test]
fn nodes_in_different_regions_stay_apart() {
    // `x + 1` inside each arm is a node of that arm's region, not of the root.
    let t = Term::App(
        lam(
            &["x"],
            zed_kernel::term::build::if_(
                prim(Prim::Lt, vec![var("x"), lit(0)]),
                prim(Prim::Add, vec![var("x"), lit(1)]),
                prim(Prim::Add, vec![var("x"), lit(1)]),
            ),
        )
        .into(),
        vec![prim(Prim::Neg, vec![lit(5)])],
    );
    let g = lower(&t).unwrap();
    assert_eq!(count(&g, "prim"), 4);
    assert_eq!(round_trip(&t), eval(&t));
}
