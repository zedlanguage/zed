//! The benchmarks of `extend.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::extend::*;
use zedc::store::presburger::extend::Extending;
use zedc::store::presburger::{Formula, Lin};

#[test]
fn a_chain_of_extensions_is_decided_in_time_of_its_links() {
    // f{i} = f{i-1} && x + i * y <= 1000 i, over x >= y + 1: the conjunction of f{n} holds n
    // constraints, and deciding each f{i} whole costs O(n²) in all; each is decided from the
    // one it extends.
    let chain = |n: usize| {
        let mut f = Formula::and(vec![
            ge(sym("x"), sym("y").plus(&Lin::constant(1))),
            ge(sym("y"), Lin::constant(0)),
        ]);
        let mut out = Vec::with_capacity(n);
        for i in 1..=n as i64 {
            f = extend(&f, vec![sum(i, 1000 * i)]);
            out.push(f.clone());
        }
        out
    };
    let chains = zed_tests::scaling::inputs(2500, chain);
    for f in chains[&2500].iter().step_by(37) {
        assert_eq!(Extending::new().answers(f), decided(f), "{f}");
    }
    zed_tests::scaling::check("the answers of a chain of extensions", 2500, |n| {
        let mut e = Extending::new();
        for f in &chains[&n] {
            let a = e.answers(f);
            assert_eq!((a.holds, a.fails), (Ok(true), Ok(true)));
        }
    });
}

#[test]
fn a_chain_whose_points_move_is_decided_in_time_of_its_links() {
    // LOAD-chain-move: each link of the moving chain is decided from the at most 3 rows that
    // bound its region over Q ([`a_moving_chain`]); decided whole it grew 56.9 times from 50 to
    // 400 links.
    let chains = zed_tests::scaling::inputs(50, a_moving_chain);
    zed_tests::scaling::check("the answers of a chain whose points move", 50, |n| {
        let mut e = Extending::new();
        for f in &chains[&n] {
            let a = e.answers(f);
            assert_eq!((a.holds, a.fails), (Ok(true), Ok(true)));
        }
    });
}

#[test]
fn a_tangent_chain_is_decided_in_time_of_its_links() {
    // LOAD-chain-move-tangent (F1): every row of the tangent chain bounds its region
    // ([`a_tangent_chain`]), so design A kept n rows at link n and decided each link from all
    // of them, Θ(n²) for the chain: 38.3 times the instructions, 50 → 400 (colab, 2026-11-23);
    // its runs at 16000 and 8000 were killed at 11.6 GB on std4 (2026-11-24). Design B
    // (/home/luke/Work/wt/design-b22-load5.md, XR-load-call-node META3 H1-H4) adds each link's
    // row to the part's integer hull, a persistent tree of n + 3 sides, in O(log n + log A)
    // (`plane::Plane::with`), and answers from the hull: O(n log n) for the chain, whose model
    // ratio `8 ln(8n) / ln(n)` is 10.19 at 2000 -> 16000 (META2 G11; 10.78 at 400, above the
    // limit, so the sizes are 2000 and 8n).
    let chains = zed_tests::scaling::inputs(2000, a_tangent_chain);
    zed_tests::scaling::check("the answers of a tangent chain", 2000, |n| {
        let mut e = Extending::new();
        for f in &chains[&n] {
            let a = e.answers(f);
            assert_eq!((a.holds, a.fails), (Ok(true), Ok(true)));
        }
    });
}

#[test]
fn many_callers_of_a_tangent_chain_are_decided_in_time_of_their_rows() {
    // Design D14 (Claude N8): a tangent chain of n links, its hull n + 3 sides, then n callers
    // of its last link, each adding one row `x >= m` or `x <= m` that cuts away between a
    // quarter and three quarters of the sides. The hull is persistent, so each caller adds its
    // row to a new version in O(log n + log A) and leaves the base for the next: O(n log n) in
    // all, at 2000 -> 16000 as F1. A hull that read every side for each caller (the mutant
    // `SCAN` of `plane.rs`, caught by `many_callers_read_few_nodes` there) is Θ(n²).
    let make = |n: usize| {
        let chain = a_tangent_chain(n);
        let base = chain.last().expect("a link").clone();
        let k = n as i64;
        let callers: Vec<Formula> = (0..k)
            .map(|c| {
                let row = if c % 2 == 0 {
                    ge(sym("x"), Lin::constant(k / 4 + c / 2))
                } else {
                    ge(Lin::constant(3 * k / 4 - c / 2), sym("x"))
                };
                extend(&base, vec![row])
            })
            .collect();
        (chain, callers)
    };
    zed_tests::scaling::check_inputs(
        "the answers of many callers of a tangent chain",
        2000,
        make,
        |(chain, callers)| {
            let mut e = Extending::new();
            for f in chain.iter().chain(callers) {
                let a = e.answers(f);
                assert_eq!((a.holds, a.fails), (Ok(true), Ok(true)));
            }
        },
    );
}

#[test]
fn bindings_put_in_place_scale() {
    // The substitution reads each top-level constraint once and resolves each atom through a
    // union of classes with its path compressed: time of the formula times a logarithm.
    use zedc::store::presburger::extend::with_bindings_in_place;
    let chains = zed_tests::scaling::inputs(9500, |n| bound_chain(n, 0));
    zed_tests::scaling::check("the bindings of a chain put in place", 9500, |n| {
        assert!(with_bindings_in_place(&chains[&n]).is_some());
    });
}
