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
    // LOAD-chain-move-tangent, red until design B (/home/luke/Work/wt/design-b22-load5.md, and
    // the plan row) is cross-reviewed and built: every row of the tangent chain bounds its
    // region ([`a_tangent_chain`]), so design A keeps n rows at link n and decides each link
    // from all of them, Θ(n²) for the chain: 38.3 times the instructions, 50 → 400 (colab,
    // 2026-11-23). Not for main while red.
    let chains = zed_tests::scaling::inputs(50, a_tangent_chain);
    zed_tests::scaling::check("the answers of a tangent chain", 50, |n| {
        let mut e = Extending::new();
        for f in &chains[&n] {
            let a = e.answers(f);
            assert_eq!((a.holds, a.fails), (Ok(true), Ok(true)));
        }
    });
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
