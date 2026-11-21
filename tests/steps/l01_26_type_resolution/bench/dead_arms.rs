use zed_tests::scaling;

use super::super::dead_arms::{NEST_ARMS, dead_arm_chain, literal_chain, refused_nest};

#[test]
fn a_chain_of_dead_arms_scales() {
    // Each read of a constant under a test is met with the scope's reading of it once
    // (`Ck::ints_here`, row NARROW-dead-arm-constant), memoized by node and term.
    let built = scaling::inputs(1000, |m| {
        let stmts = zed_tests::deep::statements(&dead_arm_chain(m));
        let res = zedc::resolve::resolve(&stmts).unwrap();
        (stmts, res)
    });
    scaling::check(
        "n tests in a chain, each arm with a dead test of a constant and a `mod` by it",
        1000,
        |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn a_chain_of_literal_moduli_scales() {
    // A literal under a test is not read in the scope: one lookup of `Ck::reads_a_name`'s
    // memo each (row NARROW-settle-spurious-warning, item 3).
    let built = scaling::inputs(1000, |m| {
        let stmts = zed_tests::deep::statements(&literal_chain(m));
        let res = zedc::resolve::resolve(&stmts).unwrap();
        (stmts, res)
    });
    scaling::check(
        "n tests in a chain, each arm with a `mod` by a literal",
        1000,
        |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn held_refusals_under_nested_refused_tests_scale() {
    // The read of `m` holds the refusals of the `n` scopes it computes, and the read of the
    // division places each once (`Ck::settle`, row NARROW-settle-spurious-warning).
    let built = scaling::inputs(16, |m| {
        let stmts = zed_tests::deep::statements(&refused_nest(m, NEST_ARMS[2]));
        let res = zedc::resolve::resolve(&stmts).unwrap();
        (stmts, res)
    });
    scaling::check(
        "n nested refused tests, a constant read then a division under them",
        16,
        |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            // The one error is the division's: `x * x + 1` is not shown nonzero, at any depth.
            assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
            assert!(info.warnings.len() >= m, "{}", info.warnings.len());
        },
    );
}
