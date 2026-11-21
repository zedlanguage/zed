use zed_tests::scaling;

use super::super::dead_arms::dead_arm_chain;

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
