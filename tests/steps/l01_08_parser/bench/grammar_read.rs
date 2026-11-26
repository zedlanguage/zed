//! A chain or a nest of `%` is read in time linear in its length: the benchmarks of
//! `grammar_read.rs`, whose test reads each at small lengths.

use zed_tests::scaling::{check, inputs};
use zedc::parse::Grammar;

use crate::grammar_read::{chain_of_separators, nest_of_separators};

#[test]
fn a_chain_of_separators_is_read_in_linear_time() {
    let texts = inputs(2_000, chain_of_separators);
    check("a grammar line of n chained `%`", 2_000, |n| {
        Grammar::read(&[&texts[&n]]).unwrap();
    });
}

/// The reader recurses once per group (the `Complexity tradeoff:` comment at `Reader::within`),
/// so the check runs on a stack deep enough for depth 8000.
#[test]
fn a_nest_of_separators_is_read_in_linear_time() {
    // n 1000, up from 32 (SCALE-small-n-rest; DESIGN sec:plan, n log n is under 10.5 only
    // from n = 777).
    zed_tests::scaling::on_a_stack(1 << 28, || {
        zed_tests::scaling::check_inputs(
            "a grammar line of n nested `%`",
            1000,
            nest_of_separators,
            |text| {
                Grammar::read(&[text]).unwrap();
            },
        );
    });
}
