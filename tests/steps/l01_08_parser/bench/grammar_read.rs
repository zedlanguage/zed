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
/// so the depths stay small.
#[test]
fn a_nest_of_separators_is_read_in_linear_time() {
    let texts = inputs(32, nest_of_separators);
    check("a grammar line of n nested `%`", 32, |n| {
        Grammar::read(&[&texts[&n]]).unwrap();
    });
}
