//! `n` negated literal chains, and one of `n` words, at `n` and `8n` (`neglit.rs`).

use zed_tests::scaling;

use crate::neglit::{long, many, many_chains_rejected, one_long_chain_rejected};

#[test]
fn rejecting_many_chains_and_one_long_chain_scales() {
    // The inputs are built before the timing.
    let n = 8400;
    let units = scaling::inputs(n, |k| (many(k), long(k)));
    scaling::check("rejecting n negated literal chains in one unit", n, |k| {
        many_chains_rejected(&units[&k].0);
    });
    scaling::check("rejecting one negated literal chain of n words", n, |k| {
        one_long_chain_rejected(&units[&k].1);
    });
}
