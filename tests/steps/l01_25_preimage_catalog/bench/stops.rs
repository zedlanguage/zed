//! `n` stops over one shared term of size `n`, at `n` and `8n`: a stop holds its term and
//! makes its text only when read. `stops.rs` checks the stops of the same term at small sizes.

use zed_tests::scaling;
use zedc::store::preimage::{Demand, preimage};

use crate::doms;
use crate::stops::stops_over_one_term;

/// A stop holds its term and makes its text only when read, so `n` stops over one shared term
/// of size `n` take time of order `n`; printing each stop's term during the transfer took
/// `n^2`.
#[test]
fn many_stops_over_one_shared_term_make_no_text() {
    let ds = doms(&[("x", None, None)]);
    let ds = &ds;
    let terms = scaling::inputs(2048, stops_over_one_term);
    scaling::on_a_thread(2 << 20, || {
        scaling::check("stops over one shared term", 2048, |n| {
            let p = preimage(&terms[&n], ds, &Demand::Bool(true));
            assert_eq!(p.stops.len(), n);
        })
    });
}
