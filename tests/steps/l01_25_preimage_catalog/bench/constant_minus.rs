//! The preimage of `c - x` over a demand of `n` pieces, at `n` and `8n`: each piece is
//! reflected once (S22b). `constant_minus.rs` checks the pieces at 12.

use zed_tests::scaling;
use zedc::store::preimage::preimage;

use crate::constant_minus::comb;

#[test]
fn a_comb_of_pieces_scales() {
    let n = 16_384;
    let made = scaling::inputs(n, comb);
    scaling::check("the preimage of c - x over a demand of n pieces", n, |k| {
        let (t, ds, d) = &made[&k];
        let p = preimage(t, ds, d);
        assert_eq!(p.domains["x"].len(), 2 * k);
    });
}
