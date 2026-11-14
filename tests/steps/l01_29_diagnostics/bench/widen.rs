//! The widening pass alone at `n` and `8n` (`widen.rs`). The units are parsed, resolved and
//! checked before the timing.

use zed_tests::scaling;

use crate::widen::{long_chain, many_squares, many_warnings, one_long_derivation, ready};

/// n warnings in a unit of O(n) nodes: the derivations share one mark vector, so a pass that
/// allocated a fresh one per warning would allocate O(n²) bytes, which this test counts.
#[test]
fn many_warnings_scale() {
    let n = 5300;
    let units = scaling::inputs(n, |m| ready(&many_squares(m)));
    scaling::check("n bindings that each widen", n, |size| {
        many_warnings(&units[&size], size)
    });
}

#[test]
fn a_long_derivation_scales() {
    let n = 8700;
    let units = scaling::inputs(n, |m| ready(&long_chain(m)));
    scaling::check("a chain of n bindings ending in a widening", n, |size| {
        one_long_derivation(&units[&size], size)
    });
}
