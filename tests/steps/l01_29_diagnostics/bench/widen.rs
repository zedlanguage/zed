//! The widening pass alone at `n` and `8n` (`widen.rs`). The units are parsed, resolved and
//! checked before the timing.

use zed_tests::scaling;

use crate::widen::{long_chain, many_squares, many_warnings, one_long_derivation, ready};

/// n warnings in a unit of O(n) nodes: the derivations share one mark vector, so a pass that
/// allocated a fresh one per warning would allocate O(n²) bytes, which this test counts.
#[test]
fn many_warnings_scale() {
    // Each unit is made ready only in the process that widens it (`scaling::check_inputs`;
    // FAIL-bench-first-phase-past-20s-l0126-l0129).
    let n = 5300;
    let unit = |m: usize| (m, ready(&many_squares(m)));
    scaling::check_inputs("n bindings that each widen", n, unit, |(size, u)| {
        many_warnings(u, *size)
    });
}

#[test]
fn a_long_derivation_scales() {
    // As in `many_warnings_scale`.
    let n = 8700;
    let unit = |m: usize| (m, ready(&long_chain(m)));
    scaling::check_inputs(
        "a chain of n bindings ending in a widening",
        n,
        unit,
        |(size, u)| one_long_derivation(u, *size),
    );
}
