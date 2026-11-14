//! The large fixed-seed suite of `product_parity.rs` (TEST-corr-slow-l0138), run by
//! `tools/run_tests.sh --bench`.

use crate::product_parity::*;
use zed_tests::instances::Rng;

/// `product_parity::every_point_returned_holds_with_products_parity_rows_and_disjunctions` as
/// first written, 5.9 s (2026-11-14, load 25): the 3000 formulas of seed 0x5eed0f9a417e5.
#[test]
fn every_point_returned_on_3000_formulas_holds_with_products_parity_rows_and_disjunctions() {
    let t = points_returned_hold(&mut Rng::new(0x0005_eed0_f9a4_17e5), 3000);
    // Both answers occur often enough to be tested, and few questions are refused.
    assert!(t.points >= 500 && t.empty >= 500, "{t:?}");
    assert!(t.searched >= 100, "{t:?}");
    assert!(t.refused * 20 <= 3000, "{t:?}");
    assert!(t.shapes.len() >= 3, "{t:?}");
}
