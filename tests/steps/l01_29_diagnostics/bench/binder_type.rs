//! The resolution of `3n` binders that name a type, at `n` and `8n` (`binder_type.rs`).

use zed_tests::scaling;

use crate::binder_type::{binders_that_name_types_rejected, statements, typed_binders};

#[test]
fn rejecting_many_binders_that_name_types_scales() {
    // The statements of both sizes are built before timing, so only resolution is measured.
    let n = 2000;
    let built = scaling::inputs(n, |k| statements(&typed_binders(k)));
    scaling::check_order("3n binders that name a type", n, 1, |k| {
        binders_that_name_types_rejected(&built[&k], k);
    });
}
