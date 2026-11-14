//! The check of calls of a generic function with needs, at `n` and `8n` (CHK-need-bound).

use super::super::generic::{call_sites, resolved, wrapper_chain};

/// Checks `make(n)` at `n` and `8n` with `check_order`, each input resolved before timing.
fn check_scales(what: &str, n: usize, make: impl Fn(usize) -> String) {
    let inputs = zed_tests::scaling::inputs(n, |m| resolved(&make(m)));
    zed_tests::scaling::check_order(what, n, 1, |m| {
        let (stmts, res) = &inputs[&m];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{what}: {:?}", info.errors);
    });
}

#[test]
fn call_sites_scale_linearly() {
    check_scales("calls of a function with needs", 8000, call_sites);
}

#[test]
fn a_chain_of_wrappers_scales_linearly() {
    check_scales("a chain of wrappers passing a need on", 6000, wrapper_chain);
}
