//! Suppressing `n` warnings, at `n` and `8n` (`suppress.rs`).

use zed_tests::scaling;

use crate::suppress::{
    every_warning_suppressed, run_with_every_warning_suppressed, suppressed, suppressions_matched,
};

/// `zedc run` on a unit of `n` warnings with every one suppressed: compiling, addressing and
/// matching together are within n log n. The files and the words are made before the timing.
#[test]
fn suppressing_every_warning_scales() {
    let n = 1400;
    let runs = scaling::inputs(n, every_warning_suppressed);
    scaling::check("zedc run suppressing each of n warnings", n, |m| {
        run_with_every_warning_suppressed(&runs[&m]);
    });
}

/// Matching `n` suppressions against `n` warnings is O(n): each address is found in a set.
#[test]
fn matching_suppressions_scales() {
    let n = 270_000;
    let sizes = scaling::inputs(n, suppressed);
    scaling::check_order("matching n suppressions against n warnings", n, 1, |m| {
        suppressions_matched(&sizes[&m]);
    });
}
