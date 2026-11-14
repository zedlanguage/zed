//! `n` diagnostics on one line, rendered and listed at `n` and `8n` (`quoted.rs`).

use zed_tests::scaling;
use zedc::front::Diagnostic;

use crate::quoted::{listing, many_errors_rendered_on_one_line, operands, sums, untracked_sum};

#[test]
fn rendering_many_errors_on_one_line_scales() {
    // The sum gives three diagnostics per component, each with a few steps, so the listing is
    // O(n) once the line is shown once.
    let n = 100;
    let inputs = scaling::inputs(n, untracked_sum);
    scaling::check("n errors of `sum` on one line of n components", n, |k| {
        many_errors_rendered_on_one_line(&inputs[&k]);
    });
}

#[test]
fn listing_many_diagnostics_on_one_line_scales() {
    let n = 1000;
    let large = scaling::FACTOR * n;
    for (what, make) in [
        (
            "listing n diagnostics of a sum on one line",
            sums as fn(usize) -> Vec<Diagnostic>,
        ),
        ("listing n diagnostics of operands on one line", operands),
    ] {
        let made = scaling::inputs(n, make);
        let bytes = |k: usize| listing(&made[&k]).len();
        scaling::hold(what, "bytes", bytes(n) as u64, bytes(large) as u64, 1);
        scaling::check(what, n, |k| {
            std::hint::black_box(listing(&made[&k]));
        });
    }
}
