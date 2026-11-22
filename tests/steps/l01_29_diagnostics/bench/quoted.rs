//! `n` diagnostics on one line, rendered and listed at `n` and `8n` (`quoted.rs`).

use zed_tests::scaling;
use zedc::front::Diagnostic;

use crate::quoted::{
    failing_sum, listing, many_errors_rendered_on_one_line, operands, refused_chain, sums,
};
use crate::rejected;

#[test]
fn rendering_many_errors_on_one_line_scales() {
    // The sum gives one diagnostic per component, each with seven steps, so the listing is
    // O(n) once the line is shown once.
    let n = 1000;
    let inputs = scaling::inputs(n, failing_sum);
    scaling::check("n errors of `sum` on one line of n components", n, |k| {
        many_errors_rendered_on_one_line(&inputs[&k]);
    });
}

#[test]
fn listing_many_diagnostics_on_one_line_scales() {
    let n = 3800;
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

#[test]
fn a_chain_of_refused_operations_scales() {
    // Each error of the chain names the error before it in one step, so the listing is O(n)
    // bytes (DERIV-never-chain-quadratic: 65.4 times the bytes at 8n before).
    let n = 100;
    let made = scaling::inputs(n, refused_chain);
    let bytes = |k: usize| rejected(&made[&k]).len();
    scaling::hold(
        "the listing of a chain of n refused `+`",
        "bytes",
        bytes(n) as u64,
        bytes(scaling::FACTOR * n) as u64,
        1,
    );
    scaling::check("checking a chain of n refused `+`", n, |k| {
        std::hint::black_box(rejected(&made[&k]));
    });
}
