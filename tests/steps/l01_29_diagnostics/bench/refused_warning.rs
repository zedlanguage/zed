//! `zedc test` on `n` refused questions, at `n` and `8n` (`refused_warning.rs`).

use zed_tests::scaling;

use crate::refused_warning::{many_placed_refusals, many_refusals, placed_refusals, refusals, unit};

/// A function whose scope places `2 n` refused questions, at its bound values and its reads:
/// placing them all is within n log n.
#[test]
fn many_placed_refusals_scale() {
    let n = 40;
    let files = scaling::inputs(n, |m| {
        unit("scale", &format!("placed{m}.zed"), &many_placed_refusals(m))
    });
    scaling::check(
        "zedc test on n refused values and n refused reads",
        n,
        |m| placed_refusals(&files[&m], m),
    );
}

/// A unit of `n` refused questions, one in each function: checking, placing and printing
/// together are within n log n. The files are written before the timing.
#[test]
fn many_refusals_scale() {
    let n = 40;
    let files = scaling::inputs(n, |m| unit("scale", &format!("{m}.zed"), &many_refusals(m)));
    scaling::check("zedc test on a unit of n refused questions", n, |m| {
        refusals(&files[&m], m);
    });
}
