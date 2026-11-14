//! The bytes and the work of rendering `n` steps on one line, at `n` and `8n` (`layout.rs`).

use zed_tests::scaling;

use crate::layout::{diagnostic, literals, summed, sums, terms};
use crate::rejected;

/// Holds the bytes of `text(k)` at `n` and `8n` to order n, then the work of making them.
fn rendered(what: &str, n: usize, text: impl Fn(usize) -> String + Sync) {
    let large = scaling::FACTOR * n;
    scaling::hold(
        what,
        "bytes",
        text(n).len() as u64,
        text(large).len() as u64,
        1,
    );
    scaling::check(what, n, |k| {
        std::hint::black_box(text(k));
    });
}

/// Each line is shown once, and a row of underlines is at most as long as the line and its
/// numbers, so `n` steps on one line print O(n) bytes, not a copy of the line for each step.
#[test]
fn rendering_many_steps_on_one_line_scales() {
    let n = 1000;
    let made = scaling::inputs(n, |k| diagnostic(terms(k)));
    rendered("rendering n steps on one line", n, |k| made[&k].to_string());
}

#[test]
fn rejecting_a_line_of_many_literals_scales() {
    let n = 300;
    let srcs = scaling::inputs(n, literals);
    rendered("rejecting a line of n literals", n, |k| rejected(&srcs[&k]));
}

/// A sum `a0 + … + an` whose every partial sum is a step nests n deep on one line; drawn by
/// their ends, the sums take a few rows, not n, so the line's quote costs O(n) bytes, not
/// O(n²).
#[test]
fn rendering_a_line_of_nested_sums_scales() {
    let n = 1000;
    let made = scaling::inputs(n, |k| diagnostic(sums(k)));
    rendered("rendering n nested sums on one line", n, |k| {
        made[&k].to_string()
    });
}

#[test]
fn rejecting_a_line_of_nested_sums_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, summed);
    rendered("rejecting a line of n nested sums", n, |k| {
        rejected(&srcs[&k])
    });
}
