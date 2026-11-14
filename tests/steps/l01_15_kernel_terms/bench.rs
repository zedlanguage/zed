//! The printer and the drop of terms at the rule of low complexity (DESIGN.md Part G): the
//! benchmarks of this step, run by `tools/run_tests.sh --bench` and left out of its default run
//! (TEST-bench-split). Each check they make besides the ratio has a small instance among the
//! correctness tests in `scaling.rs`. The benchmarks of `deep.rs` and `written.rs` are in
//! `bench/deep.rs` and `bench/written.rs` (TEST-bench-move-rest).

mod deep;
mod stack;
mod written;

use std::sync::Mutex;

use zed_kernel::Term;
use zed_kernel::print::pretty;
use zed_tests::scaling;

use super::scaling::{SHAPES, dropped_shapes, prefix_shape, shape};

#[test]
fn the_printer_scales_with_depth() {
    // Every node a broken layout visited computed its subtree's one-line text, and each level
    // of the one-line text copied the text of the level inside it.
    zed_tests::deep::on_small_stack(|| {
        for (k, what) in SHAPES.iter().enumerate() {
            let one_line = format!("one line, nested {what}, by depth");
            // A call's head was copied into the text of the call around it, a cost that
            // shows only past a few thousand levels. Between 8,000 and 16,000 levels of
            // heads the recursion leaves the cache, the cost per level stepping up from
            // 0.4 to 1.1 µs and flat again after, so both sizes are past it.
            let n = if k == 2 { 16_000 } else { 500 };
            zed_tests::scaling::check(&one_line, n, |d| {
                std::hint::black_box(shape(k, d).to_string());
            });
            // Broken, calls nested in argument position put depth `i` at indentation `2i`,
            // so their text is quadratic in the depth: they are measured by the text's
            // length, the depth growing as its square root.
            let (n, depth): (usize, fn(usize) -> usize) = match k {
                1 => (250_000, |m| m.isqrt()),
                _ => (500, |m| m),
            };
            let broken = format!("width 80, nested {what}, by text");
            zed_tests::scaling::check(&broken, n, |m| {
                std::hint::black_box(pretty(&shape(k, depth(m)), 80));
            });
        }
    });
}

#[test]
fn dropping_deep_and_wide_terms_scales() {
    // `Term`'s drop keeps the parts still to free on a heap stack (COMPLEXITY.md F62), each part
    // moved there once. Only the drop is measured: each run frees a term built before any run.
    let n = 12_500;
    zed_tests::deep::on_small_stack(|| {
        let (small_runs, large_runs) = scaling::Meter::new().runs();
        let pools = |k: usize, runs: usize| -> Vec<(&'static str, Mutex<Vec<Term>>)> {
            let built: Vec<_> = dropped_shapes(k)
                .into_iter()
                .map(|(what, t)| (what, Mutex::new(vec![t])))
                .collect();
            for _ in 1..runs {
                for ((_, pool), (_, t)) in built.iter().zip(dropped_shapes(k)) {
                    pool.lock().expect("no run panicked").push(t);
                }
            }
            built
        };
        let (small, large) = (pools(n, small_runs), pools(8 * n, large_runs));
        for ((what, s), (_, l)) in small.iter().zip(&large) {
            scaling::check(&format!("dropping {what}"), n, |k| {
                let pool = if k == n { s } else { l };
                drop(
                    pool.lock()
                        .expect("no run panicked")
                        .pop()
                        .expect("a term built for each run"),
                );
            });
        }
    });
}

#[test]
fn negations_and_indices_print_in_linear_time() {
    zed_tests::deep::on_small_stack(|| {
        let n = 2_000;
        for (k, what) in ["negations", "indices"].into_iter().enumerate() {
            let (small, large) = (prefix_shape(k, n), prefix_shape(k, 8 * n));
            scaling::check(&format!("one line, nested {what}, by depth"), n, |d| {
                let t = if d == n { &small } else { &large };
                std::hint::black_box(t.to_string());
            });
            scaling::check(&format!("width 80, nested {what}, by depth"), n, |d| {
                let t = if d == n { &small } else { &large };
                std::hint::black_box(pretty(t, 80));
            });
        }
    });
}

/// Item PRINT-group-site-defs: a term whose n type tests each write a part twice,
/// `is (int | #x{k}, int | #x{k})`, is written with n declarations before it, in time
/// linear in the term (COMPLEXITY.md K92). The text at a small n is checked by
/// `scaling::a_term_with_type_tests_that_write_a_part_twice_declares_each_part`.
#[test]
fn a_term_declaring_its_shared_parts_scales() {
    scaling::check_order(
        "a term with n type tests that each write a part twice",
        100,
        1,
        |n| {
            let text = super::scaling::declaring_shared_parts(n).to_string();
            assert_eq!(text.matches("type T").count(), n);
            std::hint::black_box(text);
        },
    );
}
