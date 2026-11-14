//! Release follows the counts of the data graph: recording the order of the frees costs O(1)
//! per free, natively and in the heap. The small instances are in `release_order.rs`.

use zed_kernel::{Evaluator, World};
use zed_tests::scaling;
use zedc::zir::lower::lower;
use zedc::zir::memory;

use crate::release_order::{many, texts, tuples_dropped};

#[test]
fn recording_the_release_order_scales() {
    // O(1) per free: T(8n)/T(n) of a run of `many(n)` with the record on, compiled first.
    scaling::on_a_thread(256 << 20, || {
        let made = scaling::inputs(1_200, |m| {
            let t = many(m);
            let g = zed_native::legalize(lower(&t).unwrap_or_else(|e| panic!("{e}")));
            let p = memory::plan(g.graph(), true);
            (g, p)
        });
        scaling::check(
            "the native run of n early values, with its frees recorded",
            1_200,
            |m| {
                let (g, p) = &made[&m];
                zed_native::record_releases(true);
                let o = zed_native::run(g, p, &mut Evaluator::new(World::new())).unwrap();
                zed_native::record_releases(false);
                std::hint::black_box((o, zed_native::counted()));
            },
        );
    });
}

#[test]
fn the_heaps_record_of_frees_scales() {
    // O(1) per free: T(8n)/T(n) of making and freeing n tuples of two strings, record on.
    let made = scaling::inputs(500_000, texts);
    scaling::check(
        "making and freeing n tuples of two strings, frees recorded",
        500_000,
        |m| {
            std::hint::black_box(tuples_dropped(&made[&m]));
        },
    );
}
