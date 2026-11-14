//! A value the kernel hands back is allocated with one cell per shared sequence, so a song
//! whose every verse sings the one below twice is `d` cells, made in time linear in `d`, by the
//! counting machine and by native code (COMPLEXITY.md R9). The small instances are in
//! `shared_values.rs`.

use zed_kernel::Evaluator;
use zed_tests::scaling;
use zedc::zir::memory;

use crate::planned;
use crate::shared_values::{looked_up, song, world};

/// The depth of the scaling tests, and 8 times it.
const D: usize = 450_000;

#[test]
fn the_machine_makes_a_shared_song_in_time_linear_in_its_verses() {
    let programs = scaling::inputs(D, |d| (world(&song(d)), planned(&looked_up())));
    scaling::check(
        "memory::run of a port giving d verses each held twice",
        D,
        |d| {
            let (w, (g, p)) = &programs[&d];
            let (_, s) = memory::run(g.graph(), p, &mut Evaluator::new(w.clone())).unwrap();
            assert_eq!(s.allocations, d as u64 + 2);
        },
    );
}

#[test]
fn native_code_makes_a_shared_song_in_time_linear_in_its_verses() {
    let programs = scaling::inputs(D, |d| (world(&song(d)), planned(&looked_up())));
    scaling::check(
        "native run of a port giving d verses each held twice",
        D,
        |d| {
            let (w, (g, p)) = &programs[&d];
            let o = zed_native::run(g, p, &mut Evaluator::new(w.clone())).unwrap();
            assert_eq!(o.stats.allocations, d as u64 + 2);
        },
    );
}
