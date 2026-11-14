//! `n` parcel checks in a row, each a derived node whose certificate compares with `>` and
//! `>=`: legalization's work is linear in the graph. The small instance is in `legalize.rs`.

use std::sync::Mutex;

use zed_tests::scaling;
use zedc::zir::Region;

use crate::legalize::parcel_checks;

#[test]
fn legalization_is_linear_in_the_graph() {
    let n = 110_000;
    let (small_runs, large_runs) = scaling::Meter::new().runs();
    let pool = |k: usize, runs: usize| Mutex::new((0..runs).map(|_| parcel_checks(k)).collect());
    let (small, large): (Mutex<Vec<Region>>, Mutex<Vec<Region>>) =
        (pool(n, small_runs), pool(scaling::FACTOR * n, large_runs));
    scaling::check("legalizing parcel checks", n, |k| {
        let pool = if k == n { &small } else { &large };
        let g = pool.lock().expect("no run panicked").pop();
        drop(zed_native::legalize(g.expect("a graph built for each run")));
    });
}
