//! The benchmarks of `front_cost.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::front_cost::*;
use zed_tests::scaling::{self, Meter};

/// At 256, 2,048 and 16,384 variables `decide` takes at most 1.5 times the instructions of
/// `integer_empty` on the same rows, and the ratio at each size is at most 1.15 times the ratio
/// at the size 8 times smaller: no factor that grows with the size. Before DECIDE-front-cost the
/// ratios were 3.95 and 4.64 at 256 and 2,048. Counts of processor time vary too much with load
/// for a limit of 1.15, so on a machine that cannot count instructions the test measures nothing.
#[test]
fn decide_on_unit_rows_costs_a_constant_times_the_search() {
    let mut meter = Meter::new();
    if meter.unit() != "instructions" {
        return;
    }
    let sizes = [
        256,
        256 * scaling::FACTOR,
        256 * scaling::FACTOR * scaling::FACTOR,
    ];
    let mut ratios = Vec::new();
    let mut report = String::from("decide against integer_empty, in instructions:");
    for n in sizes {
        let (d, u) = costs(&mut meter, n);
        let r = d as f64 / u as f64;
        report.push_str(&format!(" {d} / {u} = {r:.2} at {n} variables;"));
        ratios.push(r);
    }
    eprintln!("{report}");
    assert!(
        ratios.iter().all(|&r| r <= 1.5),
        "{report} more than 1.5 times"
    );
    assert!(
        ratios.windows(2).all(|w| w[1] <= 1.15 * w[0]),
        "{report} the ratio grows"
    );
}
