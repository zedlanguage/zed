//! The benchmarks of `cell_sweep.rs` (FAIL-pres-overlap-every-level-refused), run by
//! `tools/run_tests.sh --bench`.

use crate::cell_sweep::*;
use zed_tests::scaling;
use zedc::store::presburger::decide;

/// The chain whose guards overlap at every level, with a bound past its largest value or below
/// its smallest (no point), with and without the parameter `k`, at 400 levels and 3200, in work
/// linear in the levels (8.4 to 8.6 times the work). Control (once, not kept): with the bound
/// check in `sweep_involution` turned off, the later stages refuse the chain at 40 levels with
/// `Err(Disjuncts)` and run past 60 s at 400.
#[test]
fn overlap_at_every_level_with_a_bound_scales() {
    for k in [None, Some((0, 3))] {
        let family = mid(k, false);
        for below in [false, true] {
            let fs = scaling::inputs(400, |n| {
                let reached = family.reachable(n);
                let target = if below {
                    Target::Le(reached.first().expect("some value") - 1)
                } else {
                    Target::Ge(reached.last().expect("some value") + 1)
                };
                family.chain(n, target)
            });
            let what = format!(
                "decision of an overlapping chain, k {}, bound {}",
                if k.is_some() { "bounded" } else { "absent" },
                if below { "below" } else { "above" }
            );
            scaling::check_order(&what, 400, 1, |n| {
                assert_eq!(decide(&fs[&n]), Ok(false), "{n}");
            });
        }
    }
}
