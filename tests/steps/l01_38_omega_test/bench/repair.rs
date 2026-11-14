//! The benchmarks of `repair.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::repair::*;
use zed_tests::scaling;
use zedc::store::presburger::{decide, satisfiable};

/// Each of the `k` repairs of the chain reads its two bounds of `i`, not the `k` guards on `i`
/// taken before it (LIN-cross: the guards made the search `k^2`, 134152 constraints read at
/// `k = 256` against 8968 at `k = 64`).
#[test]
fn a_chain_of_guards_on_one_input_scales() {
    let make = |n: usize| guards(n, n as i64, true);
    let (small, large) = (make(22000), make(22000 * scaling::FACTOR));
    for f in [&small, &large] {
        assert!(satisfiable(f).expect("answered").is_some());
    }
    scaling::check("satisfiable on a chain of k guards i >= j", 22000, |n| {
        drop(satisfiable(if n == 22000 { &small } else { &large }));
    });
}

/// The failed-literal search on the chain whose point is at an end stays near linear: each
/// disjunct that a point found so far meets is kept without a propagation (LIN-probe: the
/// search ran one full propagation per disjunct, `k^2.4` in all).
#[test]
fn a_chain_whose_point_is_at_an_end_scales() {
    let make = |n: usize| guards(n, n as i64 - 2, false);
    let (small, large) = (make(490), make(490 * scaling::FACTOR));
    scaling::check(
        "decide on a chain of k guards with its point at an end",
        490,
        |n| {
            assert_eq!(decide(if n == 490 { &small } else { &large }), Ok(true));
        },
    );
}
