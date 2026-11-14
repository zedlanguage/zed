//! The benchmarks of the kernel reference evaluator, run by `tools/run_tests.sh --bench` and
//! left out of its default run (TEST-bench-move-rest). Each check they make besides the ratio
//! is made at small sizes by a correctness test of the module whose name each file bears. The
//! one here, a chain read by `-0.0` keys, is checked by the root module's
//! `a_chain_read_by_negative_zero_keys_is_defined_at_small_sizes`. The benchmarks of deep
//! values are a program of their own, `deep_scaling.rs`, whose module is
//! `bench/deep_scaling.rs`; this module does not include it.

mod deep;
mod empty_levels;
mod nested_calls;
mod provenance;
mod scaling;
mod shared;

use zed_kernel::Schedule;
use zed_tests::scaling::check_order;

use crate::{neg_zero_chain, neg_zero_chain_is_defined};

/// A chain of `n` entries, each reading the one before by a key that holds `-0.0`. Each read is a
/// search of an ordered family, O(log n), so the chain is O(n log n): 8 (log 8n / log n) times
/// the work at 8n, 10.41 at n = 1000 (measured 10.0 to 10.5, failing in runs of the whole step)
/// and 10.0 at n = 4000, the size used.
#[test]
fn reads_by_a_key_holding_negative_zero_scale() {
    const N: usize = 4_000;
    let (small, large) = (neg_zero_chain(N), neg_zero_chain(8 * N));
    for schedule in [Schedule::Rounds, Schedule::Pull] {
        check_order("a chain read by -0.0 keys", N, 1, |n| {
            let t = if n == N { &small } else { &large };
            neg_zero_chain_is_defined(t, schedule, n);
        });
    }
}
