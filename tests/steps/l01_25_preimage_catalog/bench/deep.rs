//! The transfer of a deep term, its frames on the heap, costs O(depth) (PRE-stack-explicit).
//! Each term is built before the timing, on a 2 MiB stack; `deep.rs` checks the preimages of
//! the same terms a few levels deep on the default stack, and the tests below check them 10,000
//! deep on a 2 MiB stack.

use zed_kernel::Term;
use zed_tests::scaling;
use zedc::store::preimage::{Demand, preimage};

use crate::deep::{ifs, lets, sum};
use crate::{doms, shown};

/// The default stack of a test thread.
const STACK: usize = 2 << 20;

/// Runs `f` on a thread with a 2 MiB stack, whatever `RUST_MIN_STACK` says.
fn on_small_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .expect("a test thread")
        .join()
        .expect("the test passes on a 2 MiB stack");
}

/// The preimage of `make` at depths `n` and `8n`.
fn scales(what: &'static str, n: usize, make: fn(usize) -> Term) {
    on_small_stack(move || {
        let made = scaling::inputs(n, make);
        let d = doms(&[("i", Some(-50), Some(50))]);
        scaling::check(what, n, |k| {
            preimage(&made[&k], &d, &Demand::Bool(true));
        });
    });
}

#[test]
fn a_deep_sum_costs_linear_work_in_its_depth() {
    scales("the preimage of a deep sum", 12_500, sum);
}

#[test]
fn a_deep_chain_of_lets_costs_linear_work_in_its_depth() {
    scales("the preimage of a deep chain of lets", 6_250, lets);
}

#[test]
fn deep_ifs_cost_linear_work_in_their_depth() {
    scales("the preimage of deep ifs", 3_125, ifs);
}

/// How deep the terms of the checks below are: before PRE-stack the transfer overflowed a 2 MiB
/// stack at depth 3,000, so 10,000 leaves room for smaller frames. These were tests in `deep.rs`
/// until TEST-bench-move-l0125 (author P178: a test that needs an unusual depth or stack is a
/// benchmark).
const DEEP: usize = 10_000;

/// The preimage of `true` under `make(DEEP)` for `i` in `[-50, 50]`, on a 2 MiB stack.
fn deep(make: fn(usize) -> Term, expected: &'static str) {
    on_small_stack(move || {
        let t = make(DEEP);
        let p = preimage(
            &t,
            &doms(&[("i", Some(-50), Some(50))]),
            &Demand::Bool(true),
        );
        assert_eq!(shown(&p), expected);
    });
}

#[test]
fn a_sum_10000_deep_has_its_preimage_on_a_2_mib_stack() {
    deep(sum, "i [0..=50]; exact");
}

#[test]
fn a_chain_of_10000_lets_has_its_preimage_on_a_2_mib_stack() {
    deep(lets, "i [0..=50]; exact");
}

#[test]
fn ifs_nested_10000_deep_have_their_preimage_on_a_2_mib_stack() {
    deep(ifs, "i [-50..=50]; exact");
}
