//! The transfer of a deep term, its frames on the heap, costs O(depth) (PRE-stack-explicit).
//! Each term is built before the timing, on a 2 MiB stack; `deep.rs` checks the preimages of
//! the same terms 10,000 deep.

use zed_kernel::Term;
use zed_tests::scaling;
use zedc::store::preimage::{Demand, preimage};

use crate::deep::{ifs, lets, on_small_stack, sum};
use crate::doms;

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
