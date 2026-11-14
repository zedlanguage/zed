//! The benchmarks of `deep.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::deep::*;
use std::collections::{BTreeMap, HashSet};
use zed_tests::scaling;
use zedc::store::presburger::{Formula, satisfiable};

#[test]
fn mapping_copying_comparing_printing_and_dropping_a_chain_cost_its_size() {
    // Each operation keeps one stack entry per level of the part it is in, so it costs O(n).
    let built: BTreeMap<usize, Formula> = [DEEP / 8, DEEP]
        .into_iter()
        .map(|n| (n, chain(n)))
        .collect();
    on_small_stack(move || {
        scaling::check_order(
            "a chain of guards mapped, copied, compared, hashed, printed and dropped",
            DEEP / 8,
            1,
            |n| {
                let f = &built[&n];
                let loose = f.map_cons(&loosen);
                let copy = f.clone();
                assert!(copy == *f && loose != *f);
                let set: HashSet<&Formula> = [f, &copy].into_iter().collect();
                std::hint::black_box((set.len(), f.to_string().len()));
            },
        );
    });
}

#[test]
fn deciding_a_chain_costs_its_size() {
    let built: BTreeMap<usize, Formula> = [DEEP / 8, DEEP]
        .into_iter()
        .map(|n| (n, chain(n)))
        .collect();
    on_small_stack(move || {
        scaling::check_order("a chain of guards decided", DEEP / 8, 1, |n| {
            std::hint::black_box(satisfiable(&built[&n]).is_ok());
        });
    });
}

#[test]
fn a_chain_of_guards_100000_deep_is_mapped_copied_compared_printed_decided_and_dropped() {
    // The depth and the stack are unusual sizes, so this is a benchmark (author P178); its
    // checks run at depth 30 in `deep::a_chain_of_guards_is_mapped_copied_compared_printed_decided_and_dropped`.
    on_small_stack(|| chain_checks(DEEP));
}
