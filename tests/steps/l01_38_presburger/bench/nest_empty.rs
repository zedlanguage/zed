//! The benchmarks of `nest_empty.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::nest_empty::*;
use zed_tests::scaling::{self};
use zedc::store::presburger::satisfiable;

#[test]
fn a_nest_whose_every_path_is_empty_costs_its_depth() {
    // Each part is read once, and each hull is the one it is made from with a few forms
    // changed, O(log n) each (COMPLEXITY.md PRES-nest-empty).
    costs("a nest every path of which is empty", empty);
    let built = scaling::inputs(64, near);
    scaling::check_order(
        "a nest with one path that has a point, its point found",
        64,
        1,
        |n| {
            std::hint::black_box(satisfiable(&built[&n]).is_ok());
        },
    );
}

#[test]
fn a_chain_of_two_tests_held_by_both_costs_its_depth() {
    costs("a chain of two tests held by both", chain);
}

#[test]
fn a_chain_of_two_tests_held_by_both_bounding_one_side_costs_its_depth() {
    costs(
        "a chain of two tests held by both, bounding one side",
        chain_one_side,
    );
}

#[test]
fn a_chain_of_two_tests_with_atoms_of_their_own_costs_its_depth() {
    costs(
        "a chain of two tests with atoms of their own",
        chain_two_atoms,
    );
}

#[test]
fn two_tests_each_held_by_both_at_the_level_above_cost_their_depth() {
    costs("two tests held by both disjuncts of both", pair);
}
