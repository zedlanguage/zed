//! The benchmarks of `nest_empty.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::nest_empty::*;
use zed_tests::scaling::{self};
use zedc::store::presburger::{project_each, satisfiable};

#[test]
fn a_nest_whose_every_path_is_empty_costs_its_depth() {
    // Each part is read once, and each hull is the one it is made from with a few forms
    // changed, O(log n) each (COMPLEXITY.md PRES-nest-empty).
    costs("a nest every path of which is empty", 1500, empty);
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
    costs("a chain of two tests held by both", 1250, chain);
}

#[test]
fn a_chain_of_two_tests_held_by_both_bounding_one_side_costs_its_depth() {
    costs(
        "a chain of two tests held by both, bounding one side",
        860,
        chain_one_side,
    );
}

#[test]
fn a_chain_of_two_tests_with_atoms_of_their_own_costs_its_depth() {
    costs(
        "a chain of two tests with atoms of their own",
        64,
        chain_two_atoms,
    );
}

#[test]
fn two_tests_each_held_by_both_at_the_level_above_cost_their_depth() {
    costs("two tests held by both disjuncts of both", 1000, pair);
}

#[test]
fn a_nest_is_projected_in_a_stack_its_depth_does_not_grow() {
    // An unusual stack and depth, so a benchmark (author P178); the answers at ordinary depths
    // are in `nest_empty::a_nest_with_one_path_that_has_a_point_is_projected_onto_it`.
    // The projection read each level of the nest by a recursive call, about 3.9 kB of stack
    // for each, so the nest of 512 levels overflowed a test thread's 2 MiB stack under some
    // builds, and a 256 KiB stack at about 60 levels. The levels are now kept on an explicit
    // stack (item MAIN-l01_38-failures). The answers are those of
    // `nest_empty::a_nest_whose_every_path_is_empty_is_answered_false_at_every_depth`, and of the
    // point's own values for the nest that has one.
    let run = || {
        for k in [64, 512] {
            let (each, left_out) = project_each(&empty(k), &[v("x0"), v("z")]).expect("answered");
            assert!(left_out.is_empty(), "depth {k}: {left_out:?}");
            assert!(
                each.iter().all(|p| p.as_ref().is_ok_and(|s| s.is_empty())),
                "depth {k}: {each:?}"
            );
        }
        let (each, left_out) = project_each(&near(512), &[v("x0"), v("z")]).expect("answered");
        assert!(left_out.is_empty(), "{left_out:?}");
        let one = |n: i64| zedc::store::interval::IntervalSet::of(n, n);
        assert_eq!(each, vec![Ok(one(1)), Ok(one(1))]);
    };
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(run)
        .expect("a thread")
        .join()
        .expect("answered in a 256 KiB stack");
}
