//! `min` and `max` of two tuples at the rule of low complexity: the kernel's walk and the
//! checker's join. The inputs are built in `tuple_min_max.rs`, whose test
//! `the_benchmark_inputs_give_their_results_at_a_small_size` checks each at a small size.
//!
//! Sizes: each check runs about 19 times its 1x case (a warm-up and two runs at n, two at 8n),
//! and building the inputs at n and 8n costs about as much again for the checker's units, which
//! are checked once when built. A test must end within about 15 s, so the checker's benchmarks
//! run 1x in about 0.25 to 0.35 s, below the 0.6 s other benchmarks take. Times are of
//! 2026-11-14 at a load of about 22 on 32 cores.

use zed_tests::scaling::{check, inputs};

use super::super::tuple_min_max::{
    chain_of_functions_meeting_a_literal_tuple, chain_of_functions_meeting_a_tuple,
    chain_of_tuple_mins, equal_tuples_of_shared_parts, min_of_tuples_nested,
    min_of_tuples_nested_through_shared_parts, min_of_tuples_of_n_components, pick,
    tuples_differing_last,
};

#[test]
fn min_of_two_tuples_of_n_components_scales() {
    // About 20 ns a component. Building the tuples costs far more than comparing them: at 2^22
    // components the test took 13 s for a 1x of 85 ms, so 2^21, a 1x of about 45 ms.
    let n = 1 << 21;
    let built = inputs(n, tuples_differing_last);
    check("`min` of two tuples of n components", n, |n| {
        let (a, b) = &built[&n];
        pick(true, a, b);
    });
}

#[test]
fn min_of_two_tuples_nested_n_deep_through_shared_parts_scales() {
    // Two equal tuples built apart are read to the end; the walk reads each pair of shared
    // parts once. 2^19 levels: 1x about 0.2 s, 1.1 GB allocated at 8n, 7 s in all.
    let n = 1 << 19;
    let built = inputs(n, equal_tuples_of_shared_parts);
    check("`min` of two tuples nested n deep", n, |n| {
        let (a, b) = &built[&n];
        pick(true, a, b);
    });
}

#[test]
fn checking_a_chain_of_n_tuple_mins_scales() {
    // About 0.2 ms and 0.19 MB a link: 1x about 0.32 s, 2.4 GB at 8n.
    let n = 1600;
    let built = inputs(n, chain_of_tuple_mins);
    check("checking n `min`s of tuples in a chain", n, |n| {
        built[&n].check();
    });
}

#[test]
fn checking_min_of_two_tuples_of_n_components_scales() {
    // About 90 µs and 0.11 MB a component: 1x about 0.29 s, 2.7 GB at 8n.
    let n = 3200;
    let built = inputs(n, min_of_tuples_of_n_components);
    check("checking `min` of two tuples of n components", n, |n| {
        built[&n].check();
    });
}

#[test]
fn checking_min_of_two_tuples_nested_n_deep_scales() {
    // 1x 0.61 s at a load of 43 (2026-11-14), about 0.25 s when idle. Building the unit at 8n
    // costs more than for the others; at 5000 levels the test ran past 20 s.
    let n = 2600;
    let built = inputs(n, min_of_tuples_nested);
    check("checking `min` of two tuples nested n deep", n, |n| {
        built[&n].check();
    });
}

#[test]
fn checking_min_of_two_tuples_nested_n_deep_through_shared_parts_scales() {
    // 2^n paths through n distinct types on each side, each joined once. About 85 µs a level:
    // 1x about 0.25 s; at 7000 levels the test ran past 20 s.
    let n = 3000;
    let built = inputs(n, min_of_tuples_nested_through_shared_parts);
    check(
        "checking `min` of two tuples nested n deep through shared parts",
        n,
        |n| {
            built[&n].check();
        },
    );
}

#[test]
fn checking_a_chain_of_n_functions_whose_parameter_meets_a_tuple_scales() {
    // Each class records the use of `a` by `min` once, and each call checks it once. About
    // 0.29 ms and 0.23 MB a function: 1x about 0.32 s, 2 GB at 8n.
    let n = 1100;
    let built = inputs(n, chain_of_functions_meeting_a_tuple);
    check(
        "checking n functions whose parameter meets a tuple in `min`",
        n,
        |n| {
            built[&n].check();
        },
    );
}

#[test]
fn checking_a_chain_of_n_functions_whose_parameter_meets_a_literal_tuple_scales() {
    // The class of `a` in `g{i}` meets `i + 1` distinct types through the chain. `min` joins
    // the shapes of its operands (DESIGN.md sec:reduction, item 5): its result is a variable a
    // call binds to that join, and a `min` of that result joins its operand into the same use,
    // so each function keeps one use and its result one shape. From 40 to 1280 links the work
    // grows 2.0 to 2.3 times per doubling, as for a chain whose results do not pass on; from
    // 1000 to 8000 it grew 8.03 times. 1x about 0.28 s, 1.9 GB at 8n.
    let n = 1000;
    let built = inputs(n, chain_of_functions_meeting_a_literal_tuple);
    check(
        "checking n functions whose parameter meets a literal tuple in `min`",
        n,
        |n| {
            built[&n].check();
        },
    );
}
