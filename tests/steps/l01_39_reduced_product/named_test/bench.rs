//! Benchmarks of `named_test`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn arms_of_a_named_rule_at_each_tier_take_time_near_linear_in_the_depth() {
    // Depths 120 and 960. At 30 and 240, before TEST-bench-move, with the rule's formula copied
    // at each tier the work grew 43 times (1.25 to 54.0 billion instructions); shared, it grows
    // 7.7 times.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            let tests: BTreeMap<usize, Term> = [120, 960]
                .map(|d| (d, if_(named(d), lit(1), lit(2))))
                .into();
            let scope = ints(&names());
            scaling::check(
                "arms of a rule named once, used at each of d tiers",
                120,
                |d| {
                    std::hint::black_box(arms(&tests[&d], &scope));
                },
            );
        })
        .expect("a thread")
        .join()
        .expect("the test passes");
}

#[test]
fn arms_of_a_wide_named_conjunction_at_each_tier_take_time_near_linear_in_the_depth() {
    // k = d credit limits named once and required at each of d tiers. Measured on the branch
    // of ST-formula-share, in instructions at d = 30, 60, 120, 240: 1.18, 3.87, 14.8, 59.0 G
    // (about 4 times per doubling); written out at each tier 12.1, 56.0, 251 G at d = 30 to
    // 120. That code flattened the shared conjunction into each tier's conjunction; on
    // origin/main ae9b63e9 this test fails at 36.4 times the bytes (limit 24). `Formula::and`
    // now keeps the named conjunction whole and `Parts::of` reads it once: 10.0 times the
    // instructions and 8.8 times the bytes from d = 30 to 240.
    wide_scaling(
        "arms of k = d credit limits named once, required at each of d tiers",
        approval_within,
    );
}

#[test]
fn arms_of_a_wide_named_disjunction_at_each_tier_take_time_near_linear_in_the_depth() {
    // k = d exemptions named once, any of which approves at each of d tiers. Measured on the
    // branch of ST-formula-share, in instructions at d = 30, 60, 120, 240: 0.37, 1.14, 3.88,
    // 14.2 G (3.1 to 3.7 times per doubling); written out at each tier 7.5, 33.7, 150 G at
    // d = 30 to 120. That code flattened the shared disjunction into each tier's disjunction;
    // on origin/main ae9b63e9 this test fails at 41.6 times the bytes. `Formula::or` now keeps
    // the named disjunction whole: 13.9 times the instructions and 12.3 times the bytes.
    wide_scaling(
        "arms of k = d exemptions named once, any of which approves at each of d tiers",
        approval_exempt,
    );
}

#[test]
fn arms_of_a_wide_named_disjunction_required_at_each_tier_take_time_near_linear_in_the_depth() {
    // Any one of k = d credit limits, named once, required of a small request at each of d
    // tiers. Measured by ST-formula-share verify#2, in instructions at d = 30, 60, 120, 240:
    // 2.76, 10.4, 40.2, 157.6 G (3.8 times per doubling), 0.73 to 39.6 GB allocated; written
    // out at each tier, d = 30, 60 and 120 did not finish in 300 s together. The test fails at
    // 54.1 times the bytes (limit 24) on origin/main ae9b63e9. `Parts::of` now makes the
    // disjunction once and skips it at each tier below the first that conjoined it: 9.7 times
    // the instructions and 8.9 times the bytes.
    wide_scaling(
        "arms of any of k = d credit limits named once, required at each of d tiers",
        approval_any_limit,
    );
}

#[test]
fn arms_of_a_chain_of_named_conjunctions_take_time_near_linear_in_its_length() {
    // With the named conjunctions kept whole, and `project_parts` and `Conjuncts::and` reading
    // a shared part at each path to it, 82 s at d = 28 (about 1.618 to the d); read once,
    // 10.6 times the instructions and 11.1 times the bytes from d = 30 to 240. Without the
    // `project_parts` memo it did not finish in 100 s.
    chain_scaling(
        "arms of d names, each the conjunction of the two before it",
        and2,
    );
}

#[test]
fn arms_of_a_chain_of_named_disjunctions_take_time_near_linear_in_its_length() {
    // Read once per base and symbols in `project_parts`, 7.6 times the instructions and the
    // bytes from d = 30 to 240. Without that memo it did not finish in 100 s, and on
    // origin/main ae9b63e9 it did not finish in 150 s.
    chain_scaling(
        "arms of d names, each the disjunction of the two before it",
        either,
    );
}

#[test]
fn arms_of_a_named_conjunction_of_k_limits_take_time_near_linear_in_k() {
    // The translator made the conjunction of each prefix of `l0 && l1 && ...` in turn, copying
    // and tightening the prefix again at each limit: k² (ST-formula-k2). At k = 240 and 1920, on
    // origin/main 64781908 this test fails at 39.8 times the bytes (0.47 to 18.7 GB; limit 24;
    // at k = 120 and 960 only 27.7 times). Joined in one pass (`Tx::chain`): 1.16 to 9.61 G
    // instructions (8.3 times) and 7.6 times the bytes, 2.4 s.
    limit_scaling(
        "arms of a conjunction of k credit limits named once",
        600,
        approval_within,
    );
}

#[test]
fn arms_of_a_named_disjunction_of_k_limits_take_time_near_linear_in_k() {
    // As for the conjunction, the disjunction of each prefix of `l0 || l1 || ...` was made in
    // turn (ST-formula-k2). At k = 240 and 1920, on origin/main 64781908 this test fails at 35.7
    // times the bytes (0.53 to 18.8 GB; at k = 120 and 960 only 25.3 times). Joined in one
    // pass: 1.21 to 9.41 G instructions (7.7 times) and 7.6 times the bytes, 2.6 s.
    limit_scaling(
        "arms of any of k credit limits named once, required of a small request",
        600,
        approval_any_limit,
    );
}

#[test]
fn arms_of_k_named_exemptions_take_time_near_linear_in_k() {
    // A disjunction of k exemptions beside the tier's own disjuncts (ST-formula-k2). On
    // origin/main 64781908 this test fails at 38.8 times the bytes (0.12 to 4.55 GB). Joined in
    // one pass: 0.29 to 2.36 G instructions (8.3 times) and 7.6 times the bytes.
    limit_scaling(
        "arms of any of k exemptions named once",
        600,
        approval_exempt,
    );
}

#[test]
fn arms_of_a_tier_needing_k_named_limits_take_time_near_linear_in_k() {
    // A conjunction of k limits as a conjunct of the tier's disjunct (ST-formula-k2). On
    // origin/main 64781908 this test fails at 36.5 times the bytes (0.12 to 4.37 GB). Joined in
    // one pass: 0.36 to 3.72 G instructions (10.4 times) and 8.7 times the bytes.
    limit_scaling(
        "arms of a tier needing k credit limits named once",
        480,
        approval_any_tier,
    );
}

#[test]
fn arms_of_named_limits_in_side_by_side_tiers_take_time_near_linear_in_the_depth() {
    // k = d credit limits named once, needed by each of d tiers side by side. Each disjunct
    // held the limits, and the projection read them in each: on origin/main d6d1840d, in
    // instructions at d = 30, 60, 120, 240: 0.834, 2.96, 11.5, 46.6 G (55.9 times), 0.128 to
    // 5.97 GB allocated (46.6 times). With the limits taken out of the disjunction
    // (`presburger::factored`): 0.267, 0.535, 1.08, 2.16 G (8.1 times), 0.044 to 0.350 GB
    // (8.0 times).
    wide_scaling(
        "arms of k = d credit limits named once, needed by each of d tiers side by side",
        approval_any_tier,
    );
}
