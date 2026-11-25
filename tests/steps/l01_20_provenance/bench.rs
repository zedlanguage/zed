//! The benchmarks of provenance, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-rest). Each check they make besides the ratio is made at small sizes in
//! `scaling.rs`.

use zed_tests::scaling::{check, check_proved_cost, inputs};

use crate::scaling::{
    countdown, finds_the_origins_of_each_member, finds_the_term_of_every_fact, product_of_atoms,
    records_the_recursion, sum_of_ones,
};

#[test]
fn recording_a_deep_recursion_scales() {
    // Each fact copied the call sites it was inside: the facts of a recursion of depth `n`
    // held `n²/2` of them.
    let terms = inputs(1000, countdown);
    check("the provenance of a recursion, by depth", 1000, |n| {
        records_the_recursion(&terms[&n], n);
    });
}

#[test]
fn the_term_of_every_fact_scales() {
    // The term at a node is found by walking the term in preorder to its position, so
    // reading the term of each of the `O(n)` facts of an `n`-node term one at a time took
    // `O(n²)` steps (ratio 61). `fact_terms()` finds each distinct position once, from its
    // parent.
    let terms = inputs(1000, sum_of_ones);
    check("the term at each fact, by term size", 1000, |n| {
        finds_the_term_of_every_fact(&terms[&n], n);
    });
}

#[test]
fn the_origins_of_a_failure_with_many_members_scale() {
    // The product of `n` distinct loose atoms: its `#errs` has `n` members, each first
    // appearing at its literal. Each member's search tested every input fact by walking its
    // value, an `#errs` of up to `n` members: `O(n² log n)` steps (11.1 times the bytes at 64
    // and 512 on cdf07ac4f).
    //
    // The cost now is at most a constant times `members_log_members_times_levels(n)`,
    // `n log2(n) L(n)` for `L(n)` the levels of an `IdSet` of `n` members (`idset.rs`: one leaf
    // holds 4096 numbers, each level above it 64 times more), proof:
    // 1. The product is a balanced tree of `n - 1` products, so it has `O(n)` facts, each
    //    reading two inputs, and each fact at a node of `s` atoms holds an `#errs` family of `s`
    //    members, made from its larger operand's by `Family::extend`. A member is in the
    //    smaller operand at most once per level of the tree, so the members added over all the
    //    facts number at most `n log2 n`, and the families' entries `n (log2 n + 1)`.
    // 2. `Value::merge_failures` builds each family from its operands in `O(s)` by the sorted
    //    merge of `Family::extend`, `O(n log n)` over the tree (kernel bench
    //    `merging_a_balanced_tree_of_failures_scales`).
    // 3. `origins` reads each family once (`Held::seen`), oldest first, as a difference from
    //    the family it was made from (`Held::base`): the shallow difference walks the `s`
    //    entries of both maps, which the sorted merge rebuilt and so share no nodes, and yields
    //    the added members, each entered into the tally with `IdSet::insert`, `L(n)` node
    //    steps; with step 1, `O(n log n)` compares and `O(n log n · L(n))` node steps. The sort
    //    of `reached` and the ordered `traced` map add `O(n log n)`.
    // 4. The backward pass intersects, at each of the `O(n)` facts, its set with each input's;
    //    the larger input's set shares every node but those its sibling's members changed, so
    //    the intersections read 64 slots on each of the `L(n)` levels of the paths where the
    //    two differ, `O(n L(n) + n log n / 64)` words over the tree.
    // Every term is at most a constant times `n log2(n) L(n)`, so the ratio of the work at 8n
    // to that at n is at most the largest ratio of the terms, that of `n log2(n) L(n)`. The
    // members are numbered by `u32`, so `L(n) ≤ 5` and the cost is O(n log n). The sizes 4096
    // and 32,768 hold the step where the sets gain their second level: there that ratio is
    // `8 · (15 / 12) · 2 = 20`, and 10.0 where `L` does not change (512 and 4096: 10.67, over
    // the limit 10.5 that `check` holds). Measured on b24-scale1: 9.45 times the work at 512
    // and 11.57 at 4096 (bytes 9.8 and 10.1), so the terms that grow with `L` are a small
    // share. Before SCALE-near-prov-members a tally entered each one-member set by a union that
    // allocated a new node on each level where the two differ: with that union put back, 84.4 MB
    // and 967.8 MB at 4096 and 32,768 against 75.8 MB and 765.6 MB (12.14 times the work, under
    // the limit 20). This bench cannot catch that variant: its cost has the order of the
    // proof, a larger constant only, so its ratio stays under the proved bound. The kernel test
    // `a_tally_enters_one_member_sets_in_place_at_flat_bytes_a_member` catches it by the bytes a
    // member, 254 in place and 1,230 by the union at 4,096, against a bound of 512
    // (PROV-negative-control-weak).
    let cost = members_log_members_times_levels;
    assert_eq!(cost(32_768) / cost(4096), 20.0);
    let terms = inputs(4096, product_of_atoms);
    check_proved_cost(
        "the origins of an n-member failure, by n",
        4096,
        ("n log2(n) L(n)", members_log_members_times_levels),
        |n| finds_the_origins_of_each_member(&terms[&n], n),
    );
}

/// `n log2(n) L(n)`, for `L(n)` the levels of an `IdSet` of the numbers below `n`: one leaf
/// holds 4096, and each level above it 64 times as many (`idset.rs`, `LEAF_BITS` 12 and
/// `FAN_BITS` 6).
fn members_log_members_times_levels(n: usize) -> f64 {
    let (mut levels, mut held) = (1, 4096);
    while held < n {
        (levels, held) = (levels + 1, held * 64);
    }
    n as f64 * (n as f64).log2() * levels as f64
}
