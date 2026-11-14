//! The evaluator's provenance walks (item T14-provenance, COMPLEXITY.md K25) at the rule of low
//! complexity: a run with provenance of shared branches, linear in the depth; the origins of a
//! chain of missing readings, of shared levels, of deep replacements and of growing entries,
//! and the check for repeated addresses, each linear in their size; and the origins of a
//! failure read beside a table holding none, constant in the table's rows. What each asserts
//! besides its ratio is checked at small sizes by
//! `provenance::the_origins_of_each_benchmark_run_are_found_at_small_sizes`.

use zed_kernel::{Provenance, Term, Value};
use zed_tests::scaling;

use crate::provenance::{
    deep_replacements, growing_entries, has_origins, late_beside_table, missing_chain,
    shared_branches, shared_levels, trace,
};

/// The provenance of the run of `make(m)` at `n` and at `FACTOR·n`, recorded before timing.
fn recorded(n: usize, make: impl Fn(usize) -> Term) -> Vec<(usize, Provenance)> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, trace(&make(m)).1))
        .collect()
}

/// The provenance recorded at `m`.
fn at(runs: &[(usize, Provenance)], m: usize) -> &Provenance {
    &runs
        .iter()
        .find(|(size, _)| *size == m)
        .expect("recorded")
        .1
}

#[test]
fn a_term_shared_by_both_branches_of_each_level_scales() {
    // The run takes `depth` branches, and a fact's position is its parent's and one child
    // index, so recording its provenance is `O(depth)`. Copying the term to one node per
    // position took `2^depth` steps (COMPLEXITY.md K25).
    let n = 3;
    let terms: Vec<(usize, Term)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, shared_branches(m)))
        .collect();
    scaling::check_order(
        "a run with provenance of shared branches, by depth",
        n,
        1,
        |m| {
            let (_, t) = terms.iter().find(|(size, _)| *size == m).expect("built");
            assert_eq!(trace(t).0, Value::Int(1));
        },
    );
}

#[test]
fn the_origins_of_a_failure_built_one_reading_at_a_time_scale() {
    // The `k`-th product's `#errs` set is made from the one before it by adding one member, so
    // the failures it holds are found from that set's by their difference, and the common
    // members of two sets likewise: `O(n log n)`. Reading every member of each set took
    // `O(n² log n)` (COMPLEXITY.md K25). The runs are recorded before timing.
    let n = 200;
    let runs = recorded(n, missing_chain);
    scaling::check_order(
        "the origins of a chain of n missing readings, by n",
        n,
        1,
        |m| has_origins(at(&runs, m), m),
    );
}

#[test]
fn the_check_for_repeated_addresses_on_a_chain_of_products_scales() {
    // A chain of n products is n deep, and two positions far apart in it are compared by a
    // walk up to their common ancestor; a set ordered by position made the check `O(n²)`
    // (54.7x at 250 vs 2000). Addresses are found by their hashes. The runs are recorded
    // before timing.
    let n = 250;
    let runs = recorded(n, missing_chain);
    scaling::check_order(
        "the check for repeated addresses on a chain of n products, by n",
        n,
        1,
        |m| assert!(at(&runs, m).repeated().is_empty()),
    );
}

#[test]
fn the_origins_of_a_failure_read_out_of_shared_levels_scale() {
    // The run takes `depth` steps, and the failures each value holds are found once per
    // distinct tuple and family, keyed by its id: `O(depth)`. Walking each value as a tree took
    // `2^depth` steps (COMPLEXITY.md K25). The runs are recorded before the timing.
    shared_levels_scale(2);
}

#[test]
fn the_origins_of_a_failure_read_out_of_deep_shared_levels_scale() {
    // Each level's family holds the level below it, so comparing two levels' maps compares
    // them whole: finding one level's set from another's by their difference made this
    // `O(depth²)`. A family's set is found that way only from a family it was made from.
    shared_levels_scale(128);
}

fn shared_levels_scale(n: usize) {
    let runs = recorded(n, shared_levels);
    scaling::check_order(
        "the origins of a failure read out of shared levels, by depth",
        n,
        1,
        |m| has_origins(at(&runs, m), 1),
    );
}

#[test]
fn the_origins_of_a_failure_under_deep_replacements_scale() {
    // Each of 32 steps replaces the entry at key 0 by a value `d` levels deep, so `d` nested
    // families change per step, each found from the one it was made from. Comparing their
    // values fully read each pair down to its difference, `O(d)` per level and `O(d²)` per
    // step; a shallow comparison makes it `O(d log n)` per step (COMPLEXITY.md K25). The
    // runs are recorded before timing.
    let d = 24;
    let runs = recorded(d, |m| deep_replacements(32, m));
    scaling::check_order(
        "the origins of a failure under 32 replacements d levels deep, by d",
        d,
        1,
        |m| has_origins(at(&runs, m), 33),
    );
}

#[test]
fn the_origins_of_a_table_of_growing_entries_scale() {
    // Entry `i` of table `f{i}` holds the `i` failures of entry `i - 1` and one more, and the
    // fact of each `let` meets the result's `n` failures with its table's set. Found newest
    // fact first, each set was read entry by entry and shared no nodes with the set it was
    // made from, so each meet and join cost its size, `O(n²)` in all; found oldest fact
    // first, each set is made from the last and each meet from the last meet, by their
    // differences (COMPLEXITY.md K25). The runs are recorded before timing.
    let n = 400;
    let runs = recorded(n, growing_entries);
    scaling::check_order(
        "the origins of a failure read out of n growing entries, by n",
        n,
        1,
        |m| has_origins(at(&runs, m), m),
    );
}

#[test]
fn the_origins_of_a_failure_read_beside_a_table_holding_none_cost_nothing_for_the_table() {
    // Found oldest fact first, the sets were found over every fact the failure's fact reaches,
    // so the table's `n` rows were read, `O(n log n)`; facts whose values hold no failure are
    // now left out, and the cost does not depend on `n` (COMPLEXITY.md K25). The runs are
    // recorded before timing.
    let n = 8000;
    let runs = recorded(n, late_beside_table);
    scaling::check_order(
        "the origins of a failure read beside a table of n rows holding none, by n",
        n,
        0,
        |m| has_origins(at(&runs, m), 1),
    );
}
