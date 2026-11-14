//! The benchmarks of `cells.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `cells.rs`.

use super::*;

/// A decision tree of `2c + 1` arms of `c` components, in the column order `place` gives,
/// decided at `c` and `8c` on a thread of its own.
///
/// The input has `2c + 1` arms of `c` components: `N ≈ 2c²`, so work linear in `N` is of
/// order 2 in `c`. The table before this one kept a cell for every arm on every column, and
/// tested each arm apart: 121 G instructions at `c = 1024`, against 8.0 G now, both 4 times
/// per doubling of `c`, in either column order. A prefix trie of the arms was `c^2.93` with
/// the columns reversed. The types are built before the runs, and each run forgets what was
/// decided, so it measures the decision alone.
///
/// TEST-bench-move-l0123, author P169: this was one test,
/// `a_decision_tree_is_decided_in_time_linear_in_its_size`, deciding both column orders at
/// c = 32 (the run at 8c 64 times the run at c, about 0.12 s); each order is now a test of its
/// own, sized so that the run at 8c takes about 3 s.
fn decided_in_time_linear_in_its_size(c: usize, reversed: bool, what: &'static str) {
    std::thread::Builder::new()
        .spawn(move || {
            let built: BTreeMap<usize, Type> = [c, scaling::FACTOR * c]
                .into_iter()
                .map(|c| {
                    let place = |i: usize| if reversed { c - 1 - i } else { i };
                    let (p, rows) = arms(c, 1000 * c, place);
                    (c, &p - &Type::union_all(rows))
                })
                .collect();
            scaling::check_order(what, c, 2, |c| {
                Type::forget_emptiness();
                assert!(
                    built[&c].is_empty(),
                    "the arms cover the scrutinee at c = {c}"
                );
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// TEST-bench-move-l0123, author P169: c was 32, now 160; 1x 41.4 ms at load 27.
#[test]
fn a_decision_tree_is_decided_in_time_linear_in_its_size() {
    decided_in_time_linear_in_its_size(160, false, "a decision tree, by column count");
}

/// TEST-bench-move-l0123, author P169: c was 32, now 160; 1x 41.8 ms at load 27.
#[test]
fn a_decision_tree_with_its_columns_reversed_is_decided_in_time_linear_in_its_size() {
    decided_in_time_linear_in_its_size(
        160,
        true,
        "a decision tree with its columns reversed, by column count",
    );
}
