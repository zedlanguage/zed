//! The benchmarks of `cells.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `cells.rs`.

use super::*;

#[test]
fn a_decision_tree_is_decided_in_time_linear_in_its_size() {
    // The input has `2c + 1` arms of `c` components: `N ≈ 2c²`, so work linear in `N` is of
    // order 2 in `c`. The table before this one kept a cell for every arm on every column, and
    // tested each arm apart: 121 G instructions at `c = 1024`, against 8.0 G now, both 4 times
    // per doubling of `c`, in either column order. A prefix trie of the arms was `c^2.93` with
    // the columns reversed. The types are built before the runs, and each run forgets what was
    // decided, so it measures the decision alone.
    std::thread::Builder::new()
        .spawn(|| {
            for reversed in [false, true] {
                let built: BTreeMap<usize, Type> = [32, 256]
                    .into_iter()
                    .map(|c| {
                        let place = |i: usize| if reversed { c - 1 - i } else { i };
                        let (p, rows) = arms(c, 1000 * c, place);
                        (c, &p - &Type::union_all(rows))
                    })
                    .collect();
                let what = if reversed {
                    "a decision tree with its columns reversed, by column count"
                } else {
                    "a decision tree, by column count"
                };
                scaling::check_order(what, 32, 2, |c| {
                    Type::forget_emptiness();
                    assert!(
                        built[&c].is_empty(),
                        "the arms cover the scrutinee at c = {c}"
                    );
                });
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
