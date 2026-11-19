//! The scaling benchmark of plan row REMAP-map-tests, run apart from the correctness tests
//! (`tools/run_tests.sh --bench`), at n and 8n: the whole path (parse, check, elaboration and
//! the reference evaluator's run) of one composed form, a `map` at the leaves, a transpose that
//! folds the new inner level by `><`, and a `map` of the result.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::value;

/// Entries of the family.
const N_ENTRIES: usize = 2_000;

/// n entries in rows of 10, `[[0, …, 9], [10, …, 19], …]`.
fn rows(n: usize) -> String {
    let rs = (0..n / 10)
        .map(|r| {
            let xs = (0..10)
                .map(|j| (r * 10 + j).to_string())
                .collect::<Vec<_>>();
            format!("[{}]", xs.join(", "))
        })
        .collect::<Vec<_>>();
    format!("[{}]", rs.join(", "))
}

#[test]
fn map_transpose_fold_map_runs_in_linear_time() {
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "m = {};\n\
             x = (m.map(r -> r.map(v -> v + 1)) as (i -> j -> v) into (j -> i >< (+) -> v)).map(s -> s * 2);\n\
             t = x.sum;\n",
            rows(n)
        )
    });
    let run = |n: usize| {
        // Each of the n entries v + 1 summed, then doubled: 2 · (n(n-1)/2 + n).
        assert_eq!(value(&srcs[&n], "t"), (n * (n - 1) + 2 * n).to_string());
    };
    scaling::check(
        "`m.map` at the leaves of n entries in rows of 10, a transpose folding the rows, a `map` \
         of the result, whole path",
        N_ENTRIES,
        run,
    );
}
