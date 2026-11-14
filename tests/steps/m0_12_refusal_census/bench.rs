//! The census's own work, finding the kinds of n diagnostics and counting them by kind, is O(n)
//! in the diagnostics times the kinds: one pass over each text per kind, and one pass over the
//! census lines per kind for the totals. The checker's work on each unit is measured by the
//! scaling tests of its own steps. The benchmark of this step, run by
//! `tools/run_tests.sh --bench`. The check asserts nothing besides its ratio: finding kinds is
//! checked by `kinds_are_found_by_their_phrases`, and the lines and totals by the snapshots.

use super::{kinds, line, totals};

#[test]
fn classifying_and_counting_scale_linearly() {
    let texts = zed_tests::scaling::inputs(200, |n| {
        (0..n)
            .map(|i| {
                let k = &kinds::KINDS[i % kinds::KINDS.len()];
                format!(
                    "unit {i}: the check of `f{i}` was not decided: {}.",
                    k.phrase
                )
            })
            .collect::<Vec<String>>()
    });
    zed_tests::scaling::check("census of n diagnostics", 200, |n| {
        let mut out = String::new();
        for (i, t) in texts[&n].iter().enumerate() {
            line(
                &mut out,
                &format!("u{i}"),
                "1:1",
                "warning",
                &kinds::of(t),
                t,
            );
        }
        std::hint::black_box(totals(&out));
    });
}
