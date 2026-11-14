//! How `step_targets` scales with the number of step folders: writing the targets, reading them
//! back and comparing them with the folders is O(n log n) in the folders. The benchmark of this
//! step, run by `tools/run_tests.sh --bench`; `scaling.rs` makes its check at small sizes.

use zed_tests::scaling::check;

use super::scaling::{names, round_trips, toml};

#[test]
fn step_targets_scales_with_the_number_of_folders() {
    let n = 2000;
    let inputs = [n, 8 * n].map(|m| (m, names(m)));
    let toml = toml();
    check("step_targets, by folders", n, |m| {
        let (_, folders) = inputs.iter().find(|i| i.0 == m).expect("a built size");
        round_trips(folders, &toml);
    });
}
