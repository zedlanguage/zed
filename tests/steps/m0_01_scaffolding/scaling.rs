//! The folders the benchmark of `bench.rs` writes as targets, and what writing them must give,
//! checked here at small sizes (TEST-bench-move-rest, P170).

use std::collections::BTreeSet;

use zed_tools::step_targets::{BEGIN, END, block, drift, splice, targets};

/// `n` folder names.
pub(super) fn names(n: usize) -> BTreeSet<String> {
    (0..n).map(|i| format!("l{i:06}_step")).collect()
}

/// A manifest with an empty block of targets.
pub(super) fn toml() -> String {
    format!("[package]\n{BEGIN}\n{END}\n[dev-dependencies]\n")
}

/// The targets of `folders`, written into `toml` and read back, have no drift from the folders.
pub(super) fn round_trips(folders: &BTreeSet<String>, toml: &str) {
    let written = splice(toml, &block(folders)).unwrap();
    assert!(drift(folders, &targets(&written).unwrap()).is_empty());
}

#[test]
fn the_targets_of_some_folders_are_written_and_read_back_without_drift() {
    for n in [0, 1, 2, 9] {
        round_trips(&names(n), &toml());
    }
}
