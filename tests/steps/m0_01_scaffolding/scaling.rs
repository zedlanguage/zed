//! How `step_targets` scales with the number of step folders: writing the targets, reading them
//! back and comparing them with the folders is O(n log n) in the folders.

use std::collections::BTreeSet;

use zed_tests::scaling::check;
use zed_tools::step_targets::{BEGIN, END, block, drift, splice, targets};

/// `n` folder names.
fn names(n: usize) -> BTreeSet<String> {
    (0..n).map(|i| format!("l{i:06}_step")).collect()
}

#[test]
fn step_targets_scales_with_the_number_of_folders() {
    let n = 2000;
    let inputs = [n, 8 * n].map(|m| {
        let toml = format!("[package]\n{BEGIN}\n{END}\n[dev-dependencies]\n");
        (m, names(m), toml)
    });
    check("step_targets, by folders", n, |m| {
        let (_, folders, toml) = inputs.iter().find(|i| i.0 == m).expect("a built size");
        let written = splice(toml, &block(folders)).unwrap();
        assert!(drift(folders, &targets(&written).unwrap()).is_empty());
    });
}
