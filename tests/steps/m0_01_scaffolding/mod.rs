//! Step M0.1: repository scaffolding.
//!
//! The step folders are the index the user documentation is built from, so their names and
//! their test targets in `tests/Cargo.toml` are checked here, and the list itself is an
//! expected-output snapshot.

mod bench;
mod cases;
mod fail_steps_name_layers;
mod scaling;

use std::collections::BTreeSet;
use std::fs;

use zed_tests::{is_step_name, steps_dir};
use zed_tools::step_targets::{self, block, drift, folders, splice, targets};

/// The step folders present on disk, sorted.
fn step_folders() -> BTreeSet<String> {
    folders(&steps_dir()).unwrap_or_else(|e| panic!("{e}"))
}

/// The test targets `tests/Cargo.toml` lists for the step folders, in its order.
fn declared_targets() -> Vec<(String, String)> {
    let manifest = steps_dir().join("../Cargo.toml");
    let toml = fs::read_to_string(&manifest).expect("tests/Cargo.toml is readable");
    targets(&toml).unwrap_or_else(|e| panic!("{e}"))
}

#[test]
fn every_step_folder_is_well_named() {
    for name in step_folders() {
        assert!(
            is_step_name(&name),
            "badly named step folder: tests/steps/{name}"
        );
    }
}

#[test]
fn every_step_folder_has_a_target_and_every_target_has_a_folder() {
    let problems = drift(&step_folders(), &declared_targets());
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn step_index() {
    let names: Vec<String> = declared_targets().into_iter().map(|(n, _)| n).collect();
    insta::assert_snapshot!(names.join("\n"));
}

/// The set of `names`.
fn set(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|n| n.to_string()).collect()
}

/// A manifest with the targets of `names` between the markers.
fn manifest(names: &[&str]) -> String {
    format!(
        "[package]\nname = \"t\"\n\n{}\n{}{}\n\n[dev-dependencies]\n",
        step_targets::BEGIN,
        block(&set(names)),
        step_targets::END
    )
}

#[test]
fn the_written_targets_read_back_and_splicing_twice_changes_nothing() {
    let toml = manifest(&["m0_01_a", "l01_02_b"]);
    let read = targets(&toml).unwrap();
    assert_eq!(
        read,
        [
            ("l01_02_b".to_string(), "steps/l01_02_b/mod.rs".to_string()),
            ("m0_01_a".to_string(), "steps/m0_01_a/mod.rs".to_string()),
        ]
    );
    let again = splice(&toml, &block(&set(&["m0_01_a", "l01_02_b"]))).unwrap();
    assert_eq!(again, toml);
    let grown = splice(&toml, &block(&set(&["m0_01_a", "l01_02_b", "l01_03_c"]))).unwrap();
    assert!(grown.starts_with("[package]") && grown.ends_with("[dev-dependencies]\n"));
    assert_eq!(targets(&grown).unwrap().len(), 3);
}

#[test]
fn drift_names_each_folder_without_a_target_and_each_target_without_a_folder() {
    let toml = manifest(&["l01_01_a", "l01_02_b"]);
    let problems = drift(&set(&["l01_01_a", "l01_03_c"]), &targets(&toml).unwrap());
    assert_eq!(
        problems,
        [
            "target l01_02_b in tests/Cargo.toml has no folder tests/steps/l01_02_b",
            "folder tests/steps/l01_03_c has no [[test]] target in tests/Cargo.toml: run step_targets",
        ]
    );
}

#[test]
fn drift_names_a_target_listed_twice_or_with_another_path() {
    let toml = manifest(&["l01_01_a"]).replace(
        "path = \"steps/l01_01_a/mod.rs\"\n",
        "path = \"steps/l01_01_a/main.rs\"\n[[test]]\nname = \"l01_01_a\"\npath = \"steps/l01_01_a/mod.rs\"\n",
    );
    let problems = drift(&set(&["l01_01_a"]), &targets(&toml).unwrap());
    assert_eq!(
        problems,
        [
            "target l01_01_a has the path steps/l01_01_a/main.rs, not steps/l01_01_a/mod.rs",
            "target l01_01_a is listed twice in tests/Cargo.toml",
        ]
    );
}

#[test]
fn a_manifest_without_the_markers_or_with_a_target_without_a_path_is_refused() {
    let without = "[package]\nname = \"t\"\n";
    assert!(targets(without).unwrap_err().contains("has no line"));
    assert!(splice(without, "").unwrap_err().contains("has no line"));
    let no_end = format!("{}\n[[test]]\n", step_targets::BEGIN);
    assert!(targets(&no_end).unwrap_err().contains(step_targets::END));
    let pathless = manifest(&["l01_01_a"]).replace("path = \"steps/l01_01_a/mod.rs\"\n", "");
    assert_eq!(
        targets(&pathless).unwrap_err(),
        "tests/Cargo.toml: target l01_01_a has no path"
    );
}
