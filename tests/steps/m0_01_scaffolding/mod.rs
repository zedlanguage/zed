//! Step M0.1: repository scaffolding.
//!
//! The step folders are the index the user documentation is built from, so their names and
//! their declaration in `main.rs` are checked here, and the list itself is a golden snapshot.

use std::fs;
use zed_tests::{is_step_name, steps_dir};

/// The step folders present on disk, sorted.
fn step_folders() -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(steps_dir())
        .expect("tests/steps is readable")
        .map(|e| e.expect("directory entry"))
        .filter(|e| e.file_type().expect("file type").is_dir())
        .map(|e| e.file_name().into_string().expect("UTF-8 folder name"))
        .collect();
    names.sort();
    names
}

/// The modules `main.rs` declares, in declaration order.
fn declared_modules() -> Vec<String> {
    let main = fs::read_to_string(steps_dir().join("main.rs")).expect("main.rs is readable");
    main.lines()
        .filter_map(|l| l.trim().strip_prefix("mod "))
        .map(|l| l.trim_end_matches(';').to_string())
        .collect()
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
fn every_step_folder_is_declared_and_every_declaration_has_a_folder() {
    let mut declared = declared_modules();
    declared.sort();
    assert_eq!(step_folders(), declared);
}

#[test]
fn step_index() {
    insta::assert_snapshot!(declared_modules().join("\n"));
}
