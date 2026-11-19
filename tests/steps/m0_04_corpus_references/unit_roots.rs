//! Row FAIL-corpus-unit-roots: a corpus program with units is a package. Under DESIGN.md
//! sec:units the manifest `zed.manifest` marks the package root, and a unit with no manifest at
//! or above it imports no unit; so each such program lives in its directory `NN-name/` as
//! `main.zed`, beside a `zed.manifest` and the units it imports.

use std::path::{Path, PathBuf};

use zedc::suppress::Suppress;

/// The corpus programs with units.
const PACKAGES: [&str; 6] = [
    "07-json-parser",
    "10-regex-matcher",
    "13-union-find",
    "21-stats-module",
    "30-client-server",
    "31-typechecker",
];

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../zed/corpus")
}

#[test]
fn every_corpus_program_with_units_sits_in_a_package_root_with_its_units() {
    let corpus = corpus();
    for dir in PACKAGES {
        let root = corpus.join(dir);
        assert!(
            root.join("zed.manifest").is_file(),
            "{dir}: no zed.manifest marks the root"
        );
        assert!(
            !corpus.join(format!("{dir}.zed")).exists(),
            "{dir}.zed imports units of {dir}/ from outside that package root"
        );
    }
}

/// The directories of the corpus that hold a manifest are exactly the packages above, so the
/// list is complete.
#[test]
fn the_packages_of_the_corpus_are_exactly_these() {
    let mut found: Vec<String> = std::fs::read_dir(corpus())
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.join("zed.manifest").is_file())
        .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    found.sort();
    assert_eq!(found, PACKAGES);
}

/// Loaded as `zedc run` loads a file, each program finds every unit it imports: no diagnostic
/// says a unit cannot be imported. (Each still stops at forms this zedc does not support,
/// such as tying an imported name to its definition, step L2.4.)
#[test]
fn zedc_finds_every_unit_each_package_imports() {
    for dir in PACKAGES {
        let main = corpus().join(dir).join("main.zed");
        let (mut suppress, _) = Suppress::take(&[]).unwrap();
        let mut err = Vec::new();
        let why = match zedc::run::load_file(main.to_str().unwrap(), &[], &mut suppress, &mut err) {
            Ok(_) => String::new(),
            Err((_, why)) => why,
        };
        assert!(!why.contains("cannot be imported"), "{dir}/main.zed: {why}");
        assert!(
            why.contains("an import is part of the Zed language"),
            "{dir}/main.zed reads its package: {why}"
        );
    }
}
