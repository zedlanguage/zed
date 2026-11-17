//! Step S.7b, row CLIF-shim: the Cranelift shim `zed-clif`. Its C functions are called from Rust
//! by the test target `s_07b_clif_shim_calls` of the package `zed-clif` (`calls.rs` here), since
//! this package forbids `unsafe`; this one checks the shim's Cranelift version: pinned exactly,
//! the same as zed-native's, and the only Cranelift version in Cargo.lock.

use std::collections::BTreeMap;
use std::path::Path;

/// The text of `path`, from the workspace root.
fn file(path: &str) -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    std::fs::read_to_string(root.join(path)).unwrap_or_else(|e| panic!("reading {path}: {e}"))
}

/// The Cranelift dependencies of the manifest `text`: each `cranelift-<name> = "<requirement>"`
/// line, by name.
fn cranelift_requirements(text: &str) -> BTreeMap<String, String> {
    text.lines()
        .filter_map(|line| {
            let (name, value) = line.split_once('=')?;
            let name = name.trim();
            let value = value.trim().strip_prefix('"')?.strip_suffix('"')?;
            name.starts_with("cranelift-")
                .then(|| (name.to_string(), value.to_string()))
        })
        .collect()
}

/// Every `(name, version)` of a Cranelift package in the lock file `text`.
fn locked_cranelift(text: &str) -> Vec<(String, String)> {
    let mut found = Vec::new();
    let mut lines = text.lines();
    while let Some(line) = lines.next() {
        let Some(name) = line
            .strip_prefix("name = \"")
            .and_then(|s| s.strip_suffix('"'))
        else {
            continue;
        };
        if !name.starts_with("cranelift-") {
            continue;
        }
        let version = lines
            .next()
            .and_then(|l| l.strip_prefix("version = \""))
            .and_then(|s| s.strip_suffix('"'))
            .unwrap_or_else(|| panic!("Cargo.lock: no version line after package {name}"));
        found.push((name.to_string(), version.to_string()));
    }
    found
}

#[test]
fn the_shim_pins_the_cranelift_version_of_zed_native_and_the_lock_has_no_other() {
    let shim = cranelift_requirements(&file("crates/zed-clif/Cargo.toml"));
    let native = cranelift_requirements(&file("crates/zed-native/Cargo.toml"));
    let expected = ["codegen", "module", "native", "reader"].map(|n| format!("cranelift-{n}"));
    assert_eq!(shim.keys().cloned().collect::<Vec<_>>(), expected);
    // zed-native asks for the same version, `^` (Cargo's default); the shim for exactly it.
    let version = native
        .get("cranelift-codegen")
        .expect("zed-native depends on cranelift-codegen");
    for (name, requirement) in &shim {
        assert_eq!(requirement, &format!("={version}"), "{name}");
    }
    for (name, requirement) in &native {
        assert_eq!(requirement, version, "zed-native's {name}");
    }
    // One version of each Cranelift package in the lock, the pinned one.
    let locked = locked_cranelift(&file("Cargo.lock"));
    assert!(locked.len() >= shim.len(), "{locked:?}");
    for (name, v) in &locked {
        assert_eq!(v, version, "Cargo.lock's {name}");
    }
    for name in shim.keys() {
        assert_eq!(
            locked.iter().filter(|(n, _)| n == name).count(),
            1,
            "{name}"
        );
    }
}

#[test]
fn the_requirements_and_the_lock_are_read_as_written() {
    // The readers above on small texts, so the check cannot pass by reading nothing.
    let manifest = "[dependencies]\ncranelift-codegen = \"=1.2.3\"\nother = \"1\"\n\
                    cranelift-reader = { version = \"1\" }\n";
    let read = cranelift_requirements(manifest);
    assert_eq!(read.len(), 1);
    assert_eq!(read["cranelift-codegen"], "=1.2.3");
    let lock = "[[package]]\nname = \"cranelift-codegen\"\nversion = \"1.2.3\"\n\n\
                [[package]]\nname = \"cranelift-codegen\"\nversion = \"1.2.4\"\n\n\
                [[package]]\nname = \"gimli\"\nversion = \"0.1.0\"\n";
    assert_eq!(
        locked_cranelift(lock),
        [
            ("cranelift-codegen".to_string(), "1.2.3".to_string()),
            ("cranelift-codegen".to_string(), "1.2.4".to_string())
        ]
    );
}
