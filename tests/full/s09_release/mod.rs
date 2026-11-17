//! The release build's toolchain (BUILD-root-toolchain-pin): a build from the repository's root
//! uses the Rust version that the root's rust-toolchain.toml names, and the cross builds of
//! tools/fetch_test_deps.sh fetch that same version.
//!
//! Not proved here: that rustup, on a machine whose default toolchain is another version, picks
//! the pinned one. This machine has no rustup, so the pin is checked only against the rustc on
//! the PATH (row BUILD-toolchain-pin-rustup).

use std::path::PathBuf;
use std::process::Command;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// The version the root's rust-toolchain.toml pins: its `channel`.
fn pinned() -> String {
    let path = root().join("rust-toolchain.toml");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let channel = text
        .lines()
        .find_map(|l| l.strip_prefix("channel = \""))
        .and_then(|l| l.strip_suffix('"'))
        .unwrap_or_else(|| panic!("{} names no channel", path.display()));
    channel.to_string()
}

/// The version number `program -V` prints, run from the root as a build there would run it:
/// `rustc 1.99.1 (58cf8f9c3 2026-10-13) ...` gives `1.99.1`.
fn version(program: &str) -> String {
    let out = Command::new(program)
        .arg("-V")
        .current_dir(root())
        .output()
        .unwrap_or_else(|e| panic!("{program}: {e}"));
    assert!(out.status.success(), "{program} -V failed");
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.split_whitespace()
        .nth(1)
        .unwrap_or_else(|| panic!("{program} -V printed {text:?}"))
        .to_string()
}

#[test]
fn a_build_from_the_root_uses_the_pinned_rust() {
    let pin = pinned();
    assert_eq!(
        version("rustc"),
        pin,
        "rustc at the root is not the pinned version"
    );
    assert_eq!(
        version("cargo"),
        pin,
        "cargo at the root is not the pinned version"
    );
}

#[test]
fn the_cross_builds_fetch_the_pinned_rust() {
    let pin = pinned();
    let path = root().join("tools/fetch_test_deps.sh");
    let script = std::fs::read_to_string(&path).unwrap();
    let components: Vec<&str> = script
        .lines()
        .filter_map(|l| l.strip_prefix("component "))
        .filter(|l| l.starts_with("rustc-") || l.starts_with("rust-std-"))
        .collect();
    assert!(!components.is_empty(), "{} fetches no Rust", path.display());
    for c in components {
        let name = c.split_whitespace().next().unwrap();
        let tail = name
            .trim_start_matches("rustc-")
            .trim_start_matches("rust-std-");
        assert!(
            tail.starts_with(&format!("{pin}-")),
            "{} fetches {name}, not Rust {pin}",
            path.display()
        );
    }
    let fetched = std::env::var("ZED_TEST_DEPS").expect("run through tools/run_tests.sh --full");
    let rustc = PathBuf::from(fetched).join("rust/bin/rustc");
    assert_eq!(version(rustc.to_str().unwrap()), pin);
}
