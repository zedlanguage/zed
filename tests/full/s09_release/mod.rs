//! The release build's toolchain (BUILD-root-toolchain-pin): a build from the repository's root
//! uses the Rust version that the root's rust-toolchain.toml names, and the cross builds of
//! tools/fetch_test_deps.sh fetch that same version.
//!
//! This machine has no rustup, so the first test checks the pin only against the rustc on the
//! PATH; the third runs rustup in a container whose default toolchain is another version and
//! checks that it picks the pinned one (BUILD-toolchain-pin-rustup).

use crate::s00_01_tools::podman;
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

/// rustup picks the pinned version over its default. The image (built by
/// tools/fetch_test_deps.sh) has rustup with two toolchains, the pin and the default 1.98.0, and
/// runs with no network, so rustup can only choose between them. The worktree is mounted read-only
/// at /src: rustc and cargo must report the pin from the root and from crates/zed-clif (rustup
/// looks for the file in the working directory and each one above it), and the default from /,
/// which no pin file covers; the last shows the default is not the pin, so the first two would
/// fail if rustup ignored the file. Under zrun the root's path names a mount that podman, started
/// outside zrun's mount namespace, does not see, so the worktree's own path, ZRUN_WORKTREE, is
/// mounted. SELinux labels are not applied (`label=disable`): a relabel (`:z`) would change the
/// labels of the worktree's files.
#[test]
fn rustup_picks_the_pinned_rust_over_its_default() {
    let pin = pinned();
    let image = format!("localhost/zed-test-rustup:{pin}");
    let tree = std::env::var("ZRUN_WORKTREE").map_or_else(|_| root(), PathBuf::from);
    let mount = format!("{}:/src:ro", tree.display());
    let dirs = ["/src", "/src/crates/zed-clif", "/"];
    let script = format!(
        "for d in {}; do cd $d && rustc -V && cargo -V || exit 1; done",
        dirs.join(" ")
    );
    let out = podman(&[
        "run",
        "--rm",
        "--network=none",
        "--security-opt",
        "label=disable",
        "-v",
        &mount,
        &image,
        "sh",
        "-c",
        &script,
    ]);
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "the container failed (after a change of the pin, run tools/fetch_test_deps.sh): {}{text}",
        String::from_utf8_lossy(&out.stderr)
    );
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 2 * dirs.len(), "{text}");
    for (k, dir) in dirs.iter().enumerate() {
        for line in &lines[2 * k..2 * k + 2] {
            let found = line.split_whitespace().nth(1).unwrap_or("");
            if *dir == "/" {
                assert_ne!(
                    found, pin,
                    "rustup's default is the pin, so this shows nothing: {line}"
                );
            } else {
                assert_eq!(found, pin, "in {dir}, {line}: not the pinned version");
            }
        }
    }
}
