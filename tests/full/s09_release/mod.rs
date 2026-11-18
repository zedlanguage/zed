//! The release build's toolchain (BUILD-root-toolchain-pin, BUILD-parallel-frontend): a build
//! from the repository's root uses the Rust that the root's rust-toolchain.toml pins, a dated
//! nightly, and the cross builds of tools/fetch_test_deps.sh fetch that same build.
//!
//! A nightly's `rustc -V` names its version and commit, `rustc 1.102.0-nightly (59cbdee2e
//! 2026-11-17)`, not the channel `nightly-2026-11-18`, so each test compares whole `-V` lines with
//! those of the pinned toolchain as rustup on this machine runs it (`rustup run <pin>`). The third
//! test runs rustup in a container whose default toolchain is another version and checks that it
//! picks the pinned one (BUILD-toolchain-pin-rustup).

use crate::s00_01_tools::podman;
use std::path::{Path, PathBuf};
use std::process::Command;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// The toolchain the root's rust-toolchain.toml pins: its `channel`, `nightly-<date>`.
/// tools/fetch_test_deps.sh puts its official build, with std for each target, in
/// `$ZED_TEST_DEPS/rust-<pin>`.
pub(crate) fn pinned() -> String {
    let path = root().join("rust-toolchain.toml");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let channel = text
        .lines()
        .find_map(|l| l.strip_prefix("channel = \""))
        .and_then(|l| l.strip_suffix('"'))
        .unwrap_or_else(|| panic!("{} names no channel", path.display()));
    assert!(
        channel.starts_with("nightly-"),
        "{} pins {channel}, not a dated nightly",
        path.display()
    );
    channel.to_string()
}

/// The first line `command -V` prints, run in `dir`.
fn version_line(command: &[&str], dir: &Path) -> String {
    let out = Command::new(command[0])
        .args(&command[1..])
        .arg("-V")
        .current_dir(dir)
        .output()
        .unwrap_or_else(|e| panic!("{command:?}: {e}"));
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(
        out.status.success(),
        "{command:?} -V failed: {}{text}",
        String::from_utf8_lossy(&out.stderr)
    );
    text.lines().next().unwrap_or("").to_string()
}

/// What the pinned toolchain's `program -V` prints, through rustup.
fn pinned_line(program: &str) -> String {
    version_line(&["rustup", "run", &pinned(), program], Path::new("/"))
}

#[test]
fn a_build_from_the_root_uses_the_pinned_rust() {
    for program in ["rustc", "cargo"] {
        assert_eq!(
            version_line(&[program], &root()),
            pinned_line(program),
            "{program} at the root is not the pinned toolchain"
        );
    }
}

#[test]
fn the_cross_builds_fetch_the_pinned_rust() {
    let pin = pinned();
    let date = pin.trim_start_matches("nightly-");
    let path = root().join("tools/fetch_test_deps.sh");
    let script = std::fs::read_to_string(&path).unwrap();
    let components: Vec<&str> = script
        .lines()
        .filter_map(|l| l.strip_prefix("component "))
        .filter_map(|l| l.split_whitespace().next())
        .collect();
    assert!(!components.is_empty(), "{} fetches no Rust", path.display());
    for name in components {
        assert!(
            name.starts_with(&format!("{date}/rustc-nightly-"))
                || name.starts_with(&format!("{date}/rust-std-nightly-")),
            "{} fetches {name}, not the nightly of {date}",
            path.display()
        );
    }
    let fetched = std::env::var("ZED_TEST_DEPS").expect("run through tools/run_tests.sh --full");
    let rustc = PathBuf::from(fetched).join(format!("rust-{pin}/bin/rustc"));
    assert_eq!(
        version_line(&[rustc.to_str().unwrap()], Path::new("/")),
        pinned_line("rustc")
    );
}

/// rustup picks the pinned toolchain over its default. The image (built by
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
    let expected = [pinned_line("rustc"), pinned_line("cargo")];
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
        for (line, want) in lines[2 * k..2 * k + 2].iter().zip(&expected) {
            if *dir == "/" {
                assert_ne!(
                    line, want,
                    "rustup's default is the pin, so this shows nothing"
                );
            } else {
                assert_eq!(line, want, "in {dir}: not the pinned toolchain");
            }
        }
    }
}
