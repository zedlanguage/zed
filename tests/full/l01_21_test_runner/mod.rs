//! A missing outside tool fails the run: `tools/run_tests.sh --full` stops before any test
//! and exits non-zero rather than skipping the tests that need it.

use std::process::Command;

#[test]
fn a_missing_tool_fails_the_full_run() {
    let dir = std::env::temp_dir().join("zed-full-missing-tool");
    let step = dir.join("tests/full/s99_99_needs_a_tool");
    std::fs::create_dir_all(&step).unwrap();
    std::fs::write(step.join("needs"), "zed-no-such-tool\n").unwrap();
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/../tools/run_tests.sh");
    let out = Command::new("bash")
        .args([script, "--full"])
        .current_dir(&dir)
        .output()
        .unwrap();
    assert_eq!(
        (
            out.status.code(),
            String::from_utf8_lossy(&out.stdout).into_owned()
        ),
        (Some(1), "MISSING TOOLS: zed-no-such-tool\n".to_string())
    );
}
