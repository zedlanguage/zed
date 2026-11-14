//! A missing outside tool fails the run: `tools/run_tests.sh --full` stops before any test
//! and exits non-zero rather than skipping the tests that need it.

use std::path::PathBuf;
use std::process::Command;

/// The test's directory under the temporary directory, removed when the test ends, passed or
/// failed.
struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        assert_eq!(
            self.0.file_name().and_then(|n| n.to_str()),
            Some("zed-full-missing-tool")
        );
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn a_missing_tool_fails_the_full_run() {
    let dir = Scratch(zed_tests::step_helpers::scratch("zed-full-missing-tool"));
    let step = dir.0.join("tests/full/s99_99_needs_a_tool");
    std::fs::create_dir_all(&step).unwrap();
    std::fs::write(step.join("needs"), "zed-no-such-tool\n").unwrap();
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/../tools/run_tests.sh");
    let out = Command::new("bash")
        .args([script, "--full"])
        .current_dir(&dir.0)
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
