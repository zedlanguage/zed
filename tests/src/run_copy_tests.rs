//! The test of the copy of the build that tools/run_tests.sh runs its pieces in
//! (TOOL-run-build-copy, see `make_run_copy` there): tools/test_run_tests.sh, part `copy`, runs
//! [`a_new_process_of_this_binary_starts_after_the_build_is_gone`] through run_tests.sh and,
//! while it waits, leaves this binary alone in the build's deps folder, in the run's mount
//! namespace only, as a build in the checkout deletes the names of the files it links again. The
//! test then starts this binary again, as a scaling test starts its run at 8n
//! ([`crate::scaling`]), which failed with exit 127 ("cannot open shared object file") in
//! kernel25's run of 2026-11-20 while kernel25 built zed-kernel in the same checkout.

use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

/// The variable that names the folder through which the test and test_run_tests.sh take turns:
/// the test writes `ready` in it and waits for `go`. Unset, the test does nothing.
const TURNS: &str = "ZED_TEST_RUN_COPY_TURNS";

/// How long the test waits for `go`: test_run_tests.sh writes it within a second of `ready`.
const WAIT: Duration = Duration::from_secs(50);

#[test]
fn a_new_process_of_this_binary_starts_after_the_build_is_gone() {
    let Ok(dir) = std::env::var(TURNS) else {
        return;
    };
    let dir = Path::new(&dir);
    std::fs::write(dir.join("ready"), "").unwrap();
    let start = Instant::now();
    while !dir.join("go").exists() {
        assert!(
            start.elapsed() < WAIT,
            "no file go in {} after {WAIT:?}",
            dir.display()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    let run = Command::new(std::env::current_exe().expect("this test binary"))
        .args([
            "--exact",
            "run_copy_tests::a_new_process_of_this_binary_starts_after_the_build_is_gone",
        ])
        .env_remove(TURNS)
        .output()
        .expect("starting this test binary again");
    assert!(
        run.status.success(),
        "the new process of this test binary failed ({}):\n{}{}",
        run.status,
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
}
