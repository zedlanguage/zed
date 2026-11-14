//! The tests of [`crate::scratch`].

use crate::scratch::*;
use std::path::PathBuf;
use std::process::Command;

/// The variable that makes [`a_child_process_reports_its_scratch_directory`] act.
const CHILD: &str = "ZED_SCRATCH_CHILD";

/// In a child process of [`two_processes_get_two_directories`], with `CHILD` set to a file
/// name: prints its scratch directory and leaves a file of that name in it. Otherwise does
/// nothing.
#[test]
fn a_child_process_reports_its_scratch_directory() {
    let Ok(file) = std::env::var(CHILD) else {
        return;
    };
    let dir = process_tmpdir();
    println!("scratch {}", dir.display());
    std::fs::write(dir.join(file), "left by a child process").unwrap();
}

/// The scratch directory that a child process of this binary reports, the child leaving a
/// file `file` in it.
fn child(file: &str) -> PathBuf {
    let run = Command::new(std::env::current_exe().expect("this test binary"))
        .args([
            "--exact",
            "scratch_tests::a_child_process_reports_its_scratch_directory",
            "--nocapture",
        ])
        .env(CHILD, file)
        .output()
        .expect("running this test binary");
    let out = String::from_utf8_lossy(&run.stdout);
    assert!(run.status.success(), "{out}");
    let line = out
        .lines()
        .find_map(|l| l.strip_prefix("scratch "))
        .unwrap_or_else(|| panic!("no scratch line in:\n{out}"));
    PathBuf::from(line)
}

/// A process running beside this one gets a directory of its own, beside this one's in
/// the directory of this binary, and what it leaves there stays once it has ended.
#[test]
fn two_processes_get_two_directories() {
    let own = process_tmpdir();
    let binary = own.parent().unwrap();
    assert_eq!(binary.parent(), Some(target_tmpdir().as_path()));
    let name = binary.file_name().unwrap().to_str().unwrap();
    assert!(
        name.starts_with("zed_tests") && !name.contains('-'),
        "{name} is not the name of this binary without its hash"
    );
    let other = child("left_by_a_child");
    assert_ne!(other, own, "a child process took this process's directory");
    assert_eq!(other.parent(), Some(binary));
    assert_eq!(
        std::fs::read_to_string(other.join("left_by_a_child")).unwrap(),
        "left by a child process"
    );
}

/// libtest names each test's thread after the test, which [`scratch`] tells tests apart by.
#[test]
fn a_test_runs_on_a_thread_named_after_it() {
    assert_eq!(
        std::thread::current().name(),
        Some("scratch_tests::a_test_runs_on_a_thread_named_after_it")
    );
}

/// One test may name a path again; another test naming it fails at once.
#[test]
fn a_second_test_naming_a_path_fails() {
    let path = "step_helpers_tests/claimed";
    let named = |name: &str| {
        std::thread::Builder::new()
            .name(name.to_string())
            .spawn(move || scratch(path))
            .unwrap()
            .join()
    };
    let first = named("first test").expect("the first test names it");
    assert_eq!(first, process_tmpdir().join(path));
    assert_eq!(
        named("first test").ok(),
        Some(first),
        "again by the same test"
    );
    let second = named("second test").expect_err("a second test names it");
    assert_eq!(
        second.downcast_ref::<String>().map(String::as_str),
        Some(
            "two tests use the scratch path step_helpers_tests/claimed: first test and \
             second test; give each a name of its own"
        )
    );
}
