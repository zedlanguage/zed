//! The tests of [`crate::scratch`], compiled into this crate's unit tests only: the module is
//! compiled, by `#[path]`, into test targets of zed-native too, where these tests would run
//! again.

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

/// `ask` run on a thread named `name`, or with no name for `None`, as a test or a thread a
/// test starts asks for a path: the path, or the message it panics with.
fn on_thread(
    name: Option<&str>,
    ask: impl FnOnce() -> PathBuf + Send + 'static,
) -> Result<PathBuf, String> {
    let mut thread = std::thread::Builder::new();
    if let Some(name) = name {
        thread = thread.name(name.to_string());
    }
    thread
        .spawn(ask)
        .unwrap()
        .join()
        .map_err(|panic| message(&*panic))
}

/// The message of a panic's payload.
fn message(panic: &(dyn std::any::Any + Send)) -> String {
    panic
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_default()
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

/// A path asked for on a thread with no name, which a test may start, is refused, since no
/// test can be told apart by that thread; the message says what to do instead
/// (TEST-shared-path-check-gaps). Before, the path was given unchecked.
#[test]
fn a_path_asked_for_on_a_thread_with_no_name_is_refused() {
    let refused = on_thread(None, || scratch("scratch_tests/unnamed"))
        .expect_err("a thread with no name is given no path");
    assert_eq!(
        refused,
        "the scratch path scratch_tests/unnamed was asked for on a thread with no name, which \
         no test can be told apart by; ask for it on the test's own thread and pass it to the \
         thread, or start the thread with the test's name (std::thread::Builder::name with \
         std::thread::current().name())"
    );
    let named = on_thread(Some("a test on its own thread"), || {
        scratch("scratch_tests/unnamed")
    });
    assert_eq!(named, Ok(process_tmpdir().join("scratch_tests/unnamed")));
}

/// A directory one test makes with `scratch_dir` and another test reuses by naming a path in
/// it fails, whichever names its path first; the test that made it may name paths in it
/// (TEST-shared-path-check-gaps). Before, only equal paths were compared.
#[test]
fn a_directory_of_one_test_reused_by_another_fails() {
    let maker = Some("a test making a directory");
    let made = on_thread(maker, || scratch_dir("scratch_tests/made")).unwrap();
    assert!(made.is_dir(), "{} is made", made.display());
    assert_eq!(
        on_thread(maker, || scratch("scratch_tests/made/prog.zed")),
        Ok(made.join("prog.zed")),
        "a path in a test's own directory"
    );
    assert_eq!(
        on_thread(Some("a test writing into it"), || {
            scratch("scratch_tests/made/other.zed")
        }),
        Err(
            "two tests use the scratch path scratch_tests/made and the path \
             scratch_tests/made/other.zed inside it: a test making a directory (of \
             scratch_tests/made) and a test writing into it (of scratch_tests/made/other.zed); \
             give each a name of its own, neither inside the other"
                .to_string()
        )
    );
    // The other way round: a file named first, then a directory holding it.
    let writer = Some("a test writing a file");
    on_thread(writer, || scratch("scratch_tests/held/prog.zed")).unwrap();
    assert_eq!(
        on_thread(Some("a test making the directory holding it"), || {
            scratch_dir("scratch_tests/held")
        }),
        Err(
            "two tests use the scratch path scratch_tests/held and the path \
             scratch_tests/held/prog.zed inside it: a test writing a file (of \
             scratch_tests/held/prog.zed) and a test making the directory holding it (of \
             scratch_tests/held); give each a name of its own, neither inside the other"
                .to_string()
        )
    );
    // Spelled with a `.` or a doubled `/`, a path is the same path.
    assert_eq!(
        on_thread(Some("a test spelling it otherwise"), || {
            scratch("scratch_tests/held/.//prog.zed")
        }),
        Err(
            "two tests use the scratch path scratch_tests/held/prog.zed: a test writing a file \
             and a test spelling it otherwise; give each a name of its own"
                .to_string()
        )
    );
}

/// A path that would leave the process's directory, or is no path, is refused: absolute,
/// with `..`, with a `.` first, or empty.
#[test]
fn a_path_not_of_plain_names_is_refused() {
    for path in [
        "/tmp/scratch_tests",
        "scratch_tests/../x",
        "./scratch_tests/x",
        "",
    ] {
        let refused = on_thread(Some("a test naming an odd path"), move || scratch(path));
        assert_eq!(
            refused,
            Err(format!(
                "the scratch path {path} is not a relative path of plain names in UTF-8 with \
                 no tab or newline"
            ))
        );
    }
}

/// The variable that makes [`a_child_process_names_a_shared_path`] and
/// [`another_child_process_names_the_shared_path`] act.
const CLAIM: &str = "ZED_SCRATCH_CLAIM";

/// The path the two tests name.
const SHARED: &str = "scratch_tests/two_processes";

/// In a child process of [`two_tests_naming_a_path_in_processes_of_their_own_fail`], with
/// `CLAIM` set: names [`SHARED`]. Otherwise does nothing.
#[test]
fn a_child_process_names_a_shared_path() {
    if std::env::var_os(CLAIM).is_some() {
        scratch(SHARED);
    }
}

/// As [`a_child_process_names_a_shared_path`], as another test.
#[test]
fn another_child_process_names_the_shared_path() {
    if std::env::var_os(CLAIM).is_some() {
        scratch(SHARED);
    }
}

/// Whether `test` of this binary passed, run alone in a process of its own with `CLAIM` set,
/// and its standard output.
fn alone(test: &str) -> (bool, String) {
    let run = Command::new(std::env::current_exe().expect("this test binary"))
        .args(["--exact", test, "--test-threads=1"])
        .env(CLAIM, "1")
        .output()
        .expect("running this test binary");
    (
        run.status.success(),
        String::from_utf8_lossy(&run.stdout).into_owned(),
    )
}

/// Two tests that name one path, each in a process of its own, fail: tools/run_tests.sh runs
/// each benchmark in a process of its own and the correctness tests in others, so a benchmark
/// never met another test in one process, yet the processes of a binary take each other's
/// directories and find the files left there (TEST-shared-path-check-gaps). The first test
/// passes in each run of a build, and the second fails in each, since the claims of a build
/// last from run to run. Before, both passed.
#[test]
fn two_tests_naming_a_path_in_processes_of_their_own_fail() {
    let first = "scratch_tests::a_child_process_names_a_shared_path";
    let second = "scratch_tests::another_child_process_names_the_shared_path";
    // Twice, as `compare_by` runs a test again in a new process: the second run passes and
    // adds no line to the record.
    for _ in 0..2 {
        let (passed, out) = alone(first);
        assert!(passed, "the first test names the path:\n{out}");
    }
    let record = process_tmpdir().parent().unwrap().join("scratch-owners");
    let lines = std::fs::read_to_string(&record).unwrap();
    let line = format!("{first}\t{SHARED}");
    assert_eq!(
        lines.lines().filter(|l| *l == line).count(),
        1,
        "the lines of {}:\n{lines}",
        record.display()
    );
    let (passed, out) = alone(second);
    assert!(!passed, "the second test names the path too:\n{out}");
    let expected = format!(
        "two tests use the scratch path {SHARED}: {first} and {second}; give each a name of its \
         own"
    );
    assert!(out.contains(&expected), "no `{expected}` in:\n{out}");
}
