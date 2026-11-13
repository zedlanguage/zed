//! A build of `out` works in a directory of its own beside `out`, `<out>.zed-build.<pid>.<k>`,
//! which it holds locked while it lives and removes when it ends (LINK-obj-leftover). What a
//! build stopped by a signal leaves there blocks no later build, and the next build to `out`
//! that links removes it, but never the directory of a build that is still running. Builds
//! before this item wrote the object file at `<out>.zed.o`, opened only if no file had that
//! name, so one stopped between writing and removing it made every later build fail.

use std::fs::File;
use std::io::{BufRead as _, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};

use zed_native::link::{recorded, sweep};
use zed_tests::scaling::{self, FACTOR};

use super::{Link, dir, executable, link, sign, toolchain};

/// The line the executable `exe` writes when run with no words.
fn says(exe: &Path) -> String {
    let ran = executable(exe, &[], b"");
    assert_eq!(ran.status, 0, "{}", ran.stderr);
    ran.stdout
}

/// The names in `d` that begin with `out`'s name followed by `.zed-build.`: the working
/// directories of builds of `out`.
fn working(d: &Path, out: &Path) -> Vec<String> {
    let prefix = format!("{}.zed-build.", out.file_name().unwrap().to_str().unwrap());
    let mut names: Vec<String> = std::fs::read_dir(d)
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.starts_with(&prefix))
        .collect();
    names.sort_unstable();
    names
}

/// The working directory a build of `out` in process `pid` would take at attempt `k`, made
/// here with a file in it, as a build stopped by a signal leaves it.
fn left(out: &Path, pid: u32, k: u32) -> PathBuf {
    let mut name = out.as_os_str().to_owned();
    name.push(format!(".zed-build.{pid}.{k}"));
    let at = PathBuf::from(name);
    std::fs::create_dir_all(&at).unwrap();
    std::fs::write(at.join("program.o"), b"half an object file").unwrap();
    at
}

/// The directory `at` held locked, as a running build holds its working directory.
fn held(at: &Path) -> File {
    let f = File::open(at).unwrap();
    f.lock().unwrap();
    f
}

/// The variable that makes this test executable, started by [`Elsewhere::new`], hold the
/// directory it names locked in [`a_process_that_locks_a_directory_for_another_test`].
const LOCK_DIR: &str = "ZED_TEST_LOCK_DIR";

/// A process of its own that holds the directory `at` locked, as a running build in another
/// process holds its working directory, until it is dropped. Its lock is not this process's:
/// a lock this process held would last past its own release while any child forked in another
/// test thread before the release has not yet reached exec, since the child holds a copy of
/// every open file until then, and the lock belongs to the open file, not to the descriptor.
/// The process is this test executable, running only the ignored test
/// [`a_process_that_locks_a_directory_for_another_test`] with [`LOCK_DIR`] set to `at`; it
/// takes the lock as a build does, says `held`, and keeps it until it is killed or its
/// standard input ends, as it does when this process ends however it ends.
struct Elsewhere(Child);

impl Elsewhere {
    fn new(at: &Path) -> Elsewhere {
        let exe = std::env::current_exe().unwrap();
        let mut child = Command::new(&exe)
            .args([
                "leftover::a_process_that_locks_a_directory_for_another_test",
                "--exact",
                "--ignored",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(LOCK_DIR, at)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap_or_else(|e| panic!("{}: {e}", exe.display()));
        let stdout = BufReader::new(child.stdout.take().unwrap());
        let holder = Elsewhere(child);
        // libtest writes its own lines first, and the name of the test on the line it says
        // `held` on.
        let mut said = String::new();
        for line in stdout.lines() {
            let line = line.unwrap();
            said.push_str(&line);
            said.push('\n');
            if line.trim_end().ends_with("held") {
                return holder;
            }
        }
        panic!("the process to hold {} locked ended:\n{said}", at.display());
    }
}

impl Drop for Elsewhere {
    /// Ends the process; once `wait` returns, the kernel has closed its files and its lock is
    /// released.
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Run only by [`Elsewhere::new`], in a process of its own, with [`LOCK_DIR`] set: locks that
/// directory with the call a build locks its working directory with, says `held`, and keeps
/// the lock until its standard input ends. Run any other way, it does nothing.
#[test]
#[ignore = "TEST-l01_36b-leftover: a helper, not a test; run only by Elsewhere::new, in a \
            process of its own"]
fn a_process_that_locks_a_directory_for_another_test() {
    use std::io::{Read as _, Write as _};
    let Some(at) = std::env::var_os(LOCK_DIR) else {
        return;
    };
    let _lock = held(Path::new(&at));
    let mut out = std::io::stdout();
    writeln!(out, "held").unwrap();
    out.flush().unwrap();
    let mut rest = Vec::new();
    std::io::stdin().read_to_end(&mut rest).unwrap();
}

/// A file at the name earlier builds gave the object file stops no build, and is not
/// touched: it may be the user's, or an older zedc's that is still linking.
#[test]
fn a_file_at_the_old_object_files_name_blocks_no_build() {
    let d = dir("old_name");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("open late")).unwrap();
    let old = d.join("sign.zed.o");
    std::fs::write(&old, b"left by a build that was stopped").unwrap();
    // An output that records no key, so the build links and writes its object file.
    std::fs::write(&out, "not yet built\n").unwrap();
    assert_eq!(link(&src, &out, &toolchain()), Link::Ran);
    assert_eq!(says(&out), "open late\n");
    assert_eq!(
        std::fs::read(&old).unwrap(),
        b"left by a build that was stopped"
    );
    assert_eq!(working(&d, &out), Vec::<String>::new());
}

/// A build that links removes the working directories that builds of the same output left
/// unlocked, and keeps the one a running build holds and those of other outputs.
#[test]
fn a_build_removes_what_stopped_builds_left_and_keeps_a_running_ones() {
    let d = dir("swept");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("sweep the floor")).unwrap();
    std::fs::write(&out, "not yet built\n").unwrap();
    // Left by the run before, if it failed.
    for name in working(&d, &out) {
        let at = d.join(name);
        File::open(&at).unwrap().lock().unwrap();
        std::fs::remove_dir_all(&at).unwrap();
    }
    let stopped = [left(&out, 1, 0), left(&out, std::process::id(), 0)];
    let running = left(&out, 2, 0);
    let lock = Elsewhere::new(&running);
    let other = left(&d.join("menu"), 1, 0);
    assert_eq!(link(&src, &out, &toolchain()), Link::Ran);
    assert_eq!(says(&out), "sweep the floor\n");
    for at in &stopped {
        assert!(!at.exists(), "{} is left", at.display());
    }
    assert!(
        running.join("program.o").exists(),
        "a running build's is kept"
    );
    assert!(other.join("program.o").exists(), "another output's is kept");
    // Once the running build ends, the next build removes its directory too.
    drop(lock);
    sweep(&out);
    assert_eq!(working(&d, &out), Vec::<String>::new());
    std::fs::remove_dir_all(&other).unwrap();
}

/// Builds of one program to one output at the same time each succeed, and the output is a
/// whole executable whichever ends last.
#[test]
fn builds_to_one_output_at_once_all_succeed() {
    let d = dir("at_once");
    let (src, out) = (d.join("sign.zed"), d.join("sign"));
    std::fs::write(&src, sign("two at once")).unwrap();
    std::fs::write(&out, "not yet built\n").unwrap();
    let tools = toolchain();
    let links: Vec<Link> = std::thread::scope(|s| {
        let builds: Vec<_> = (0..4)
            .map(|_| s.spawn(|| link(&src, &out, &tools)))
            .collect();
        builds.into_iter().map(|b| b.join().unwrap()).collect()
    });
    assert!(links.contains(&Link::Ran), "{links:?}");
    assert_eq!(says(&out), "two at once\n");
    assert_eq!(recorded(&out).map(|k| k.len()), Some(32));
    assert_eq!(working(&d, &out), Vec::<String>::new());
}

/// The sweep reads the output's directory once, and opens and tries to lock each working
/// directory of the output: linear in the directory's entries.
#[test]
fn the_sweep_scales() {
    let n = 400;
    let made = |m: usize| -> (PathBuf, Vec<File>) {
        let d = dir(&format!("sweep{m}"));
        let out = d.join("sign");
        // m other files, and m working directories of running builds, which stay.
        let locks = (0..m)
            .map(|i| {
                std::fs::write(d.join(format!("note{i}")), b"").unwrap();
                held(&left(&out, 1, u32::try_from(i).unwrap()))
            })
            .collect();
        (out, locks)
    };
    let (small, large) = (made(n), made(FACTOR * n));
    scaling::check("the sweep of a directory of n entries", n, |m| {
        let out = if m == n { &small.0 } else { &large.0 };
        sweep(out);
    });
    assert_eq!(
        working(large.0.parent().unwrap(), &large.0).len(),
        FACTOR * n
    );
}
