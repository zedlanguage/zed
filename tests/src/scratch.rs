//! The scratch directories of the tests: a directory per process of a test binary, and in it a
//! path per test. Re-exported by `crate::step_helpers`; its own tests are in
//! `crate::scratch_tests`.

use std::collections::BTreeMap;
use std::fs::{File, TryLockError};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock, PoisonError};

/// The scratch directory of the running test target: what cargo gives a test target's source
/// as `CARGO_TARGET_TMPDIR`, `<target dir>/tmp`. Cargo sets that variable for test targets
/// only, not for this library, so it is found from the test binary's own path,
/// `<target dir>/<profile>/deps/<binary>`.
pub fn target_tmpdir() -> PathBuf {
    let exe = std::env::current_exe().expect("the test binary has a path");
    let target = exe
        .ancestors()
        .nth(3)
        .expect("a test binary lies in <target dir>/<profile>/deps");
    target.join("tmp")
}

/// This process's own scratch directory, `<target dir>/tmp/<binary>/process-<k>`, where
/// `<binary>` is the test binary's name without its hash: of `process-0`, `process-1`, ...,
/// the first whose lock no running process holds. The directory is opened and locked (`flock`)
/// for the life of the process; the kernel releases the lock when the process ends, however
/// it ends, so the next process of the binary to start takes the directory again.
///
/// Every process of every test binary of a worktree shares `<target dir>/tmp`, and two
/// processes writing one name there read each other's files: a process of a test binary
/// read a file another had just emptied with `std::fs::write` (TEST-shared-tmpdir-race,
/// TEST-l01_29-widen-flake). tools/run_tests.sh runs several processes of one binary at once
/// when it splits the binary into pieces. A directory per process ends that. A directory per
/// process id would need a sweep of those whose process has ended, which a reused process id
/// defeats; lock slots hold no more directories than processes of the binary ran at once, as
/// the working directories of `zed_native::link` are kept apart by their locks. Cost: one
/// `open` and one lock per slot tried, at the first call of a process.
///
/// What a process leaves in its directory stays for the next process that takes it, as files
/// in `<target dir>/tmp` always stayed: the executables the tests of L1.36a and L1.36b link
/// are kept from run to run and linked again only when an input changed
/// (`zed_native::link::kept`), and a binary run alone takes `process-0` each time, so it finds
/// them. Emptying the directory at each start would link every executable again on every run,
/// about 1.5 s each (TEST-runtime-build-in-piece, in tools/run_tests.sh). The cost is disk:
/// one copy of a binary's files per process of it that ran at once, where there was one copy.
///
/// Worktrees do not share it: zrun mounts each worktree's own build over the target
/// directory.
pub fn process_tmpdir() -> &'static Path {
    static DIR: OnceLock<(PathBuf, File)> = OnceLock::new();
    &DIR.get_or_init(|| {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let name = exe
            .file_name()
            .expect("a test binary has a file name")
            .to_string_lossy();
        let binary = name
            .rsplit_once('-')
            .map_or(&*name, |(binary, _hash)| binary);
        let tmp = target_tmpdir().join(binary);
        for k in 0u32.. {
            let path = tmp.join(format!("process-{k}"));
            std::fs::create_dir_all(&path).expect("making a scratch directory of a process");
            let lock = File::open(&path).expect("opening a scratch directory of a process");
            match lock.try_lock() {
                Ok(()) => return (path, lock),
                Err(TryLockError::WouldBlock) => continue,
                Err(TryLockError::Error(e)) => {
                    panic!("locking the scratch directory {}: {e}", path.display())
                }
            }
        }
        unreachable!("a lock is free among 2^32 slots")
    })
    .0
}

/// `path` under [`process_tmpdir`], for the calling test alone; nothing is made. A test is
/// told apart by its thread's name, which libtest sets to the test's path. A second test of
/// this process that names the same `path` panics, so two tests that share a name fail at
/// once, every time they run in one process, instead of now and then: two l01_19 tests both
/// wrote `twice/prog.zed` and read each other's program (TEST-shared-tmpdir-race). A call
/// from a thread with no name, which a test may start, is not checked.
pub fn scratch(path: impl AsRef<Path>) -> PathBuf {
    static OWNERS: Mutex<BTreeMap<PathBuf, String>> = Mutex::new(BTreeMap::new());
    let path = path.as_ref();
    if let Some(test) = std::thread::current().name() {
        let mut owners = OWNERS.lock().unwrap_or_else(PoisonError::into_inner);
        let owner = owners
            .entry(path.to_path_buf())
            .or_insert_with(|| test.to_string());
        if owner != test {
            let owner = owner.clone();
            drop(owners);
            panic!(
                "two tests use the scratch path {}: {owner} and {test}; give each a name of \
                 its own",
                path.display()
            );
        }
    }
    process_tmpdir().join(path)
}
