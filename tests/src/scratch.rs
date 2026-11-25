//! The scratch directories of the tests: a directory per process of a test binary, and in it a
//! path per test. Compiled into this crate as `crate::scratch` (re-exported by
//! `crate::step_helpers`) and, by `#[path]`, into the test targets of zed-native that run the
//! zedc executable, which cannot depend on this crate; its own tests are in
//! `crate::scratch_tests`, so they run once, in this crate only (as TEST-seed-test-once does
//! for `crate::seed`).

use std::collections::BTreeMap;
use std::fs::{File, TryLockError};
use std::io::{Read, Seek, SeekFrom, Write};
use std::ops::Bound;
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
        let tmp = binary_tmpdir();
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

/// The directory of the running test binary's processes, `<target dir>/tmp/<binary>`, where
/// `<binary>` is the binary's name without its hash.
fn binary_tmpdir() -> PathBuf {
    let exe = std::env::current_exe().expect("the test binary has a path");
    let name = exe
        .file_name()
        .expect("a test binary has a file name")
        .to_string_lossy();
    let binary = name
        .rsplit_once('-')
        .map_or(&*name, |(binary, _hash)| binary);
    target_tmpdir().join(binary)
}

/// `path` under [`process_tmpdir`], for the calling test alone; nothing is made. A test is
/// told apart by its thread's name, which libtest sets to the test's path. A second test that
/// names the same `path`, a path inside it or a directory holding it panics, so two tests that
/// share a file fail at once instead of now and then: two l01_19 tests both wrote
/// `twice/prog.zed` and read each other's program (TEST-shared-tmpdir-race).
///
/// Which tests are compared (TEST-shared-path-check-gaps, three cases the check once missed):
///
/// - Every test of this build of the binary, in any of its processes and runs, not only those
///   of this process. tools/run_tests.sh runs each benchmark in a process of its own, and the
///   correctness tests in others with `--skip bench::`, so a benchmark never met another test
///   in one process; yet each process takes a directory another took before
///   ([`process_tmpdir`]) and finds the files it left. So each claim of a path is written to a
///   record all processes of this build of the binary share, as a line `<test>\t<path>`,
///   under an exclusive lock (`flock`) on the record, and each claim is checked against every
///   line. The record is named by the build ([`claims_record`]), so a test renamed or a path
///   moved to another test in a new build is not held to the claims of the old one, and two
///   builds sharing one target directory keep a record each. One record shared by all builds
///   and emptied by a process of another build, as before, lost the claims of a build whenever
///   a process of another build ran between two of its processes (TEST-scratch-native-dirs).
///   The cost is one small file per build of the binary, kept until the target directory is
///   cleaned; no process can tell whether another build still runs, so none deletes another's
///   record. A process of `compare_by` (tests/src/scaling.rs), which runs the same test again
///   in a new process, claims with the same name and passes.
/// - A path inside another test's path, or holding it: `scratch_dir("d")` of one test and
///   `scratch("d/prog.zed")` of another reuse the directory `d`, and a test that empties its
///   directory (`fs::remove_dir_all`, as m0_01 `cases.rs` does) removes the other's files. Two
///   paths are compared by their components, so `d/./f`, `d//f` and `d/f` are one path; a path
///   must be relative and made of plain names (no `..`, no `.` first, not absolute, which
///   `join` would put outside the directory), in UTF-8 with no tab or newline, as the record
///   holds it.
/// - A call from a thread with no name is refused, since no test can be told apart by it.
///   No caller of `scratch` or `scratch_dir` under tests/ calls from such a thread (each of
///   the tests that start threads, l01_36b `at_once`, l02_08 `pins_binary`, m0_09
///   `treap_seeds_binary` and l01_36a `one_engine`, asks for its paths on the test's thread
///   and passes them in; the harness's own threads, [`crate::scaling::on_a_stack`] and the
///   runs it measures, take the test's name), so refusing costs no caller anything, where
///   passing an owner in would add an argument every caller must give. A thread that needs a
///   path is given it, or is started with the test's name.
///
/// Not checked: a directory made from [`process_tmpdir`] without `scratch`. The zedc tests of
/// zed-native once made one directory per test file that way, shared by the file's tests;
/// they now take one per test from [`test_dir`] (TEST-scratch-native-dirs).
///
/// Complexity tradeoff: a test's first claim of a path in a process takes the record's lock,
/// reads the lines other processes added since this process last read (each line is read once
/// a process), and looks the path, its ancestors and the paths inside it up in a sorted map:
/// O(d log p + the lines read) for a path of d components among p claims. A later claim of
/// the same path by the same test is a lookup alone, with no lock. Keeping claims per process,
/// as before, needs no file, but misses the benchmarks above.
pub fn scratch(path: impl AsRef<Path>) -> PathBuf {
    let path = path.as_ref();
    let thread = std::thread::current();
    let Some(test) = thread.name() else {
        panic!(
            "the scratch path {} was asked for on a thread with no name, which no test can be \
             told apart by; ask for it on the test's own thread and pass it to the thread, or \
             start the thread with the test's name (std::thread::Builder::name with \
             std::thread::current().name())",
            path.display()
        );
    };
    let plain = path.to_str().is_some_and(|p| !p.contains(['\t', '\n']))
        && path.components().next().is_some()
        && path
            .components()
            .all(|c| matches!(c, std::path::Component::Normal(_)));
    assert!(
        plain,
        "the scratch path {} is not a relative path of plain names in UTF-8 with no tab or \
         newline",
        path.display()
    );
    // Spelled by its components alone, as the record and the messages show it.
    let path: PathBuf = path.components().collect();
    claim(&path, test);
    process_tmpdir().join(path)
}

/// The claims of scratch paths in this build of the test binary that this process has read
/// from the record (see [`scratch`]) or added to it.
struct Claims {
    /// Each path claimed, with the test that claimed it. No path is inside another test's.
    owners: BTreeMap<PathBuf, String>,
    /// The bytes of the record read so far.
    read: u64,
}

/// Claims `path` for `test`, or panics naming the test that claimed it or a path inside it or
/// holding it first.
fn claim(path: &Path, test: &str) {
    static CLAIMS: Mutex<Claims> = Mutex::new(Claims {
        owners: BTreeMap::new(),
        read: 0,
    });
    static RECORD: OnceLock<File> = OnceLock::new();
    let mut claims = CLAIMS.lock().unwrap_or_else(PoisonError::into_inner);
    if claims.owners.get(path).is_some_and(|owner| owner == test) {
        return;
    }
    let record = RECORD.get_or_init(|| {
        let at = claims_record();
        let dir = at.parent().expect("a record lies in a directory");
        std::fs::create_dir_all(dir).expect("making the directory of the scratch records");
        std::fs::OpenOptions::new()
            .read(true)
            .append(true)
            .create(true)
            .open(&at)
            .unwrap_or_else(|e| panic!("opening the scratch record {}: {e}", at.display()))
    });
    record.lock().expect("locking the scratch record");
    let locked = Unlock(record);
    claims.catch_up(record);
    let clash = claims
        .clash(path, test)
        .map(|(owned, owner)| (owned.to_path_buf(), owner.to_string()));
    // A claim another process of the same test made (a process of `compare_by`, or an earlier
    // run) is in the record already: a second line would only make every later process read
    // more.
    let known = claims.owners.get(path).is_some_and(|owner| owner == test);
    if clash.is_none() && !known {
        let line = format!("{test}\t{}\n", path.display());
        let mut writer = record;
        writer
            .write_all(line.as_bytes())
            .expect("writing the scratch record");
        claims.read += line.len() as u64;
        claims.owners.insert(path.to_path_buf(), test.to_string());
    }
    drop(locked);
    drop(claims);
    let Some((owned, owner)) = clash else {
        return;
    };
    if owned.as_path() == path {
        panic!(
            "two tests use the scratch path {}: {owner} and {test}; give each a name of its own",
            path.display()
        );
    }
    let (outer, inner) = if path.starts_with(&owned) {
        (owned.as_path(), path)
    } else {
        (path, owned.as_path())
    };
    panic!(
        "two tests use the scratch path {} and the path {} inside it: {owner} (of {}) and \
         {test} (of {}); give each a name of its own, neither inside the other",
        outer.display(),
        inner.display(),
        owned.display(),
        path.display()
    );
}

/// Releases the lock on the scratch record when dropped, on a panic too, so that no other
/// process waits on it forever.
struct Unlock<'a>(&'a File);

impl Drop for Unlock<'_> {
    fn drop(&mut self) {
        // Best effort: the lock goes when the process ends in any case.
        let _ = self.0.unlock();
    }
}

impl Claims {
    /// Reads the lines other processes of this build added to `record` since the last read.
    /// Called under the record's lock. Lines are only ever added to a record, never removed.
    fn catch_up(&mut self, mut record: &File) {
        record
            .seek(SeekFrom::Start(self.read))
            .expect("seeking in the scratch record");
        let mut lines = String::new();
        record
            .read_to_string(&mut lines)
            .expect("reading the scratch record");
        for line in lines.split_terminator('\n') {
            // Every line is written whole under the lock, in one write to a file opened to
            // append; a line with no tab, which only a write cut short could leave, is skipped.
            if let Some((test, path)) = line.split_once('\t') {
                self.owners.insert(PathBuf::from(path), test.to_string());
            }
        }
        self.read += lines.len() as u64;
    }

    /// The first claim of another test on `path`, on a directory holding it or on a path inside
    /// it: the path claimed and its test.
    fn clash(&self, path: &Path, test: &str) -> Option<(&Path, &str)> {
        // The paths inside `path` follow it in the map: paths are ordered by their components,
        // and every path that starts with the components of `path` sorts after it and before
        // any other path that sorts after it.
        let inside = self
            .owners
            .range::<Path, _>((Bound::Excluded(path), Bound::Unbounded))
            .take_while(|(owned, _)| owned.starts_with(path));
        path.ancestors()
            .filter_map(|a| self.owners.get_key_value(a))
            .chain(inside)
            .find(|(_, owner)| *owner != test)
            .map(|(owned, owner)| (owned.as_path(), owner.as_str()))
    }
}

/// The record of the claims of this build of the test binary ([`scratch`]):
/// `<target dir>/tmp/<binary>/scratch-claims/<build>`, with `<build>` from [`build_stamp`].
pub(crate) fn claims_record() -> PathBuf {
    binary_tmpdir().join("scratch-claims").join(build_stamp())
}

/// The variable that names the build in place of the binary's modification time, so that a
/// test of the record runs a process as of another build of the same binary
/// (`crate::scratch_tests`). It must be a plain file name.
pub(crate) const BUILD_VAR: &str = "ZED_SCRATCH_BUILD";

/// This build of the test binary: the modification time of its file, which a new build
/// changes and the hard links of a run copy keep; or the value of [`BUILD_VAR`] when set.
fn build_stamp() -> &'static str {
    static STAMP: OnceLock<String> = OnceLock::new();
    STAMP.get_or_init(|| {
        if let Some(build) = std::env::var_os(BUILD_VAR) {
            let build = build.into_string().unwrap_or_default();
            assert!(
                !build.is_empty() && !build.contains('/') && build != "." && build != "..",
                "{BUILD_VAR} is not a plain file name: {build:?}"
            );
            return build;
        }
        let exe = std::env::current_exe().expect("the test binary has a path");
        let modified = std::fs::metadata(&exe)
            .and_then(|m| m.modified())
            .unwrap_or_else(|e| panic!("reading the modification time of {}: {e}", exe.display()));
        let since = modified
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default();
        format!("{}.{:09}", since.as_secs(), since.subsec_nanos())
    })
}

/// The directory [`scratch`]`(path)`, made if it is missing. Files a run leaves in it stay
/// for the next run, which overwrites them; nothing is deleted.
pub fn scratch_dir(path: impl AsRef<Path>) -> PathBuf {
    let dir = scratch(path);
    std::fs::create_dir_all(&dir)
        .unwrap_or_else(|e| panic!("making the scratch directory {}: {e}", dir.display()));
    dir
}

/// The directory [`scratch_dir`]`(base/<test>)` of the calling test, with `<test>` its
/// thread's name, the test's path: a directory of its own for each test that shares one
/// helper naming `base`, as the zedc tests of zed-native do (TEST-scratch-native-dirs). A
/// thread with no name is refused by [`scratch`].
pub fn test_dir(base: &str) -> PathBuf {
    scratch_dir(Path::new(base).join(std::thread::current().name().unwrap_or_default()))
}
