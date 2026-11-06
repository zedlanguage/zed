//! Step L1.36a: `zedc build file -o out` links the object file of step L1.36 with the runtime
//! library into an executable, which binds its ports from its own command line as `zedc run`
//! does and exits with the same statuses. Two builds of a program give the same bytes, and the
//! executable's outputs and exit status equal the interpreter's.

mod agreement;
mod minmax;
mod runtime;
mod scaling;

use std::ffi::OsString;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use zed_native::link::{Toolchain, build, runtime_of};

/// A directory of its own for test `name`, under the test target's scratch directory; files
/// in it are overwritten by each run, never deleted.
pub(crate) fn dir(name: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("l01_36a")
        .join(name);
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The system's C compiler driver and the runtime library built with this test executable.
/// Cargo keeps a `libzed_native-<hash>.a` beside it for each set of features it has built
/// zed-native with, and the newest need not be this build's, so the library is picked by the
/// symbol it shares with this executable (`runtime_of`), not by its time.
pub(crate) fn toolchain() -> Toolchain {
    let exe = std::env::current_exe().unwrap();
    let runtime = runtime_of(&exe, exe.parent().unwrap()).unwrap_or_else(|e| panic!("{e}"));
    Toolchain {
        linker: "cc".into(),
        runtime,
    }
}

/// The program in `src` built into the executable `out`.
pub(crate) fn built(src: &Path, out: &Path) {
    let mut warnings = Vec::new();
    if let Err((status, why)) = build(src.to_str().unwrap(), out, &toolchain(), &mut warnings) {
        panic!("building {}: status {status}: {why}", src.display());
    }
}

/// What a run gives: its exit status and the bytes it writes to standard output and error.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Ran {
    pub status: u8,
    pub stdout: String,
    pub stderr: String,
}

/// The executable `exe` run on the words `words` after its name, with `stdin` as its input.
pub(crate) fn executable(exe: &Path, words: &[OsString], stdin: &[u8]) -> Ran {
    let mut child = Command::new(exe)
        .args(words)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("{}: {e}", exe.display()));
    // A program that reads no input may exit before taking it all.
    match child.stdin.take().unwrap().write_all(stdin) {
        Err(e) if e.kind() != std::io::ErrorKind::BrokenPipe => panic!("{}: {e}", exe.display()),
        _ => {}
    }
    let out = child.wait_with_output().unwrap();
    Ran {
        status: u8::try_from(out.status.code().expect("an exit status")).unwrap(),
        stdout: String::from_utf8(out.stdout).unwrap(),
        stderr: String::from_utf8(out.stderr).unwrap(),
    }
}

/// The program in `src` run by `zedc run` on the same words and input.
pub(crate) fn interpreter(src: &Path, words: &[OsString], stdin: &[u8]) -> Ran {
    let mut all: Vec<OsString> = vec!["run".into(), src.into()];
    all.extend(words.iter().cloned());
    let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&all, &mut &stdin[..], &mut stdout, &mut stderr);
    Ran {
        status,
        stdout: String::from_utf8(stdout).unwrap(),
        stderr: String::from_utf8(stderr).unwrap(),
    }
}
