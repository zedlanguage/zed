//! Step L1.36a: `zedc build file -o out` links the object file of step L1.36 with the runtime
//! library into an executable, which binds its ports from its own command line as `zedc run`
//! does and exits with the same statuses. Two builds of a program give the same bytes, and the
//! executable's outputs and exit status equal the interpreter's.

mod agreement;
mod scaling;

use std::ffi::OsString;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use zed_native::link::{Toolchain, build};

/// A directory of its own for test `name`, under the test target's scratch directory; files
/// in it are overwritten by each run, never deleted.
pub(crate) fn dir(name: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("l01_36a")
        .join(name);
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The system's C compiler driver and the runtime library this test was built with. Cargo
/// writes the library of a dependency only beside this executable, under its hash, so the
/// newest `libzed_native-*.a` there is the one built from the current source.
pub(crate) fn toolchain() -> Toolchain {
    let exe = std::env::current_exe().unwrap();
    let deps = exe.parent().unwrap();
    let runtime = std::fs::read_dir(deps)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| {
            let name = p.file_name().unwrap().to_string_lossy();
            name.starts_with("libzed_native-") && name.ends_with(".a")
        })
        .max_by_key(|p| std::fs::metadata(p).unwrap().modified().unwrap())
        .unwrap_or_else(|| panic!("no libzed_native-*.a in {}", deps.display()));
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
