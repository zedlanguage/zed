//! Step L1.36b: the key of a link names everything that enters the executable by its content,
//! not by its path: the object file, the runtime library's bytes, the linker's version as its
//! driver reports it, and the link's other arguments (`zed_native::link::Identity`). The
//! executable records the key as its GNU build ID, and a build whose output already records
//! the key it would link with does not link again. A changed program, runtime library or
//! linker gives another key, and the build links; the same toolchain reached by other paths
//! gives the same key, and the build does not.

#![cfg(target_os = "linux")]

mod bench;
mod cache;
mod deps;
mod identity;
mod leftover;
mod scaling;
mod sources;

use std::path::{Path, PathBuf};

use zed_native::link::{Toolchain, build};
use zedc::work::{self, Stage, Work};

pub(crate) use zed_tests::step_helpers::l01_36a_executables::{executable, toolchain};

/// A directory of its own for test `name`, under the test target's scratch directory; files
/// in it are overwritten by each run, never deleted, so a test's first build may find its
/// output from the run before.
pub(crate) fn dir(name: &str) -> PathBuf {
    let d = zed_tests::step_helpers::target_tmpdir()
        .join("l01_36b")
        .join(name);
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// What a build did at its link.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Link {
    /// It ran the linker.
    Ran,
    /// Its output already recorded the key of the link, and it was left as it was.
    Kept,
}

/// Builds the program in `src` into `out` with `tools`, and says whether it linked, as the
/// report of `zedc --report build` counts its link row: computed or cached.
pub(crate) fn link(src: &Path, out: &Path, tools: &Toolchain) -> Link {
    let (built, report) = work::with(Box::new(Work::default), || {
        build(
            src.to_str().unwrap(),
            out,
            &[],
            &mut Default::default(),
            tools,
            &mut Vec::new(),
        )
    });
    if let Err((status, why)) = built {
        panic!("building {}: status {status}: {why}", src.display());
    }
    let row = report
        .rows
        .iter()
        .find(|r| r.stage == Stage::Link)
        .expect("a build has a row of its link");
    match (row.computed, row.cached) {
        (1, 0) => Link::Ran,
        (0, 1) => Link::Kept,
        counts => panic!("one build linked (computed, cached) = {counts:?} times"),
    }
}

/// The results of `cases`, each run on a thread of its own, all at once. A link takes a second
/// or more, most of it the linker reading the runtime library, so a test whose cases each link
/// on an output of their own runs them at once rather than one after another.
pub(crate) fn at_once<R: Send>(cases: &[&(dyn Fn() -> R + Sync)]) -> Vec<R> {
    std::thread::scope(|s| {
        let threads: Vec<_> = cases.iter().map(|case| s.spawn(case)).collect();
        threads
            .into_iter()
            .map(|t| t.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
            .collect()
    })
}

/// A copy at `copy` of the executable `out` and its record: an output last linked as `out`
/// was, since the output's path enters neither the key nor the bytes. A test that changes an
/// input links the copy with it and leaves `out` as it was, so the next run finds `out` linked
/// with the inputs of its first build and keeps it, where it would link it again. `cp` writes
/// the copy in a process of its own, for the reason given at [`script`].
pub(crate) fn copied(out: &Path, copy: &Path) {
    use zed_native::link::Record;
    for (from, to) in [
        (out.to_path_buf(), copy.to_path_buf()),
        (Record::path(out), Record::path(copy)),
    ] {
        let status = std::process::Command::new("cp")
            .arg(&from)
            .arg(&to)
            .status()
            .unwrap();
        assert!(
            status.success(),
            "cp {} {}: {status}",
            from.display(),
            to.display()
        );
    }
}

/// The program of a shop's sign: it writes `text` on one line.
pub(crate) fn sign(text: &str) -> String {
    format!("main(m: MainArgs) {{\n  m.stdout <- \"{text}\";\n}}\n")
}

/// Writes the shell script `body` at `path`, runnable. `install` writes it in a process of its
/// own: a file this process held open for writing could be inherited by a child that another
/// test thread forks at that moment, and running the script would then fail with "Text file
/// busy" (ETXTBSY).
pub(crate) fn script(path: &Path, body: &str) {
    let text = path.with_extension("text");
    std::fs::write(&text, format!("#!/bin/sh\n{body}")).unwrap();
    let installed = std::process::Command::new("install")
        .arg("-m")
        .arg("755")
        .arg(&text)
        .arg(path)
        .status()
        .unwrap();
    assert!(
        installed.success(),
        "install {}: {installed}",
        path.display()
    );
}

/// A C compiler driver at `path` that runs `cc` for a link, and writes `version` for
/// `--version` and `linker` for `-Wl,--version`, or what `cc` writes where `None`: a
/// toolchain whose driver or linker is another release than the system's, linking the same.
pub(crate) fn driver(path: &Path, version: Option<&str>, linker: Option<&str>) {
    let case = |arg: &str, says: Option<&str>| {
        says.map(|s| format!("{arg}) printf '%s\\n' '{s}' ;;\n"))
            .unwrap_or_default()
    };
    script(
        path,
        &format!(
            "case \"$1\" in\n{}{}*) exec cc \"$@\" ;;\nesac\n",
            case("--version", version),
            case("-Wl,--version", linker)
        ),
    );
}
