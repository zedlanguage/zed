//! `zedc build` refuses, with its exit status and a message naming what is wrong, each command
//! line, tool and output it cannot build with (DESIGN.md step L1.36a; `link::command` and
//! `link::build` called in this process): a command line not of the form `<file> -o <out>`, a
//! runtime library that is not an archive, a linker that cannot be run or whose link fails,
//! and an output path that names a directory or lies in a directory that does not exist. The
//! linker of each of these fails before it links, or is a script that does not link, so only
//! the output that is a directory costs a real link.

use std::path::{Path, PathBuf};
use std::process::Command;

use zed_native::link::{Toolchain, USAGE, command};
use zed_tests::step_helpers::l01_36a_executables::toolchain;

use super::dir;

/// A program that builds, written in the directory of test `name`.
fn program(name: &str) -> (PathBuf, PathBuf) {
    let d = dir(name);
    let src = d.join("quiet.zed");
    std::fs::write(&src, "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n").unwrap();
    (d, src)
}

/// `zedc build` with the words `words` after `build`: its status and standard error.
fn build(words: &[&str], tools: &Toolchain) -> (u8, String) {
    let words: Vec<String> = words.iter().map(|w| (*w).to_string()).collect();
    let mut stderr = Vec::new();
    let status = command(&words, tools, &mut stderr);
    (status, String::from_utf8(stderr).unwrap())
}

/// Writes `text` at `path` as a runnable file, in a process of its own: a file this process
/// held open for writing could be inherited by a child another test thread forks at that
/// moment, and running it would then fail with "Text file busy" (ETXTBSY). As `binary.rs`
/// does.
fn install(path: &Path, text: &str, mode: &str) {
    let staged = path.with_extension("text");
    std::fs::write(&staged, text).unwrap();
    let installed = Command::new("install")
        .args(["-m", mode])
        .arg(&staged)
        .arg(path)
        .status()
        .unwrap();
    assert!(
        installed.success(),
        "install {}: {installed}",
        path.display()
    );
}

/// The working directories builds of `out` left beside it (`<out>.zed-build.<pid>.<k>`).
fn left(out: &Path) -> Vec<String> {
    let mut prefix = out.file_name().unwrap().to_owned();
    prefix.push(".zed-build.");
    let prefix = prefix.into_string().unwrap();
    std::fs::read_dir(out.parent().unwrap())
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.starts_with(&prefix))
        .collect()
}

#[test]
fn a_command_line_not_of_the_form_file_o_out_is_a_usage_error() {
    let tools = toolchain();
    let usage = (2, format!("{USAGE}\n"));
    for words in [
        &[][..],
        &["a.zed"],
        &["a.zed", "-o"],
        &["-o", "out"],
        &["a.zed", "-x", "out"],
        &["-o", "out", "a.zed"],
        &["a.zed", "-o", "out", "extra"],
        &["a.zed", "b.zed", "-o", "out"],
        &["--addresses"],
        &["--option", "fast"],
    ] {
        assert_eq!(build(words, &tools), usage, "{words:?}");
    }
    // A `--suppress` or `--option` with nothing after it is named before the form is read.
    for (words, starts) in [
        (
            &["a.zed", "-o", "out", "--suppress"][..],
            "`--suppress` is the last word",
        ),
        (
            &["a.zed", "-o", "out", "--suppress", "zz"],
            "`--suppress zz`: `zz` is not an address",
        ),
        (
            &["a.zed", "-o", "out", "--option"],
            "`--option` is the last word",
        ),
    ] {
        let (status, stderr) = build(words, &tools);
        assert_eq!(status, 2, "{words:?}: {stderr}");
        assert!(stderr.starts_with(starts), "{words:?}: {stderr}");
    }
}

#[test]
fn a_runtime_library_that_is_not_an_archive_is_named() {
    let (d, src) = program("not-an-archive");
    let runtime = d.join("libzed_native-text.a");
    std::fs::write(&runtime, "not an archive\n").unwrap();
    let tools = Toolchain {
        runtime: runtime.clone(),
        ..toolchain()
    };
    let out = d.join("quiet");
    let (status, stderr) = build(
        &[src.to_str().unwrap(), "-o", out.to_str().unwrap()],
        &tools,
    );
    let starts = format!(
        "zedc cannot build an executable: it could not check that the runtime library {} was \
         built with it: {}: ",
        runtime.display(),
        runtime.display()
    );
    assert_eq!(status, 2, "{stderr}");
    assert!(stderr.starts_with(&starts), "{stderr}");
    assert!(!out.exists());
}

#[test]
fn a_linker_that_cannot_be_run_is_named() {
    let (d, src) = program("not-runnable");
    let linker = d.join("cc-not-runnable");
    install(&linker, "#!/bin/sh\nexec cc \"$@\"\n", "644");
    let tools = Toolchain {
        linker: linker.clone().into(),
        ..toolchain()
    };
    let out = d.join("quiet");
    assert_eq!(
        build(
            &[src.to_str().unwrap(), "-o", out.to_str().unwrap()],
            &tools
        ),
        (
            1,
            format!(
                "zedc could not run the linker `{}`: Permission denied (os error 13). Repair: \
                 name in the environment variable CC a C compiler that can be run\n",
                linker.display()
            )
        )
    );
    assert!(!out.exists());
}

#[test]
fn a_link_that_fails_is_named_with_what_the_linker_printed() {
    let (d, src) = program("link-fails");
    // The driver gives the system compiler's versions, and refuses every link.
    let linker = d.join("cc-refuses");
    install(
        &linker,
        "#!/bin/sh\ncase \"$1\" in --version|-Wl,--version) exec cc \"$@\" ;; esac\n\
         echo 'the link is refused' >&2\nexit 1\n",
        "755",
    );
    let tools = Toolchain {
        linker: linker.clone().into(),
        ..toolchain()
    };
    let out = d.join("quiet");
    let l = linker.display();
    assert_eq!(
        build(
            &[src.to_str().unwrap(), "-o", out.to_str().unwrap()],
            &tools
        ),
        (
            1,
            format!(
                "zedc could not link {}: the linker `{l}` failed (exit status: 1). Repair: check \
                 that `{l}` links C programs, or name another C compiler in the environment \
                 variable CC. The linker printed:\nthe link is refused\n",
                out.display()
            )
        )
    );
    // The working directory, with the object file in it, is removed.
    assert!(!out.exists());
    assert_eq!(left(&out), Vec::<String>::new());
}

#[test]
fn an_output_that_names_no_file_is_refused() {
    let (d, src) = program("output-paths");
    let tools = toolchain();
    // `d/..` has no file name: there is no file of that name to write.
    let parent = d.join("..");
    assert_eq!(
        build(
            &[src.to_str().unwrap(), "-o", parent.to_str().unwrap()],
            &tools
        ),
        (
            2,
            format!(
                "zedc cannot build {p}: the path after `-o` names a directory, not a file. \
                 Repair: name the executable to write, as in `-o {p}/program`\n",
                p = parent.display()
            )
        )
    );
    // An output in a directory that does not exist: its working directory cannot be made.
    let missing = d.join("no-such-directory").join("quiet");
    let (status, stderr) = build(
        &[src.to_str().unwrap(), "-o", missing.to_str().unwrap()],
        &tools,
    );
    let starts = format!(
        "zedc could not write {}.zed-build.{}.",
        missing.display(),
        std::process::id()
    );
    let ends = format!(
        " while building {m}: No such file or directory (os error 2). Repair: check that the \
         directory of {m} exists and can be written, and that the disk has room\n",
        m = missing.display()
    );
    assert_eq!(status, 1, "{stderr}");
    assert!(
        stderr.starts_with(&starts) && stderr.ends_with(&ends),
        "{stderr}"
    );
}

#[test]
fn an_output_that_is_a_directory_is_left_as_it_is() {
    let (d, src) = program("output-directory");
    let out = d.join("a-directory");
    std::fs::create_dir_all(out.join("inside")).unwrap();
    let (status, stderr) = build(
        &[src.to_str().unwrap(), "-o", out.to_str().unwrap()],
        &toolchain(),
    );
    let starts = format!(
        "zedc could not write {o} while building {o}: ",
        o = out.display()
    );
    assert_eq!(status, 1, "{stderr}");
    assert!(stderr.starts_with(&starts), "{stderr}");
    assert!(out.join("inside").is_dir());
    assert_eq!(left(&out), Vec::<String>::new());
}
