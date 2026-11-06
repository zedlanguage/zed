//! Each step program and each enabled fence and corpus program, built twice, gives the same
//! bytes, and its executable gives the interpreter's outputs and exit status on every corpus
//! input, the inputs of the harness of step L1.37; a program reading the files its arguments
//! name agrees on a present file, a missing one, a directory, a file that is not UTF-8 and such
//! an argument.

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt as _;
use std::path::Path;

use zed_tests::oracle::{self, ENABLED};

use super::{Ran, built, dir, executable, interpreter};

/// Builds `src` twice under different names, checks the two executables are the same bytes,
/// and returns the path of the first.
fn built_twice(name: &str, src: &Path) -> std::path::PathBuf {
    let d = dir(name);
    let (one, two) = (d.join(name), d.join(format!("{name}-again")));
    built(src, &one);
    built(src, &two);
    let (a, b) = (std::fs::read(&one).unwrap(), std::fs::read(&two).unwrap());
    assert!(a == b, "two builds of {} differ", src.display());
    one
}

/// The step program `name` (of step L1.21's programs) built twice and run under both engines
/// on every corpus input.
fn step_program_agrees(name: &str) {
    let src = oracle::step_units()
        .into_iter()
        .find(|p| p.file_stem().is_some_and(|s| s == name))
        .unwrap();
    let exe = built_twice(name, &src);
    let corpus = oracle::corpus();
    for (c, _) in &corpus {
        let input = std::fs::read(c.with_extension("in")).unwrap();
        let native = executable(&exe, &[], &input);
        assert_eq!(
            native,
            interpreter(&src, &[], &input),
            "{name} on {}",
            c.display()
        );
    }
    assert_eq!(corpus.len(), 31);
}

#[test]
fn the_step_programs_are_exactly_these() {
    // A step unit with `main` is a program; the others are units with no ports.
    let programs: Vec<String> = oracle::step_units()
        .iter()
        .filter(|p| zedc::run::load(&std::fs::read(p).unwrap()).is_ok())
        .map(|p| p.file_stem().unwrap().to_string_lossy().into_owned())
        .collect();
    assert_eq!(programs, ["config", "fahrenheit", "greeting", "username"]);
}

#[test]
fn config_agrees() {
    step_program_agrees("config");
}

#[test]
fn fahrenheit_agrees() {
    step_program_agrees("fahrenheit");
}

#[test]
fn greeting_agrees() {
    step_program_agrees("greeting");
}

#[test]
fn username_agrees() {
    step_program_agrees("username");
}

#[test]
fn every_enabled_corpus_program_agrees() {
    let enabled: Vec<_> = oracle::corpus()
        .into_iter()
        .filter(|(_, l)| *l <= ENABLED)
        .collect();
    // The corpus begins at L3; each program joins when its layer is enabled.
    assert_eq!(enabled.len(), 0);
    for (src, _) in enabled {
        let name = src.file_stem().unwrap().to_string_lossy().into_owned();
        let exe = built_twice(&name, &src);
        let input = std::fs::read(src.with_extension("in")).unwrap();
        let native = executable(&exe, &[], &input);
        assert_eq!(native, interpreter(&src, &[], &input), "{}", src.display());
        let out = std::fs::read_to_string(src.with_extension("out")).unwrap();
        assert_eq!((native.status, native.stdout), (0, out));
    }
}

#[test]
fn every_enabled_fence_program_agrees() {
    // A fence with `main` is a program; the enabled fences at L1 are units with no ports.
    let programs: Vec<_> = zed_tests::fences::all()
        .into_iter()
        .filter(|f| f.layer <= ENABLED && !f.notation)
        .filter(|f| zedc::run::load(f.text.as_bytes()).is_ok())
        .collect();
    assert_eq!(programs.len(), 0);
    let d = dir("fences");
    for (k, f) in programs.iter().enumerate() {
        let src = d.join(format!("fence{k}.zed"));
        std::fs::write(&src, &f.text).unwrap();
        let exe = built_twice(&format!("fence{k}"), &src);
        let native = executable(&exe, &[], b"");
        assert_eq!(native, interpreter(&src, &[], b""), "{}", f.at);
    }
}

/// Reads the files its three arguments name, and says which are missing or unreadable.
const READER: &str = "main(fs: Files, args: CommandLine) -> (stdout: Lines) {\n  \
    a = (fs[args[1] else \"\"] else #notFound -> \"missing\") else #ioError -> \"unreadable\";\n  \
    b = (fs[args[2] else \"\"] else #notFound -> \"missing\") else #ioError -> \"unreadable\";\n  \
    c = (fs[args[3] else \"\"] else #notFound -> \"missing\") else #ioError -> \"unreadable\";\n  \
    stdout <- \"${a}|${b}|${c}\";\n}\n";

#[test]
fn files_named_by_arguments_agree() {
    let d = dir("reader");
    let src = d.join("reader.zed");
    std::fs::write(&src, READER).unwrap();
    std::fs::write(d.join("present.txt"), "hello").unwrap();
    std::fs::write(d.join("binary.txt"), b"\xff\xfe").unwrap();
    let exe = built_twice("reader", &src);
    let path = |f: &str| OsString::from(d.join(f));
    let cases: Vec<(Vec<OsString>, Ran)> = vec![
        (
            vec![
                "--".into(),
                path("present.txt"),
                path("absent.txt"),
                path("binary.txt"),
            ],
            Ran {
                status: 0,
                stdout: "hello|missing|unreadable\n".into(),
                stderr: String::new(),
            },
        ),
        (
            // A directory is no file, and a missing argument reads the file named by "", which is
            // missing.
            vec!["--".into(), d.clone().into_os_string()],
            Ran {
                status: 0,
                stdout: "unreadable|missing|missing\n".into(),
                stderr: String::new(),
            },
        ),
        (
            vec![
                "--".into(),
                "a".into(),
                OsString::from_vec(vec![b'x', 0xff]),
            ],
            Ran {
                status: 2,
                stdout: String::new(),
                stderr: "command-line argument 2 is not UTF-8\n".into(),
            },
        ),
        (
            vec!["nope=x".into()],
            Ran {
                status: 2,
                stdout: String::new(),
                stderr: "`main` has no port `nope`\n".into(),
            },
        ),
    ];
    for (words, want) in &cases {
        let native = executable(&exe, words, b"");
        assert_eq!(&native, want, "{words:?}");
        assert_eq!(native, interpreter(&src, words, b""), "{words:?}");
    }
    // A word the executable does not know is a usage error naming the executable.
    let bad = executable(&exe, &["bad".into()], b"");
    assert_eq!(bad.status, 2);
    assert_eq!(
        bad.stderr,
        format!(
            "usage: {} [port=path …] [--record <out>] [-- arg …]\n",
            exe.display()
        )
    );
}

/// Compares its first two arguments by `>` and `>=`, which legalization rewrites for this back
/// end, the comparison not known before the run.
const ORDER: &str = "main(args: CommandLine) -> (stdout: Lines) {\n  \
    a = args[1] else \"\";\n  \
    b = args[2] else \"\";\n  \
    x = if a > b { \"after\" } else { \"not after\" };\n  \
    y = if a >= b { \"at or after\" } else { \"before\" };\n  \
    stdout <- \"${x}|${y}\";\n}\n";

#[test]
fn a_built_comparison_by_greater_than_agrees() {
    let d = dir("order");
    let src = d.join("order.zed");
    std::fs::write(&src, ORDER).unwrap();
    let exe = built_twice("order", &src);
    for (a, b, want) in [
        ("b", "a", "after|at or after\n"),
        ("a", "a", "not after|at or after\n"),
        ("a", "b", "not after|before\n"),
    ] {
        let words: Vec<OsString> = vec!["--".into(), a.into(), b.into()];
        let native = executable(&exe, &words, b"");
        assert_eq!(
            (native.status, native.stdout.as_str()),
            (0, want),
            "{a} {b}"
        );
        assert_eq!(native, interpreter(&src, &words, b""), "{a} {b}");
    }
}

#[test]
fn a_record_of_the_executable_replays_under_the_interpreter() {
    let d = dir("record");
    let src = d.join("reader.zed");
    std::fs::write(&src, READER).unwrap();
    std::fs::write(d.join("present.txt"), "recorded").unwrap();
    let exe = built_twice("record", &src);
    let record = d.join("run.record");
    let words: Vec<OsString> = vec![
        "--record".into(),
        record.clone().into(),
        "--".into(),
        d.join("present.txt").into(),
    ];
    let native = executable(&exe, &words, b"");
    assert_eq!(native.stdout, "recorded|missing|missing\n");
    // The file changes; the replay reads the recorded contents.
    std::fs::write(d.join("present.txt"), "changed").unwrap();
    let replay: Vec<OsString> = vec!["replay".into(), src.into(), record.into()];
    let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&replay, &mut &b""[..], &mut stdout, &mut stderr);
    assert_eq!(
        (
            status,
            String::from_utf8(stdout).unwrap(),
            String::from_utf8(stderr).unwrap()
        ),
        (0, native.stdout, native.stderr)
    );
}
