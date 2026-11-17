//! The output of zedc is the same under two draws of the treap priorities
//! (PERF-treap-seeded-priorities, module `zed_kernel::priority`): each corpus program run on its
//! input, each step unit's tests, and programs rejected with messages that print unions, run by
//! the zedc executable under `ZED_TREAP_SEED=1` and `ZED_TREAP_SEED=2`, give the same exit
//! status and the same bytes on standard output and standard error. A treap's shape follows the
//! draw, so this fails if any shape reaches what zedc prints. `crates/zed-native/Cargo.toml`
//! names this test, since only a test of that package can name the executable.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

/// This process's scratch directory, as the step tests have it. A test target of zed-native
/// cannot depend on zed-tests, so the module is compiled in; a target may use part of it.
#[allow(dead_code)]
#[path = "../../src/scratch.rs"]
mod scratch;

/// The repository's directory of `name`, from this package's.
fn repo(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(name)
}

/// Programs that are rejected with a note that prints the type the checker found for `f`, a
/// union of atoms or of literals of several kinds, `k` of them, in the order of types (the
/// order of digests), as a printed set's members are.
fn rejected() -> Vec<String> {
    let chain = |k: usize, value: &dyn Fn(usize) -> String| {
        let mut body = value(0);
        for i in 1..k {
            body = format!("if n > {i} {{ {} }} else {{ {body} }}", value(i));
        }
        format!(
            "f(n: int) = {body};\nmain(m: MainArgs) {{\n  m.stdout <- f(int(m.args[0]) else 0);\n}}\n"
        )
    };
    let mixed = |i: usize| match i % 3 {
        0 => format!("{}", 7 * i + 3),
        1 => format!("\"s{i}\""),
        _ => format!("#k{i}"),
    };
    vec![
        chain(4, &|i| ["#gray", "#blue", "#green", "#red"][i].to_string()),
        chain(4, &|i| ["#none", "\"x\"", "7", "11"][i].to_string()),
        chain(64, &|i| format!("#a{i}")),
        chain(64, &mixed),
        "main(m: MainArgs) {\n  b = 2^64 + 13;\n  m.stdout <- String(rat(f64(b) ^ (2^64)));\n}\n"
            .into(),
    ]
}

/// `zedc <words>` under the draw `seed`, given `input`, run in `dir`.
fn zedc(seed: u32, words: &[&std::ffi::OsStr], input: &[u8], dir: &Path) -> Output {
    use std::io::Write;
    let mut child = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .args(words)
        .current_dir(dir)
        .env("ZED_TREAP_SEED", seed.to_string())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("zedc starts");
    let mut stdin = child.stdin.take().expect("a pipe");
    let input = input.to_vec();
    let feed = std::thread::spawn(move || {
        // A program that reads no input closes the pipe early; that is not an error here.
        let _ = stdin.write_all(&input);
    });
    let out = child.wait_with_output().expect("zedc runs");
    feed.join().expect("the input is written");
    out
}

/// One run of zedc to compare: a name, the words and the input.
struct Case {
    name: String,
    words: Vec<std::ffi::OsString>,
    input: Vec<u8>,
    /// Text the run must print on standard error, so that the case prints what it is here for.
    shows: &'static str,
}

fn cases() -> Vec<Case> {
    let mut out = Vec::new();
    let corpus = repo("zed/corpus");
    let mut programs: Vec<PathBuf> = std::fs::read_dir(&corpus)
        .expect("the corpus")
        .map(|e| e.expect("an entry").path())
        .filter_map(|p| {
            if p.extension().is_some_and(|x| x == "zed") {
                Some(p)
            } else if p.join("zed.manifest").is_file() {
                Some(p.join("main.zed"))
            } else {
                None
            }
        })
        .collect();
    programs.sort();
    assert_eq!(programs.len(), 31, "the corpus programs");
    for p in programs {
        let base = match p.file_name().is_some_and(|f| f == "main.zed") {
            true => p.parent().expect("a package root").to_path_buf(),
            false => p.clone(),
        };
        out.push(Case {
            name: p.display().to_string(),
            words: vec!["run".into(), p.clone().into()],
            input: std::fs::read(base.with_extension("in")).expect("the program's input"),
            shows: "",
        });
    }
    let mut units: Vec<PathBuf> = Vec::new();
    for step in std::fs::read_dir(repo("tests/steps")).expect("the steps") {
        if let Ok(entries) = std::fs::read_dir(step.expect("an entry").path().join("zed")) {
            units.extend(entries.map(|e| e.expect("an entry").path()));
        }
    }
    units.sort();
    assert!(units.len() >= 13, "the step units: {units:?}");
    for u in units {
        out.push(Case {
            name: u.display().to_string(),
            words: vec!["test".into(), u.into()],
            input: Vec::new(),
            shows: "",
        });
    }
    for (i, text) in rejected().iter().enumerate() {
        let f = scratch::scratch(format!("treap_seeds_{i}.zed"));
        std::fs::write(&f, text).expect("the program is written");
        out.push(Case {
            name: format!("rejected program {i}"),
            words: vec!["run".into(), f.into()],
            input: Vec::new(),
            shows: if i < 4 {
                "the type the checker found for `f` is"
            } else {
                "gives String | #invalid"
            },
        });
    }
    out
}

#[test]
fn the_output_is_the_same_under_two_draws_of_the_treap_priorities() {
    let dir = scratch::scratch("treap_seeds_dir");
    std::fs::create_dir_all(&dir).expect("a directory");
    let cases = cases();
    std::thread::scope(|s| {
        for c in &cases {
            let dir = &dir;
            s.spawn(move || {
                let words: Vec<&std::ffi::OsStr> = c.words.iter().map(|w| w.as_os_str()).collect();
                let one = zedc(1, &words, &c.input, dir);
                let two = zedc(2, &words, &c.input, dir);
                assert_eq!(one.status.code(), two.status.code(), "{}", c.name);
                assert!(
                    one.stdout == two.stdout,
                    "{}: standard output differs:\n{}\n---\n{}",
                    c.name,
                    String::from_utf8_lossy(&one.stdout),
                    String::from_utf8_lossy(&two.stdout)
                );
                assert!(
                    one.stderr == two.stderr,
                    "{}: standard error differs:\n{}\n---\n{}",
                    c.name,
                    String::from_utf8_lossy(&one.stderr),
                    String::from_utf8_lossy(&two.stderr)
                );
                let err = String::from_utf8_lossy(&one.stderr);
                assert!(err.contains(c.shows), "{}: {err}", c.name);
            });
        }
    });
}
