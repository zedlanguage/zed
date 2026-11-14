//! `zedc build`, `zedc run` and `zedc replay` take the staged program (plan row
//! STAGE-commands): an executable holds the string of the branch of `if build.target == …` or
//! `if build.options.<name> …` that its build takes and not the other's; a run's record names
//! the program's address as checked, before staging, so it replays.

use std::path::{Path, PathBuf};

use zedc::build::Build;
use zedc::run::{Record, load_for};
use zedc::work::{self, Stage, Work};

use zed_tests::step_helpers::l01_36a_executables::{executable, toolchain};

/// A directory of its own for test `name` holding `files`, under the test target's scratch
/// directory; files in it are overwritten by each run, never deleted.
fn dir(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = zed_tests::step_helpers::target_tmpdir()
        .join("l02_08d_staged")
        .join(name);
    for (file, text) in files {
        let path = d.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    d
}

/// The target of the machine the test runs on, the one a build is for.
fn host() -> String {
    Build::default().target().to_string()
}

/// A target no test machine is: `build.target == OTHER` is false on every one.
const OTHER: &str = "x86_64-windows";

/// A program that writes one line of two parts: the first from a branch on the host's target, which is
/// taken, and the second from a branch on [`OTHER`], which is not. The strings are long and
/// distinct, so each is found in an executable only if its branch was compiled.
fn by_target() -> String {
    format!(
        "main(m: MainArgs) {{
  m.stdout <- (if build.target == \"{host}\" {{
    \"taken: the branch for the target of this build\"
  }} else {{
    \"dropped: the branch for every other target\"
  }}) ++ \" / \" ++ (if build.target == \"{OTHER}\" {{
    \"dropped: the branch for a target no test machine is\"
  }} else {{
    \"taken: the branch for the targets other than that one\"
  }});
}}
",
        host = host()
    )
}

/// What `zedc build` of `file`, with the options `on` turned on, writes: the executable's bytes
/// and what it writes to standard output when run.
fn built(file: &Path, on: &[&str]) -> (Vec<u8>, String) {
    let out = file.with_extension("exe");
    let mut warnings = Vec::new();
    zed_native::link::build(
        file.to_str().unwrap(),
        &out,
        on,
        &mut Default::default(),
        &toolchain(),
        &mut warnings,
    )
    .unwrap_or_else(|(status, why)| panic!("{}: status {status}: {why}", file.display()));
    let ran = executable(&out, &[], b"");
    assert_eq!(
        (ran.status, ran.stderr.as_str()),
        (0, ""),
        "{}",
        file.display()
    );
    (std::fs::read(&out).unwrap(), ran.stdout)
}

/// Whether `bytes` hold `text`.
fn holds(bytes: &[u8], text: &str) -> bool {
    bytes.windows(text.len()).any(|w| w == text.as_bytes())
}

#[test]
fn an_executable_holds_the_string_of_the_taken_branch_only() {
    let d = dir("target", &[("main.zed", &by_target())]);
    let (exe, out) = built(&d.join("main.zed"), &[]);
    assert_eq!(
        out,
        "taken: the branch for the target of this build / \
         taken: the branch for the targets other than that one\n"
    );
    for line in [
        "taken: the branch for the target of this build",
        "taken: the branch for the targets other than that one",
    ] {
        assert!(holds(&exe, line), "the executable lacks `{line}`");
    }
    // The control of the string search: both lines are in the program as lowered unstaged.
    for line in [
        "dropped: the branch for every other target",
        "dropped: the branch for a target no test machine is",
    ] {
        assert!(
            super::lowered(&by_target(), &Build::default(), false).contains(line),
            "{line}"
        );
        assert!(!holds(&exe, line), "the executable holds `{line}`");
    }
}

#[test]
fn an_executable_holds_the_string_of_the_options_branch_only() {
    let d = dir(
        "options",
        &[
            ("zed.manifest", "options = \"fast\";\n"),
            (
                "app/main.zed",
                "main(m: MainArgs) {\n  m.stdout <- if build.options.fast {\n    \"the fast \
                 build, with the option turned on\"\n  } else {\n    \"the slow build, with \
                 the option left off\"\n  };\n}\n",
            ),
        ],
    );
    let file = d.join("app/main.zed");
    let (on, off) = (
        "the fast build, with the option turned on",
        "the slow build, with the option left off",
    );
    for (options, kept, cut) in [(&["fast"][..], on, off), (&[][..], off, on)] {
        let (exe, out) = built(&file, options);
        assert_eq!(out, format!("{kept}\n"), "{options:?}");
        assert!(
            holds(&exe, kept),
            "{options:?}: the executable lacks `{kept}`"
        );
        assert!(
            !holds(&exe, cut),
            "{options:?}: the executable holds `{cut}`"
        );
    }
}

/// The rows of `zedc <words>` counted by stage, with its status.
fn reported(words: &[&str]) -> (u8, Vec<Stage>) {
    let (status, report) = work::with(Box::new(Work::default), || {
        let (mut out, mut err) = (Vec::new(), Vec::new());
        zedc::run::command(words, &mut "".as_bytes(), &mut out, &mut err)
    });
    (status, report.rows.iter().map(|r| r.stage).collect())
}

#[test]
fn run_and_replay_stage_the_program() {
    let d = dir("record", &[("main.zed", &by_target())]);
    let (file, rec) = (d.join("main.zed"), d.join("wave.rec"));
    let (file, rec) = (file.to_str().unwrap(), rec.to_str().unwrap());
    let (status, stages) = reported(&["run", file, "--record", rec]);
    assert_eq!(status, 0);
    assert!(stages.contains(&Stage::Staging), "{stages:?}");
    // Staging changes the term `main` runs here, and the program keeps its address.
    let p = load_for(by_target().as_bytes(), &Build::default()).unwrap();
    let staged = p.stage().0;
    assert_ne!(
        staged.ports().address(staged.term()).unwrap(),
        p.address().unwrap()
    );
    assert_eq!(staged.address().unwrap(), p.address().unwrap());
    // So the record names the program as checked, which the library loads.
    let record = Record::from_bytes(&std::fs::read(rec).unwrap()).unwrap();
    assert_eq!(record.program, Some(p.address().unwrap()));
    let (status, stages) = reported(&["replay", file, rec]);
    assert_eq!(status, 0);
    assert!(stages.contains(&Stage::Staging), "{stages:?}");
    // Staging a staged program keeps the address of the first.
    assert_eq!(staged.stage().0.address().unwrap(), p.address().unwrap());
}

/// A package whose manifest declares the options `o0` to `o<n-1>` and whose `main` writes
/// `n` letters, `a` where the build turns option `o<i>` on and `b` where it does not.
fn branches(n: usize) -> PathBuf {
    let options: Vec<String> = (0..n).map(|i| format!("o{i}")).collect();
    let letters: Vec<String> = options
        .iter()
        .map(|o| format!("(if build.options.{o} {{ \"a\" }} else {{ \"b\" }})"))
        .collect();
    dir(
        &format!("branches-{n}"),
        &[
            (
                "zed.manifest",
                &format!("options = \"{}\";\n", options.join(", ")),
            ),
            (
                "app/main.zed",
                &format!(
                    "main(m: MainArgs) {{ m.stdout <- {}; }}\n",
                    letters.join(" ++ ")
                ),
            ),
        ],
    )
}

/// The words of `zedc run` of [`branches`]`(n)` with every other option turned on.
pub(super) fn run_words(n: usize) -> Vec<String> {
    let file = branches(n).join("app/main.zed");
    let mut words = vec!["run".to_string(), file.to_str().unwrap().to_string()];
    for i in (0..n).step_by(2) {
        words.extend(["--option".to_string(), format!("o{i}")]);
    }
    words
}

/// The output of a run is the letters of the branches its build takes; the time of a run is
/// held linear in the branches in `bench/staged.rs`.
#[test]
fn run_of_a_few_option_branches_writes_the_letters_its_build_takes() {
    for (n, letters) in [(1, "a"), (2, "ab"), (6, "ababab")] {
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let status = zedc::run::command(&run_words(n), &mut "".as_bytes(), &mut out, &mut err);
        let err = String::from_utf8(err).unwrap();
        assert_eq!(status, 0, "{err}");
        assert_eq!(String::from_utf8(out).unwrap(), format!("{letters}\n"));
    }
}
