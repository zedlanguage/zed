//! `zedc test` runs the tables on the program staged as `zedc run` stages it (plan row
//! TEST-staged): for the host's target and the options `--option` turns on, or for the target
//! `--target <t>` names. A row of a function that only branches the build does not take reach
//! is not run, and is listed as such; a function the build evaluates, or one `main` does not
//! reach, has its rows run.

use std::path::PathBuf;

use zedc::build::{Build, TARGETS};
use zedc::query::Db;
use zedc::testing::{self, command};

/// A directory of its own for test `name` holding `files`, under the test target's scratch
/// directory; files in it are overwritten by each run, never deleted.
fn dir(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = zed_tests::step_helpers::target_tmpdir()
        .join("l02_08d_test_staged")
        .join(name);
    for (file, text) in files {
        let path = d.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    d
}

/// What `zedc test <words>` gives: its status, standard output and standard error.
fn test(words: &[&str]) -> (u8, String, String) {
    let words: Vec<String> = words.iter().map(|w| w.to_string()).collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = command(&words, &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// The target of the machine the test runs on.
fn host() -> String {
    Build::default().target().to_string()
}

/// A target that is not the host's.
fn other() -> &'static str {
    let host = host();
    TARGETS.iter().find(|&&t| t != host).unwrap()
}

/// A program whose `main` calls `here` on the host's target and `there` on every other, each
/// with a row that fails, so a row that runs is seen to run. `there` calls `deeper`, which
/// nothing else reaches; `both` is reached from both branches.
fn by_target() -> String {
    format!(
        "deeper(positional x) = x ++ \"?\" test {{ \"d\" -> \"wrong\" }}
there(positional x) = deeper(x) ++ \"!\" test {{ \"a\" -> \"wrong\" }}
here(positional x) = x ++ \".\" test {{ \"b\" -> \"wrong\" }}
both(positional x) = x test {{ \"c\" -> \"c\" }}
main(m: MainArgs) {{
  m.stdout <- if build.target == \"{host}\" {{ here(both(\"x\")) }} else {{ there(both(\"y\")) }};
}}
",
        host = host()
    )
}

#[test]
fn a_row_of_a_branch_the_build_does_not_take_is_listed_as_not_run() {
    let d = dir("target", &[("main.zed", &by_target())]);
    let file = d.join("main.zed").display().to_string();
    let (status, out, err) = test(&[&file]);
    let host = host();
    assert_eq!(
        (status, out.as_str(), err.as_str()),
        (
            1,
            format!(
                "{file}:1:40: `\"d\" -> \"wrong\"` of `deeper`: not run, since the build for \
                 `{host}` takes no branch that reaches `deeper`\n\
                 {file}:2:47: `\"a\" -> \"wrong\"` of `there`: not run, since the build for \
                 `{host}` takes no branch that reaches `there`\n\
                 {file}:3:38: `\"b\" -> \"wrong\"` of `here`: the result is \"b.\"\n\
                 1 passed, 1 failed, 2 not run, 0 rejection units\n"
            )
            .as_str(),
            ""
        )
    );
    // `--target` names the other build: the rows of `here` are those not run, and those of
    // `there` and `deeper` run and fail.
    let other = other();
    let (status, out, _) = test(&["--target", other, &file]);
    assert_eq!(status, 1);
    assert_eq!(
        out,
        format!(
            "{file}:1:40: `\"d\" -> \"wrong\"` of `deeper`: the result is \"d?\"\n\
             {file}:2:47: `\"a\" -> \"wrong\"` of `there`: the result is \"a?!\"\n\
             {file}:3:38: `\"b\" -> \"wrong\"` of `here`: not run, since the build for \
             `{other}` takes no branch that reaches `here`\n\
             1 passed, 2 failed, 1 not run, 0 rejection units\n"
        )
    );
}

#[test]
fn rows_not_run_do_not_fail_the_run() {
    let d = dir(
        "pass",
        &[(
            "main.zed",
            &format!(
                "there(positional x) = x test {{ \"a\" -> \"wrong\" }}
here(positional x) = x test {{ \"b\" -> \"b\" }}
main(m: MainArgs) {{
  m.stdout <- if build.target == \"{}\" {{ there(\"x\") }} else {{ here(\"y\") }};
}}
",
                other()
            ),
        )],
    );
    let file = d.join("main.zed").display().to_string();
    assert_eq!(
        test(&[&file]),
        (
            0,
            format!(
                "{file}:1:32: `\"a\" -> \"wrong\"` of `there`: not run, since the build for \
                 `{}` takes no branch that reaches `there`\n\
                 1 passed, 0 failed, 1 not run, 0 rejection units\n",
                host()
            ),
            String::new()
        )
    );
}

#[test]
fn option_turns_the_rows_not_run_over() {
    let d = dir(
        "options",
        &[
            ("zed.manifest", "options = \"fast, counting\";\n"),
            (
                "app/main.zed",
                "quick(positional x) = x ++ \"q\" test { \"a\" -> \"aq\" }
slow(positional x) = x ++ \"s\" test { \"a\" -> \"as\" }
main(m: MainArgs) {
  m.stdout <- if build.options.fast { quick(\"x\") } else { slow(\"y\") };
}
",
            ),
        ],
    );
    let file = d.join("app/main.zed").display().to_string();
    let host = host();
    assert_eq!(
        test(&[&file]),
        (
            0,
            format!(
                "{file}:1:39: `\"a\" -> \"aq\"` of `quick`: not run, since the build for \
                 `{host}` takes no branch that reaches `quick`\n\
                 1 passed, 0 failed, 1 not run, 0 rejection units\n"
            ),
            String::new()
        )
    );
    assert_eq!(
        test(&["--option", "fast", "--option", "counting", &file]),
        (
            0,
            format!(
                "{file}:2:38: `\"a\" -> \"as\"` of `slow`: not run, since the build for \
                 `{host}` with `--option fast` and `--option counting` takes no branch that \
                 reaches `slow`\n\
                 1 passed, 0 failed, 1 not run, 0 rejection units\n"
            ),
            String::new()
        )
    );
    // `zedc run` takes the same branch under each set of options.
    for (on, wrote) in [(&[][..], "ys\n"), (&["--option", "fast"][..], "xq\n")] {
        let mut words = vec!["run", &file];
        words.extend(on);
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let status = zedc::run::command(&words, &mut "".as_bytes(), &mut out, &mut err);
        assert_eq!(status, 0, "{}", String::from_utf8_lossy(&err));
        assert_eq!(String::from_utf8(out).unwrap(), wrote);
    }
}

#[test]
fn a_function_the_build_evaluates_or_main_does_not_reach_has_its_rows_run() {
    // `make` is reached only through `table`, which the build evaluates, so the staged
    // program does not read it; `alone` is read by no definition. Both rows run and fail.
    let d = dir(
        "evaluated",
        &[(
            "main.zed",
            "make(positional n) = n * 10 test { 3 -> 31 }
alone(positional n) = n test { 1 -> 2 }
table = make(3);
main(m: MainArgs) {
  m.stdout <- if table == 30 { \"thirty\" } else { \"other\" };
}
",
        )],
    );
    let file = d.join("main.zed").display().to_string();
    let (status, out, _) = test(&[&file]);
    assert_eq!(status, 1);
    assert_eq!(
        out,
        format!(
            "{file}:1:36: `3 -> 31` of `make`: the result is 30\n\
             {file}:2:32: `1 -> 2` of `alone`: the result is 1\n\
             0 passed, 2 failed, 0 rejection units\n"
        )
    );
}

#[test]
fn a_unit_with_no_main_runs_every_row() {
    // A library has no program to stage: each function is an entry, and each row runs.
    let d = dir(
        "library",
        &[(
            "lib.zed",
            &format!(
                "there(positional x) = x test {{ \"a\" -> \"a\" }}
here(positional x) = x test {{ \"b\" -> \"b\" }}
pick(positional x) = if build.target == \"{}\" {{ there(x) }} else {{ here(x) }} \
                 test {{ \"c\" -> \"c\" }}
",
                other()
            ),
        )],
    );
    let file = d.join("lib.zed").display().to_string();
    assert_eq!(
        test(&[&file]),
        (
            0,
            "3 passed, 0 failed, 0 rejection units\n".to_string(),
            String::new()
        )
    );
}

#[test]
fn test_and_run_stage_the_same_program() {
    let d = dir(
        "same",
        &[
            ("zed.manifest", "options = \"fast\";\n"),
            (
                "app/main.zed",
                "quick(positional x) = x ++ \"q\" test { \"a\" -> \"aq\" }
slow(positional x) = x ++ \"s\" test { \"a\" -> \"as\" }
main(m: MainArgs) {
  m.stdout <- if build.options.fast { quick(\"x\") } else { slow(\"y\") };
}
",
            ),
        ],
    );
    let file = d.join("app/main.zed");
    let place = zedc::place::Place::of(&file).unwrap();
    let text = std::fs::read_to_string(&file).unwrap();
    let mut terms = Vec::new();
    for on in [&[][..], &["fast"][..]] {
        let build = zedc::unit::package_build(&place, on).unwrap();
        let mut db = Db::for_build(build);
        let front = db.front(&text);
        let Ok((stmts, unit, _)) = &*front else {
            panic!("the unit is accepted")
        };
        let (tested, _) = testing::program_of(stmts, unit).unwrap();
        let run = zedc::run::load_file(
            file.to_str().unwrap(),
            on,
            &mut Default::default(),
            &mut Vec::new(),
        )
        .unwrap_or_else(|(_, why)| panic!("{why}"));
        assert_eq!(tested.term(), run.term(), "{on:?}");
        terms.push(run.term());
    }
    // The control: the two builds stage different programs.
    assert_ne!(terms[0], terms[1]);
}

#[test]
fn target_is_a_usage_error_when_it_names_no_target() {
    let d = dir("usage", &[("main.zed", &by_target())]);
    let file = d.join("main.zed").display().to_string();
    let (status, out, err) = test(&["--target", "x86_64-linx", &file]);
    assert_eq!((status, out.as_str()), (2, ""));
    assert_eq!(
        err,
        "`--target x86_64-linx`: `x86_64-linx` is no target. Write one of `x86_64-linux`, \
         `aarch64-linux`, `riscv64-linux`, `x86_64-macos`, `aarch64-macos`, `x86_64-windows` \
         and `aarch64-windows`.\n"
    );
    let (status, _, err) = test(&[&file, "--target"]);
    assert_eq!(status, 2);
    assert!(
        err.starts_with("`--target` is the last word of the command line"),
        "{err}"
    );
    let (status, _, err) = test(&["--target", "x86_64-linux", "--target", other(), &file]);
    assert_eq!(status, 2);
    assert_eq!(
        err,
        format!(
            "`--target x86_64-linux` and `--target {}`: a build is for one target. Keep one \
             `--target`.\n",
            other()
        )
    );
}

/// A program of `n` functions on the branch of the host's target and `n` on the branch of
/// another, each with one row that passes, the functions of each branch called in one chain.
fn branches(n: usize) -> PathBuf {
    let mut text = String::new();
    for side in ["t", "u"] {
        for i in 0..n {
            text += &format!("{side}{i}(positional x) = x ++ \"-\" test {{ \"a\" -> \"a-\" }}\n");
        }
    }
    let chain = |side: &str| (0..n).fold("\"\"".to_string(), |s, i| format!("{side}{i}({s})"));
    text += &format!(
        "main(m: MainArgs) {{\n  m.stdout <- if build.target == \"{}\" {{ {} }} else {{ {} }};\n}}\n",
        host(),
        chain("t"),
        chain("u")
    );
    dir(&format!("scaling-{n}"), &[("main.zed", &text)]).join("main.zed")
}

#[test]
fn test_of_n_taken_and_n_dropped_functions_is_linear() {
    // The control: the rows of the taken branch run, and those of the other are not run.
    let file = branches(3);
    let (status, out, err) = test(&[file.to_str().unwrap()]);
    assert_eq!((status, err.as_str()), (0, ""), "{out}");
    assert_eq!(out.matches(": not run, since").count(), 3, "{out}");
    assert!(
        out.ends_with("3 passed, 0 failed, 3 not run, 0 rejection units\n"),
        "{out}"
    );
    let inputs = zed_tests::scaling::inputs(100, branches);
    zed_tests::scaling::check_order(
        "`zedc test` of n functions on a taken branch and n on a dropped one",
        100,
        1,
        |n| {
            let file = inputs[&n].to_str().unwrap();
            let (status, out, _) = test(&[file]);
            assert_eq!(status, 0);
            assert!(out.ends_with(&format!("{n} not run, 0 rejection units\n")));
        },
    );
}

#[test]
fn mutate_runs_no_row_that_test_does_not_run() {
    // `slow`'s row would detect its mutants; it is not run, so they are undetected with that
    // reason, while `quick`'s are detected by its row, which runs.
    let d = dir(
        "mutate",
        &[(
            "main.zed",
            &format!(
                "quick(positional n) = n + 1 test {{ 1 -> 2 }}
slow(positional n) = n + 2 test {{ 1 -> 3 }}
main(m: MainArgs) {{
  m.stdout <- if build.target == \"{}\" {{ if slow(1) == 3 {{ \"s\" }} else {{ \"t\" }} }} \
                 else {{ if quick(1) == 2 {{ \"q\" }} else {{ \"r\" }} }};
}}
",
                other()
            ),
        )],
    );
    let file = d.join("main.zed").display().to_string();
    let (status, out, err) = test(&["--mutate", &file]);
    assert_eq!((status, err.as_str()), (0, ""), "{out}");
    let why = "the build takes no branch that reaches the definition, so no row that reaches \
               it runs";
    // The mutants of `main` are not about rows not run; the comparison leaves them out, and
    // leaves out the place in the elaborated term, which changes with the carriers.
    let out: String = out
        .lines()
        .filter(|l| !l.contains("in `main` at"))
        .map(|l| match l.split_once(" at .") {
            Some((head, tail)) => format!("{head}{}\n", &tail[tail.find(": ").unwrap()..]),
            None => l.to_owned() + "\n",
        })
        .collect();
    assert_eq!(
        out,
        format!(
            "{file}:2:35: `1 -> 3` of `slow`: not run, since the build for `{host}` takes no \
             branch that reaches `slow`\n\
             1 passed, 0 failed, 1 not run, 0 rejection units\n\
             {file}:2:24: undetected: `+` replaced by `-` in `slow`: {why}\n\
             {file}:2:26: undetected: `2` replaced by `1` in `slow`: {why}\n\
             {file}:2:26: undetected: `2` replaced by `3` in `slow`: {why}\n\
             17 mutants: 3 detected, 9 undetected, 5 skipped, 0 not run\n",
            host = host()
        )
    );
}
