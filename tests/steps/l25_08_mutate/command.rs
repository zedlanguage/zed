//! `zedc test --mutate <file> …`: the exit status follows `zedc test` (step L1.21), and a run
//! of several files reports each as a run of that file alone does.

use zedc::testing::command;

fn run(args: &[&str]) -> (u8, String, String) {
    let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = command(&args, &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

fn unit(name: &str, text: &str) -> String {
    let dir = std::env::temp_dir().join("zed-l25-08");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path.display().to_string()
}

#[test]
fn undetected_mutants_do_not_change_the_exit_status() {
    let a = unit(
        "minor.zed",
        "isMinor(positional age) = age < 18 test { 5 -> true, 40 -> false }\n",
    );
    let (status, out, err) = run(&["--mutate", &a]);
    assert_eq!((status, err.as_str()), (0, ""));
    assert_eq!(
        out,
        format!(
            "2 passed, 0 failed, 0 rejection units\n\
             {a}:1:31: undetected: `<` replaced by `<=` in `isMinor` at .0.1: every row that \
             reaches it passes\n\
             {a}:1:33: undetected: `18` replaced by `17` in `isMinor` at .0.1.1.4: every row that \
             reaches it passes\n\
             {a}:1:33: undetected: `18` replaced by `19` in `isMinor` at .0.1.1.4: every row that \
             reaches it passes\n\
             3 mutants: 0 detected, 3 undetected, 0 skipped, 0 not run\n"
        )
    );
}

#[test]
fn a_program_whose_own_tests_fail_exits_non_zero_and_runs_no_mutant() {
    let a = unit(
        "fails.zed",
        "isChild(positional age) = age < 12 test { 12 -> true, 13 -> false }\n",
    );
    let (status, out, _) = run(&["--mutate", &a]);
    assert_eq!(status, 1);
    assert_eq!(
        out,
        format!(
            "{a}:1:43: `12 -> true` of `isChild`: the result is false\n\
             1 passed, 1 failed, 0 rejection units\n\
             no mutant runs: the original's checks fail\n"
        )
    );
}

#[test]
fn a_program_that_does_not_compile_exits_non_zero_and_runs_no_mutant() {
    let a = unit(
        "broken.zed",
        "isChild(positional age) = age <= test { 12 -> true }\n",
    );
    let (status, out, _) = run(&["--mutate", &a]);
    assert_eq!(status, 1);
    assert!(
        out.ends_with(
            "0 passed, 1 failed, 0 rejection units\nno mutant runs: the original's checks fail\n"
        ),
        "{out}"
    );
}

#[test]
fn a_usage_error_names_the_flag() {
    let (status, out, err) = run(&["--mutate"]);
    assert_eq!(
        (status, out.as_str(), err.as_str()),
        (
            2,
            "",
            "usage: zedc test [--mutate] [--suppress <address> …] [--addresses] [--option <name> …] <file> …\n"
        )
    );
}

#[test]
fn several_files_report_as_each_file_alone() {
    let a = unit(
        "batch-a.zed",
        "isMinor(positional age) = age < 18 test { 5 -> true, 40 -> false }\n",
    );
    let b = unit(
        "batch-b.zed",
        "limit = 10;\nscale(positional x: int) = x * (2 + 0) test { 3 -> 6 }\n",
    );
    // A rejection unit has no mutants.
    let c = unit(
        "batch-c.zed",
        "x = 1 ++ 2;  // ✗ Operator with no arrow at its operands' carrier: `++` joins strings\n",
    );
    let mutant_lines = |out: &str| -> Vec<String> {
        out.lines()
            .filter(|l| l.contains(" replaced by "))
            .map(String::from)
            .collect()
    };
    let (status, batch, _) = run(&["--mutate", &a, &b, &c]);
    assert_eq!(status, 0, "{batch}");
    let mut alone = Vec::new();
    for f in [&a, &b, &c] {
        let (status, out, _) = run(&["--mutate", f]);
        assert_eq!(status, 0, "{out}");
        alone.extend(mutant_lines(&out));
    }
    assert_eq!(mutant_lines(&batch), alone);
    assert!(
        batch.ends_with("10 mutants: 4 detected, 5 undetected, 1 skipped, 0 not run\n"),
        "{batch}"
    );
}
