//! `zedc test <file> …`.

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
    let dir = std::env::temp_dir().join("zed-l01-21");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path.display().to_string()
}

#[test]
fn passing_units_exit_zero_with_the_counts() {
    let a = unit(
        "pass.zed",
        "double(positional x) = x * 2 test { 0 -> 0, 2 -> 4 }\n",
    );
    assert_eq!(
        run(&[&a, &a]),
        (
            0,
            "4 passed, 0 failed, 0 rejection units\n".into(),
            String::new()
        )
    );
}

#[test]
fn a_failing_check_is_printed_at_its_file_and_line() {
    let a = unit(
        "fail.zed",
        "double(positional x) = x * 2 test { 0 -> 0, 2 -> 5 }\n",
    );
    let (status, out, err) = run(&[&a]);
    assert_eq!(status, 1);
    assert_eq!(
        out,
        format!(
            "{a}:1:45: `2 -> 5` of `double`: the result is 4\n1 passed, 1 failed, 0 rejection units\n"
        )
    );
    assert_eq!(err, "");
}

#[test]
fn a_file_that_is_not_utf8_fails_and_a_missing_file_is_a_usage_error() {
    let bad = unit("bad.zed", "x = 1;\n");
    std::fs::write(&bad, [0xffu8, 0xfe]).unwrap();
    let (status, out, _) = run(&[&bad]);
    assert_eq!(status, 1);
    assert_eq!(
        out,
        format!("{bad}: 1:1: not UTF-8: FF\n0 passed, 1 failed, 0 rejection units\n")
    );
    let (status, _, err) = run(&["/nonexistent/zed-l01-21.zed"]);
    assert_eq!(status, 2);
    assert!(err.starts_with("/nonexistent/zed-l01-21.zed: "), "{err}");
    assert_eq!(
        run(&[]),
        (
            2,
            String::new(),
            "usage: zedc test [--mutate] [--suppress <address> …] <file> …\n".into()
        )
    );
}

#[test]
fn a_unit_with_no_tests_fails_so_a_run_that_finds_none_fails() {
    let a = unit("none.zed", "vat(positional price: rat) = price * 1.2r;\n");
    assert_eq!(
        run(&[&a]),
        (
            1,
            format!(
                "{a}: no test: the unit has no table row and no ✗ mark\n\
                 0 passed, 1 failed, 0 rejection units\n"
            ),
            String::new()
        )
    );
}

#[test]
fn the_rejection_units_run_are_counted() {
    let pass = unit(
        "counted.zed",
        "double(positional x) = x * 2 test { 2 -> 4 }\n",
    );
    let rejected = unit(
        "rejected.zed",
        "fee(positional amount: int, rate: int) = amount * rate;\n\
         f = fee(rate: 3);    // ✗ Missing argument: amount is positional\n",
    );
    assert_eq!(
        run(&[&pass, &rejected, &rejected]),
        (
            0,
            "3 passed, 0 failed, 2 rejection units\n".into(),
            String::new()
        )
    );
}

#[test]
fn a_rejection_unit_that_compiles_fails() {
    let a = unit(
        "compiles.zed",
        "fee(positional amount: int, rate: int) = amount * rate;\n\
         f = fee(5, rate: 3);    // ✗ Missing argument: but none is\n",
    );
    assert_eq!(
        run(&[&a]),
        (
            1,
            format!(
                "{a}:2:1: the line is marked ✗ and the unit is accepted\n\
                 0 passed, 1 failed, 1 rejection unit\n"
            ),
            String::new()
        )
    );
}

#[test]
fn a_rejection_unit_with_a_table_fails_each_row_and_exits_non_zero() {
    // The rows cannot run, since the unit does not compile; two of them are wrong, and the
    // file must not report success.
    let a = unit(
        "rows-rejected.zed",
        "inc(positional x: int) = x + 1\n\
         test { 1 -> 999, 2 -> 3, 5 -> \"wrong\" }\n\
         bad = inc();    // ✗ Missing argument: x\n",
    );
    assert_eq!(
        run(&[&a]),
        (
            1,
            format!(
                "{a}:2:8: `1 -> 999` of `inc`: not run, since the unit is rejected\n\
                 {a}:2:18: `2 -> 3` of `inc`: not run, since the unit is rejected\n\
                 {a}:2:26: `5 -> \"wrong\"` of `inc`: not run, since the unit is rejected\n\
                 1 passed, 3 failed, 1 rejection unit\n"
            ),
            String::new()
        )
    );
}

#[test]
fn a_unit_that_does_not_compile_and_a_row_that_aborts_fail() {
    let bad = unit("type.zed", "total = 3 + \"pounds\";\n");
    let (status, out, _) = run(&[&bad]);
    assert_eq!(status, 1, "{out}");
    assert!(
        out.ends_with("0 passed, 1 failed, 0 rejection units\n"),
        "{out}"
    );
    let aborts = unit(
        "aborts.zed",
        "share(positional total: int, positional people: int) = total div people \
         test { (10, 0) -> 0 }\n",
    );
    let (status, out, _) = run(&[&aborts]);
    assert_eq!(status, 1, "{out}");
    assert!(
        out.ends_with("0 passed, 1 failed, 0 rejection units\n"),
        "{out}"
    );
}
