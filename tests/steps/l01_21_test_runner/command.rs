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
        (0, "4 passed, 0 failed\n".into(), String::new())
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
        format!("{a}:1:45: `2 -> 5` of `double`: the result is 4\n1 passed, 1 failed\n")
    );
    assert_eq!(err, "");
}

#[test]
fn a_file_that_is_not_utf8_fails_and_a_missing_file_is_a_usage_error() {
    let bad = unit("bad.zed", "x = 1;\n");
    std::fs::write(&bad, [0xffu8, 0xfe]).unwrap();
    let (status, out, _) = run(&[&bad]);
    assert_eq!(status, 1);
    assert!(
        out.starts_with(&format!("{bad}: ")) && out.ends_with("0 passed, 1 failed\n"),
        "{out}"
    );
    let (status, _, err) = run(&["/nonexistent/zed-l01-21.zed"]);
    assert_eq!(status, 2);
    assert!(err.starts_with("/nonexistent/zed-l01-21.zed: "), "{err}");
    assert_eq!(
        run(&[]),
        (2, String::new(), "usage: zedc test <file> …\n".into())
    );
}
