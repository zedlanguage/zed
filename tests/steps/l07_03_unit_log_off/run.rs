//! A unit with `@log(#off);` checks and runs as it does without it: the item binds nothing and
//! gives no value. With no log port before step L7.3 there is no line for it to drop yet.

use zedc::testing::test;

/// Runs `zedc <command> <file>`, the file holding `src`, with `stdin`; its status, standard
/// output and standard error.
fn zedc(command: &str, name: &str, src: &str, stdin: &str) -> (u8, String, String) {
    let file = zed_tests::step_helpers::scratch(format!("l07_03/{name}.zed"));
    std::fs::create_dir_all(file.parent().unwrap()).unwrap();
    std::fs::write(&file, src).unwrap();
    let args = [command.to_string(), file.to_str().unwrap().to_string()];
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&args, &mut stdin.as_bytes(), &mut out, &mut err);
    std::fs::remove_file(&file).unwrap();
    let text = |b| String::from_utf8(b).unwrap();
    (status, text(out), text(err))
}

const GREETER: &str = "\
greeting(name) = \"Hello, ${name}!\";

main(m: MainArgs) {
  m.stdout <- greeting(name: \"world\");
}
";

#[test]
fn a_program_runs_the_same_with_the_unit_item() {
    let plain = zedc("run", "plain", GREETER, "");
    let quiet = zedc("run", "quiet", &format!("@log(#off);\n\n{GREETER}"), "");
    assert_eq!(quiet, (0, "Hello, world!\n".into(), String::new()));
    assert_eq!(quiet, plain);
}

#[test]
fn the_test_tables_of_a_unit_with_the_item_run() {
    let src = "square(positional x) = x * x test { 2 -> 4, 3 -> 9 }\n";
    let ok = |text: &str| {
        test(text)
            .into_iter()
            .map(|o| (o.line, o.failure))
            .collect::<Vec<_>>()
    };
    assert_eq!(ok(&format!("@log(#off);\n\n{src}")), [(3, None), (3, None)]);
    assert_eq!(ok(src), [(1, None), (1, None)]);
}

#[test]
fn a_refused_unit_item_stops_the_run_with_its_message() {
    let (status, out, err) = zedc("run", "on", &format!("@log(#on);\n{GREETER}"), "");
    assert_ne!(status, 0);
    assert_eq!(out, "");
    assert!(
        err.contains(":1:1: the unit item `@log` takes the one argument `#off`"),
        "{err}"
    );
}
