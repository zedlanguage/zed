//! `zedc run` and `zedc build` write the pins into the package's files: each unit file keeps its
//! own bytes, line endings included, around the pins, a second build writes nothing, and the
//! pin file is written at the package root.

use std::path::{Path, PathBuf};

/// A package directory of its own for test `name`, holding `files`, under this process's
/// scratch directory; files in it are overwritten by each run, never deleted.
fn package_dir(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = zed_tests::step_helpers::scratch(format!("l02_08/{name}"));
    for (file, text) in files {
        let path = d.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    d
}

/// Runs `zedc run <file>` and gives its status and standard error.
fn run(file: &Path) -> (u8, String) {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(
        &["run", file.to_str().unwrap()],
        &mut "".as_bytes(),
        &mut out,
        &mut err,
    );
    (status, String::from_utf8(err).unwrap())
}

/// The text of `file`.
fn read(file: &Path) -> String {
    String::from_utf8(std::fs::read(file).unwrap()).unwrap()
}

/// The lines of `err` that are not about forms of later steps.
fn mistakes(err: &str) -> Vec<&str> {
    err.lines().filter(|l| !zed_tests::is_not_yet(l)).collect()
}

#[test]
fn a_run_writes_the_pins_and_a_second_run_writes_nothing() {
    let d = package_dir(
        "writes",
        &[
            ("zed.manifest", "// the shop\n"),
            (
                "app/main.zed",
                "import pricing.{net};\nmain(m: MainArgs) {}\n",
            ),
            ("pricing.zed", "net(g: f64) = g / 1.2;\n"),
        ],
    );
    let main = d.join("app/main.zed");
    let (_, err) = run(&main);
    assert_eq!(mistakes(&err), Vec::<&str>::new(), "{err}");
    let pinned = read(&main);
    let h = super::pin_in(&pinned, 0);
    assert_eq!(
        pinned,
        format!("import pricing.{{net}} @hash(\"{h}\");\nmain(m: MainArgs) {{}}\n")
    );
    // No prelude unit, so no pin file.
    assert!(!d.join("zed.pins").exists());
    let modified = std::fs::metadata(&main).unwrap().modified().unwrap();
    let (_, err) = run(&main);
    assert_eq!(mistakes(&err), Vec::<&str>::new(), "{err}");
    assert_eq!(read(&main), pinned);
    // Nothing was written: the file is the one the first run wrote.
    assert_eq!(
        std::fs::metadata(&main).unwrap().modified().unwrap(),
        modified
    );
}

#[test]
fn a_file_with_crlf_lines_keeps_them_around_its_pins() {
    let d = package_dir(
        "crlf",
        &[
            ("zed.manifest", "// the shop\r\n"),
            (
                "main.zed",
                "// till\r\nimport pricing;\r\nimport pricing as p;\r\nmain(m: MainArgs) {}\r\n",
            ),
            ("pricing.zed", "net(g: f64) = g / 1.2;\r\n"),
        ],
    );
    let main = d.join("main.zed");
    let (_, err) = run(&main);
    assert_eq!(mistakes(&err), Vec::<&str>::new(), "{err}");
    let pinned = read(&main);
    let h = super::pin_in(&pinned, 0);
    assert_eq!(
        pinned,
        format!(
            "// till\r\nimport pricing @hash(\"{h}\");\r\nimport pricing as p @hash(\"{h}\");\r\n\
             main(m: MainArgs) {{}}\r\n"
        )
    );
}

#[test]
fn a_file_with_lone_cr_or_mixed_line_ends_keeps_them_around_its_pins() {
    // The pin writer changes no line end (author, 2026-11-13, QUESTIONS A90): a pin goes inside
    // its import line, and every other byte of the file stays.
    for (name, text, want) in [
        (
            "lone-cr",
            "// till\rimport pricing;\rmain(m: MainArgs) {}\r",
            "// till\rimport pricing @hash(\"H\");\rmain(m: MainArgs) {}\r",
        ),
        (
            "mixed",
            "// till\r\nimport pricing;\rimport pricing as p;\nmain(m: MainArgs) {}\r\n",
            "// till\r\nimport pricing @hash(\"H\");\rimport pricing as p @hash(\"H\");\n\
             main(m: MainArgs) {}\r\n",
        ),
    ] {
        let d = package_dir(
            name,
            &[
                ("zed.manifest", "// the shop\n"),
                ("main.zed", text),
                ("pricing.zed", "net(g: f64) = g / 1.2;\n"),
            ],
        );
        let main = d.join("main.zed");
        let (_, err) = run(&main);
        assert_eq!(mistakes(&err), Vec::<&str>::new(), "{name}: {err}");
        let pinned = read(&main);
        let h = super::pin_in(&pinned, 0);
        assert_eq!(pinned, want.replace('H', &h), "{name}");
    }
}

#[test]
fn the_pin_file_ends_its_lines_with_lf_beside_a_crlf_manifest() {
    // `zed.pins` is written whole by the toolchain, with `\n` (author, 2026-11-13, QUESTIONS
    // A90), whatever the line ends of the package's other files.
    let d = package_dir(
        "prelude-crlf",
        &[
            ("zed.manifest", "// the shop\r\nprelude = \"std\";\r\n"),
            ("std.zed", "double(x: f64) = x * 2.0;\r\n"),
            ("app/main.zed", "main(m: MainArgs) {}\r\n"),
        ],
    );
    let pins = d.join("zed.pins");
    if pins.exists() {
        std::fs::write(&pins, "").unwrap();
    }
    let (_, err) = run(&d.join("app/main.zed"));
    assert_eq!(mistakes(&err), Vec::<&str>::new(), "{err}");
    let text = read(&pins);
    assert!(text.starts_with("// Pins written by zedc"), "{text}");
    assert!(!text.contains('\r'), "{text:?}");
    assert_eq!(text.matches('\n').count(), 2, "{text:?}");
    // The manifest keeps its own line ends.
    assert_eq!(
        read(&d.join("zed.manifest")),
        "// the shop\r\nprelude = \"std\";\r\n"
    );
}

#[test]
fn a_stale_pin_stops_the_run_at_the_import_in_its_file() {
    let d = package_dir(
        "stale",
        &[
            ("zed.manifest", "// the shop\n"),
            ("main.zed", "import pricing;\nmain(m: MainArgs) {}\n"),
            ("pricing.zed", "net(g: f64) = g / 1.2;\n"),
        ],
    );
    let main = d.join("main.zed");
    run(&main);
    let pinned = read(&main);
    std::fs::write(d.join("pricing.zed"), "net(g: f64) = g / 1.25;\n").unwrap();
    let (status, err) = run(&main);
    assert_eq!(status, 1, "{err}");
    let root = d.display();
    assert!(
        err.contains(&format!(
            "{root}/main.zed:1:1: the import of the unit `pricing` is pinned to the content address"
        )),
        "{err}"
    );
    // The stale pin is left as it was written.
    assert_eq!(read(&main), pinned);
}

#[test]
fn the_prelude_pin_is_written_into_the_pin_file_at_the_root() {
    let d = package_dir(
        "prelude",
        &[
            ("zed.manifest", "prelude = \"std\";\n"),
            ("std.zed", "double(x: f64) = x * 2.0;\n"),
            ("app/main.zed", "main(m: MainArgs) {}\n"),
        ],
    );
    let pins = d.join("zed.pins");
    if pins.exists() {
        // Left by an earlier run of this test: the run must write it again, and the same.
        std::fs::write(&pins, "").unwrap();
    }
    let main = d.join("app/main.zed");
    let (_, err) = run(&main);
    assert_eq!(mistakes(&err), Vec::<&str>::new(), "{err}");
    let text = read(&pins);
    assert!(text.starts_with("// Pins written by zedc"), "{text}");
    let line = text.lines().nth(1).unwrap();
    assert!(
        line.starts_with("prelude ") && line.ends_with(" std"),
        "{text}"
    );
    assert_eq!(text.lines().count(), 2, "{text}");
    let (_, err) = run(&main);
    assert_eq!(mistakes(&err), Vec::<&str>::new(), "{err}");
    assert_eq!(read(&pins), text);
}
