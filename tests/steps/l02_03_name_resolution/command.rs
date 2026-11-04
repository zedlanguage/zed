//! `zedc run` on a unit of a package: a unit under a manifest that imports a unit is read with
//! its package, and the package's problems are reported in its files; a unit that imports
//! nothing runs as a single file does.

use std::path::PathBuf;

/// A package directory of its own for test `name`, holding `files`, under the test target's
/// scratch directory; files in it are overwritten by each run, never deleted.
fn package_dir(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("l02_03")
        .join(name);
    for (file, text) in files {
        let path = d.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    d
}

/// Runs `zedc run <file>` and gives its status and standard error.
fn run(file: &str) -> (u8, String) {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&["run", file], &mut "".as_bytes(), &mut out, &mut err);
    (status, String::from_utf8(err).unwrap())
}

#[test]
fn a_unit_with_imports_reports_its_package_in_the_files_of_its_units() {
    let d = package_dir(
        "imports",
        &[
            ("zed.manifest", "// the root of the shop's package\n"),
            (
                "app/main.zed",
                "import pricing.{net, gross};\nmain() -> (stdout: Lines) {}\n",
            ),
            ("pricing.zed", "net(g: f64) = g / 1.2;\n"),
        ],
    );
    let main = d.join("app/main.zed");
    let (status, err) = run(main.to_str().unwrap());
    assert_eq!(status, 1, "{err}");
    let root = d.display();
    assert!(
        err.contains(&format!(
            "{root}/app/main.zed:1:1: the unit `pricing` defines no `gross`"
        )),
        "{err}"
    );
    assert!(
        err.contains(&format!(
            "{root}/app/main.zed:1:1: an import is linked from step L2.4, which ties each name \
             it brings in to the other unit's definition"
        )),
        "{err}"
    );
}

#[test]
fn a_unit_with_no_import_under_a_manifest_runs_as_a_single_file() {
    let d = package_dir(
        "alone",
        &[
            ("zed.manifest", "// no prelude\n"),
            (
                "hello.zed",
                "main() -> (stdout: Lines) {\n  stdout <- \"hello\";\n}\n",
            ),
        ],
    );
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let file = d.join("hello.zed");
    let status = zedc::run::command(
        &["run", file.to_str().unwrap()],
        &mut "".as_bytes(),
        &mut out,
        &mut err,
    );
    assert_eq!(status, 0, "{}", String::from_utf8_lossy(&err));
    assert_eq!(String::from_utf8(out).unwrap(), "hello\n");
}

#[test]
fn a_file_whose_name_is_no_unit_path_is_reported() {
    let d = package_dir(
        "badname",
        &[
            ("zed.manifest", ""),
            (
                "my-app.zed",
                "import pricing;\nmain() -> (stdout: Lines) {}\n",
            ),
        ],
    );
    let (status, err) = run(d.join("my-app.zed").to_str().unwrap());
    assert_eq!(status, 1);
    assert_eq!(
        err,
        "the file `my-app.zed` names no unit: `my-app` is not a name, and each directory under \
         the package root and the file's stem must be one\n"
    );
}
