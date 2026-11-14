//! `zedc run` on a unit of a package: a unit under a manifest that imports a unit is read with
//! its package, and the package's problems are reported in its files; a unit that imports
//! nothing runs as a single file does.

use std::path::PathBuf;

/// A package directory of its own for test `name`, holding `files`, under this process's
/// scratch directory; files in it are overwritten by each run, never deleted.
fn package_dir(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = zed_tests::step_helpers::scratch(format!("l02_03/{name}"));
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
                "import pricing.{net, gross};\nmain(m: MainArgs) {}\n",
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
            "{root}/app/main.zed:1:1: {}",
            zed_tests::IMPORT_NOT_YET
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
                "main(m: MainArgs) {\n  m.stdout <- \"hello\";\n}\n",
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
            ("my-app.zed", "import pricing;\nmain(m: MainArgs) {}\n"),
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

#[test]
fn a_cycle_is_reported_alike_by_each_of_its_units_run_alone_and_by_the_whole_package() {
    let d = package_dir(
        "cycle",
        &[
            ("zed.manifest", "// the shop\n"),
            ("main.zed", "import orders.{place};\nmain(m: MainArgs) {}\n"),
            (
                "orders.zed",
                "import stock.{reserve};\nplace(n) = reserve(n);\n",
            ),
            (
                "stock.zed",
                "\nimport orders.{place};\nreserve(n) = n;\nrestock(n) = place(n);\n",
            ),
        ],
    );
    let cycle_lines = |lines: Vec<String>| -> Vec<String> {
        lines
            .into_iter()
            .filter(|l| l.contains("the imports form a cycle"))
            .collect()
    };
    let batch = zedc::unit::load(
        &mut zedc::query::Db::new(),
        &zedc::unit::Dir(d.clone()),
        &["stock", "main", "orders"],
    );
    let batch = cycle_lines(batch.report(&d));
    let root = d.display();
    assert_eq!(
        batch,
        [format!(
            "{root}/orders.zed:1:1: the unit `stock` cannot be imported: the imports form a cycle, \
             so its units have no order to be resolved in: `orders` imports `stock` at \
             orders.zed:1:1, `stock` imports `orders` at stock.zed:2:1."
        )]
    );
    for unit in ["main.zed", "orders.zed", "stock.zed"] {
        let (status, err) = run(d.join(unit).to_str().unwrap());
        assert_eq!(status, 1, "{unit}: {err}");
        let alone = cycle_lines(err.lines().map(str::to_string).collect());
        assert_eq!(alone, batch, "`zedc run {unit}`: {err}");
    }
}
