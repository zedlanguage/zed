//! `zedc run --suppress`, run as a user runs it, from a directory of the user's (items
//! DIAG-suppress, DIAG-suppress-rest and DIAG-addr-root, DESIGN.md sec:diagnostics): a warning's
//! address names its file by its path from its package root or, with no manifest above it, by
//! its absolute path, never by the directory zedc runs in, so every directory zedc runs in
//! prints the same address; a package copied elsewhere prints the same addresses, and an
//! address printed in one copy suppresses the warning in the other; two files of one text have
//! two addresses. `crates/zed-native/Cargo.toml` names this test, since only a test of that
//! package can name the executable and set the directory it runs in.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// A program whose one warning is at `area`, 4:10.
const AREA: &str = "half(positional x) = x div 2 test { 10 -> 5, 7 -> 3 }\n\
                    main(stdin: Lines) -> (stdout: Lines) {\n  side = 3037000500;\n  \
                    area = side * side;\n  stdout <- String(0);\n}\n";

/// The directory `name` of this test under the test target's scratch directory, holding
/// `src/area.zed` and, when `package`, a manifest; its files are overwritten by each run, never
/// deleted, so a name is used for a package or for loose files, never for both.
fn tree(name: &str, package: bool) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("suppress_binary")
        .join(name);
    std::fs::create_dir_all(d.join("src")).unwrap();
    std::fs::write(d.join("src").join("area.zed"), AREA).unwrap();
    if package {
        std::fs::write(d.join("zed.manifest"), "").unwrap();
    }
    d
}

/// `zedc run <words>` with no input, run in the directory `dir`: status, stdout and stderr.
fn zedc_in(dir: &Path, words: &[&str]) -> (Option<i32>, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg("run")
        .args(words)
        .current_dir(dir)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    (
        out.status.code(),
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
    )
}

/// The one address printed in `err`.
fn address(err: &str) -> String {
    let all: Vec<&str> = err
        .lines()
        .filter_map(|l| l.strip_prefix("  address: "))
        .collect();
    assert_eq!(all.len(), 1, "{err}");
    all[0].to_string()
}

#[test]
fn a_copied_package_run_from_the_same_place_prints_the_same_address() {
    let (one, two) = (tree("package_one", true), tree("package_two", true));
    let (status, out, err) = zedc_in(&one, &["src/area.zed"]);
    assert_eq!((status, out.as_str()), (Some(0), "0\n"), "{err}");
    assert!(err.starts_with("src/area.zed:4:10: `area` widens"), "{err}");
    let a = address(&err);
    assert_eq!(address(&zedc_in(&two, &["src/area.zed"]).2), a);
    // The address printed in one copy suppresses the warning in the other.
    assert_eq!(
        zedc_in(&two, &["src/area.zed", "--suppress", &a]),
        (Some(0), "0\n".into(), String::new())
    );
    // Another path to the same file from the same directory gives the same address.
    assert_eq!(
        address(&zedc_in(&one, &["../package_one/./src/area.zed"]).2),
        a
    );
}

/// The address `zedc run` prints for the file `file` of the tree `d`, run from the tree, from
/// its `src` directory, from the directory above it and from the file system's root, each
/// naming the file by its path from there; each run's address suppresses the warning in each
/// other run.
fn the_same_from_four_directories(d: &Path) -> String {
    let full = d.join("src").join("area.zed");
    let full = full.to_str().unwrap();
    let name = d.file_name().unwrap().to_str().unwrap();
    let up = format!("{name}/src/area.zed");
    let runs: [(&Path, &str); 4] = [
        (d, "src/area.zed"),
        (&d.join("src"), "area.zed"),
        (d.parent().unwrap(), &up),
        (Path::new("/"), full),
    ];
    let all: Vec<String> = runs
        .iter()
        .map(|(dir, file)| address(&zedc_in(dir, &[file]).2))
        .collect();
    assert!(all.iter().all(|a| *a == all[0]), "{all:?}");
    for (dir, file) in runs {
        assert_eq!(
            zedc_in(dir, &[file, "--suppress", &all[0]]),
            (Some(0), "0\n".into(), String::new()),
            "{file} from {}",
            dir.display()
        );
    }
    all[0].clone()
}

#[test]
fn the_address_does_not_depend_on_the_directory_zedc_runs_in() {
    // A unit of a package is named by its path from the package root, and a file with no
    // manifest above it by its absolute path: neither is the directory zedc runs in.
    let unit = the_same_from_four_directories(&tree("package_dirs", true));
    let loose = the_same_from_four_directories(&tree("loose_dirs", false));
    // The same text and the same name under the root give two addresses for the two kinds.
    assert_ne!(unit, loose);
}

#[test]
fn two_files_of_one_text_have_two_addresses() {
    // Loose files: two directories holding `src/area.zed`, and a second name in one of them.
    let (left, right) = (tree("loose_left", false), tree("loose_right", false));
    std::fs::write(left.join("src").join("copy.zed"), AREA).unwrap();
    // A package: two names, in the root and in a directory under it.
    let package = tree("package_names", true);
    std::fs::write(package.join("area.zed"), AREA).unwrap();
    let runs: [(&Path, &str); 5] = [
        (&left, "src/area.zed"),
        (&right, "src/area.zed"),
        (&left, "src/copy.zed"),
        (&package, "src/area.zed"),
        (&package, "area.zed"),
    ];
    let all: Vec<String> = runs
        .iter()
        .map(|(dir, file)| address(&zedc_in(dir, &[file]).2))
        .collect();
    let distinct: std::collections::HashSet<&String> = all.iter().collect();
    assert_eq!(distinct.len(), runs.len(), "{all:?}");
}
